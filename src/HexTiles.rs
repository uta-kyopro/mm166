#![allow(non_snake_case)]

use std::cmp::Reverse;
use std::collections::{HashMap, VecDeque};
use std::io::{self, Write};
use std::str::FromStr;
use std::time::{Duration, Instant};

// Search parameters are kept here so experiments use one visible configuration.
const TIME_LIMIT_MS: u64 = 9_200;
const NORMAL_BEAM: usize = 72;
const NORMAL_BONUS_PENALTY: i64 = 300; // reserve bonus transitions for long paths
const SPECIAL_BEAM: usize = 192;
const SPECIAL_CANDIDATES: usize = 24;
const WIDTHS: [usize; 3] = [1, 2, 3];
const MAX_SPECIAL: usize = 3;
const LAYERED_SPECIAL_TRIALS: usize = 2;
const OUTER_LAYERS: usize = 3;
const CONSTRUCTION_LIMIT_MS: u64 = 4_500;
const LOCAL_EXTEND_INTERVAL_MS: u64 = 60;
const LOCAL_EXTEND_BUDGET_MS: u64 = 7;
const LOCAL_PATTERN_LIMIT_4: usize = 480;
const RESTORE_REPAIR_INTERVAL_MS: u64 = 120;
const RESTORE_REPAIR_BUDGET_MS: u64 = 5;
const CONNECT_REPAIR_INTERVAL_MS: u64 = 450;
const CONNECT_REPAIR_BUDGET_MS: u64 = 25;
const CONNECT_REPAIR_BEAM: usize = 48;
const CONNECT_REPAIR_TARGETS: usize = 10;
const ENABLE_CONNECT_REPAIR: bool = true; // paired evaluation switch
const SA_START_TEMP: f64 = 240.0;
const SA_END_TEMP: f64 = 0.01;
const POSTPROCESS_LIMIT_MS: u64 = 450;
const ENABLE_TRANSITION_TABLE: bool = true; // paired evaluation switch
const MIN_LONG_PAIRS_FOR_VIRTUALIZATION: usize = 5;
const LONG_PAIR_DISTANCE_NUM: usize = 1;
const LONG_PAIR_DISTANCE_DEN: usize = 1;
const VIRTUAL_PAIRING_BEAM: usize = 192;
const VIRTUAL_GROUP_CANDIDATES: usize = 48;
const VIRTUAL_GAIN_COEFF_NUM: usize = 1;
const VIRTUAL_GAIN_COEFF_DEN: usize = 1;

struct Scanner {
    input: io::Stdin,
    tokens: VecDeque<String>,
}

impl Scanner {
    fn new() -> Self { Self { input: io::stdin(), tokens: VecDeque::new() } }
    fn next<T: FromStr>(&mut self) -> T {
        loop {
            if let Some(s) = self.tokens.pop_front() {
                return s.parse().ok().expect("invalid input token");
            }
            let mut line = String::new();
            assert!(self.input.read_line(&mut line).unwrap() > 0, "unexpected EOF");
            self.tokens.extend(line.split_whitespace().map(str::to_owned));
        }
    }
}

// Directions, clockwise: NW, NE, E, SE, SW, W.
const DR: [isize; 6] = [-1, -1, 0, 1, 1, 0];
const DC: [isize; 6] = [0, 1, 1, 0, -1, -1];

#[derive(Clone, Copy, Default)]
struct Stats {
    matched: usize,
    total: i64,
    moves: i32,
    score: i64,
}

#[derive(Clone)]
struct Route {
    tiles: Vec<(usize, u8)>,
    length: usize,
    bonuses: usize,
}

#[derive(Clone)]
struct Node {
    cell: usize,
    enter: usize,
    placed_cell: usize,
    parent: usize,
    orientation: u8,
    length: usize,
    bonuses: usize,
    rotations: i32,
    depth_sum: usize,
    damaged: u128,
    seen: Vec<u64>,
}

struct DamageModel {
    cell_masks: Vec<u128>,
    contributions: Vec<i64>,
    base: Stats,
}

struct EvalScratch {
    bonus_stamp: Vec<u32>,
    epoch: u32,
}

struct DifferentialEval {
    contribution: Vec<i64>,
    cell_masks: Vec<u128>,
    pair_cells: Vec<Vec<usize>>,
}

impl EvalScratch {
    fn new(cells: usize) -> Self { Self { bonus_stamp: vec![0; cells], epoch: 0 } }
    fn next_epoch(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.bonus_stamp.fill(0);
            self.epoch = 1;
        }
        self.epoch
    }
}

#[derive(Clone)]
struct Board {
    W: usize,
    M: i32,
    initial: Vec<u8>,
    valid: Vec<bool>,
    bonus: Vec<bool>,
    exits: Vec<(usize, usize)>,
    exit_id: Vec<i32>,
    pairs: Vec<[usize; 2]>,
    transition: Vec<usize>,
    boundary_depth: Vec<usize>,
    valid_count: usize,
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 7;
        self.0 ^= self.0 >> 9;
        self.0
    }
    fn usize(&mut self, n: usize) -> usize { self.next() as usize % n }
    fn unit(&mut self) -> f64 { (self.next() >> 11) as f64 / ((1u64 << 53) as f64) }
}

fn paired_dir(o: u8, enter: usize) -> usize {
    const BASE: [usize; 6] = [1, 0, 4, 5, 2, 3];
    let x = (enter + 6 - o as usize) % 6;
    (BASE[x] + o as usize) % 6
}

fn rotation_cost(from: u8, to: u8) -> i32 {
    let d = (to as i32 - from as i32 + 6) % 6;
    d.min(6 - d)
}

impl Board {
    fn inside(&self, r: isize, c: isize) -> bool {
        r >= 0 && c >= 0 && r < self.W as isize && c < self.W as isize
            && self.valid[r as usize * self.W + c as usize]
    }

    fn next(&self, cell: usize, side: usize) -> Option<(usize, usize)> {
        let r = cell / self.W;
        let c = cell % self.W;
        let nr = r as isize + DR[side];
        let nc = c as isize + DC[side];
        if self.inside(nr, nc) {
            Some((nr as usize * self.W + nc as usize, (side + 3) % 6))
        } else {
            None
        }
    }

    fn trace(&self, orientation: &[u8], start: usize) -> (usize, usize, usize) {
        let (mut cell, mut enter) = self.exits[start];
        let mut length = 0usize;
        let mut bonuses = 0usize;
        let mut bonus_seen = vec![false; self.valid.len()];
        // A port belongs to exactly one path. More than 3*tiles steps means a bug/cycle.
        for _ in 0..=3 * self.valid_count {
            length += 1;
            if self.bonus[cell] && !bonus_seen[cell] {
                bonuses += 1;
                bonus_seen[cell] = true;
            }
            let out = paired_dir(orientation[cell], enter);
            if let Some((nc, ne)) = self.next(cell, out) {
                cell = nc;
                enter = ne;
            } else {
                let id = self.exit_id[cell * 6 + out];
                return (id as usize, length, bonuses);
            }
        }
        (usize::MAX, length, bonuses)
    }

    fn trace_exit_cells(&self, orientation: &[u8], start: usize, cells: &mut Vec<usize>) {
        cells.clear();
        let (mut cell, mut enter) = self.exits[start];
        for _ in 0..=3 * self.valid_count {
            cells.push(cell);
            let out = paired_dir(orientation[cell], enter);
            let Some((next, next_enter)) = self.next(cell, out) else { break; };
            cell = next;
            enter = next_enter;
        }
    }

    fn evaluate(&self, orientation: &[u8]) -> Stats {
        let mut scratch = EvalScratch::new(self.valid.len());
        self.evaluate_with_scratch(orientation, &mut scratch)
    }

    fn evaluate_with_scratch(&self, orientation: &[u8], scratch: &mut EvalScratch) -> Stats {
        let mut moves = 0;
        for cell in 0..orientation.len() {
            if self.valid[cell] {
                moves += rotation_cost(self.initial[cell], orientation[cell]);
            }
        }
        self.evaluate_with_moves(orientation, moves, scratch)
    }

    fn evaluate_with_moves(
        &self, orientation: &[u8], moves: i32, scratch: &mut EvalScratch,
    ) -> Stats {
        let mut s = Stats { moves, ..Stats::default() };
        let terminal_base = self.valid.len() * 6;
        for pair in &self.pairs {
            let epoch = scratch.next_epoch();
            let (cell, enter) = self.exits[pair[0]];
            let mut state = cell * 6 + enter;
            let mut len = 0usize;
            let mut bonuses = 0usize;
            let mut end = usize::MAX;
            for _ in 0..=3 * self.valid_count {
                len += 1;
                let cell = state / 6;
                if self.bonus[cell] && scratch.bonus_stamp[cell] != epoch {
                    scratch.bonus_stamp[cell] = epoch;
                    bonuses += 1;
                }
                let next = self.transition[state * 6 + orientation[cell] as usize];
                if next >= terminal_base {
                    end = next - terminal_base;
                    break;
                }
                state = next;
            }
            if end == pair[1] {
                s.matched += 1;
                s.total += (len * (bonuses + 1)) as i64;
            }
        }
        s.score = (s.matched as i64 * (s.total - self.M as i64 * s.moves as i64)).max(0);
        s
    }

    fn trace_pair(
        &self, orientation: &[u8], id: usize, scratch: &mut EvalScratch,
        mut cells: Option<&mut Vec<usize>>,
    ) -> (i64, i64) {
        let epoch = scratch.next_epoch();
        let pair = self.pairs[id];
        let (cell, enter) = self.exits[pair[0]];
        let mut state = cell * 6 + enter;
        let terminal_base = self.valid.len() * 6;
        let mut len = 0usize;
        let mut bonuses = 0usize;
        for _ in 0..=3 * self.valid_count {
            len += 1;
            let cell = state / 6;
            if let Some(path) = cells.as_deref_mut() { path.push(cell); }
            if self.bonus[cell] && scratch.bonus_stamp[cell] != epoch {
                scratch.bonus_stamp[cell] = epoch;
                bonuses += 1;
            }
            let next = self.transition[state * 6 + orientation[cell] as usize];
            if next >= terminal_base {
                return if next - terminal_base == pair[1] {
                    ((len * (bonuses + 1)) as i64, len as i64)
                } else { (0, 0) };
            }
            state = next;
        }
        (0, 0)
    }

    fn damage_model(&self, orientation: &[u8]) -> DamageModel {
        let mut cell_masks = vec![0u128; self.valid.len()];
        let mut contributions = vec![0i64; self.pairs.len()];
        for (id, pair) in self.pairs.iter().enumerate() {
            let (end, len, bonuses) = self.trace(orientation, pair[0]);
            if end != pair[1] { continue; }
            contributions[id] = (len * (bonuses + 1)) as i64;
            let (mut cell, mut enter) = self.exits[pair[0]];
            for _ in 0..=3 * self.valid_count {
                cell_masks[cell] |= 1u128 << id;
                let out = paired_dir(orientation[cell], enter);
                let Some((next, next_enter)) = self.next(cell, out) else { break; };
                cell = next;
                enter = next_enter;
            }
        }
        DamageModel { cell_masks, contributions, base: self.evaluate(orientation) }
    }

    fn tester_safe(&self, orientation: &[u8]) -> bool {
        let ports = self.valid.len() * 6;
        let mut globally_seen = vec![false; ports];
        for start in 0..ports {
            if !self.valid[start / 6] || globally_seen[start] { continue; }
            let mut local = std::collections::HashMap::new();
            let mut state = start;
            let mut step = 0usize;
            loop {
                if globally_seen[state] { break; }
                if let Some(&began) = local.get(&state) {
                    if step - began > 400 { return false; }
                    break;
                }
                local.insert(state, step);
                step += 1;
                let cell = state / 6;
                let enter = state % 6;
                let out = paired_dir(orientation[cell], enter);
                let Some((next, next_enter)) = self.next(cell, out) else { break; };
                state = next * 6 + next_enter;
            }
            for state in local.keys() { globally_seen[*state] = true; }
        }
        true
    }
}

impl DifferentialEval {
    fn new(board: &Board, orientation: &[u8], scratch: &mut EvalScratch) -> Self {
        assert!(board.pairs.len() <= 128);
        let mut cell_masks = vec![0u128; board.valid.len()];
        let mut pair_cells = vec![Vec::new(); board.pairs.len()];
        let mut contribution = vec![0i64; board.pairs.len()];
        for id in 0..board.pairs.len() {
            (contribution[id], _) = board.trace_pair(
                orientation, id, scratch, Some(&mut pair_cells[id]));
            for &cell in &pair_cells[id] { cell_masks[cell] |= 1u128 << id; }
        }
        Self { contribution, cell_masks, pair_cells }
    }

    fn proposal(
        &self, board: &Board, orientation: &[u8], current: Stats, moves: i32,
        affected: u128, scratch: &mut EvalScratch,
        updates: &mut Vec<(usize, i64)>,
    ) -> Stats {
        let mut next = Stats { moves, matched: current.matched, total: current.total, score: 0 };
        updates.clear();
        for id in 0..board.pairs.len() {
            if affected >> id & 1 == 0 { continue; }
            let old = self.contribution[id];
            let (new, _) = board.trace_pair(orientation, id, scratch, None);
            if old > 0 { next.matched -= 1; next.total -= old; }
            if new > 0 { next.matched += 1; next.total += new; }
            updates.push((id, new));
        }
        next.score = (next.matched as i64
            * (next.total - board.M as i64 * moves as i64)).max(0);
        next
    }

    fn commit(
        &mut self, board: &Board, orientation: &[u8], scratch: &mut EvalScratch,
        updates: &[(usize, i64)], route_cells: &mut Vec<usize>,
    ) {
        for &(id, value) in updates {
            let bit = 1u128 << id;
            for &cell in &self.pair_cells[id] { self.cell_masks[cell] &= !bit; }
            route_cells.clear();
            board.trace_pair(orientation, id, scratch, Some(route_cells));
            self.pair_cells[id].clear();
            self.pair_cells[id].extend_from_slice(route_cells);
            for &cell in &self.pair_cells[id] { self.cell_masks[cell] |= bit; }
            self.contribution[id] = value;
        }
    }

}

fn bit_test(bits: &[u64], cell: usize) -> bool {
    bits[cell >> 6] >> (cell & 63) & 1 != 0
}

fn bit_set(bits: &mut [u64], cell: usize) {
    bits[cell >> 6] |= 1u64 << (cell & 63);
}

fn orientation_choices(board: &Board, fixed: &[i8], base: &[u8], cell: usize, enter: usize)
    -> Vec<(usize, u8, i32)>
{
    let mut best = [None::<(u8, i32)>; 6];
    let first = if fixed[cell] >= 0 { fixed[cell] as u8 } else { 0 };
    let last = if fixed[cell] >= 0 { fixed[cell] as u8 } else { 5 };
    for o in first..=last {
        let out = paired_dir(o, enter);
        let cost = rotation_cost(board.initial[cell], o)
            + if o == base[cell] { 0 } else { 1 };
        if best[out].map_or(true, |x| cost < x.1) {
            best[out] = Some((o, cost));
        }
    }
    IntoIterator::into_iter(best).enumerate().filter_map(|(out, x)| x.map(|(o, c)| (out, o, c))).collect()
}

fn damage_loss(model: &DamageModel, mut mask: u128) -> (usize, i64) {
    let mut count = 0usize;
    let mut total = 0i64;
    while mask != 0 {
        let id = mask.trailing_zeros() as usize;
        mask &= mask - 1;
        count += 1;
        total += model.contributions[id];
    }
    (count, total)
}

fn route_rank(
    board: &Board, node: &Node, target_cell: usize, width: usize, special: bool,
    damage: Option<&DamageModel>,
) -> i64 {
    let r = node.cell / board.W;
    let c = node.cell % board.W;
    let tr = target_cell / board.W;
    let tc = target_cell % board.W;
    let heuristic = (r.abs_diff(tr) + c.abs_diff(tc)) as i64;
    if special {
        // Length and bonuses reinforce one another. A small target heuristic keeps
        // the beam capable of closing after taking a profitable detour.  Once the
        // perimeter has been secured, depth is useful: it steers the reserved pair
        // through a gate into otherwise unused interior tiles.
        let intrinsic = (node.length * (node.bonuses + 1)) as i64;
        let predicted_gain = if let Some(model) = damage {
            let (lost_k, lost_t) = damage_loss(model, node.damaged);
            let old_q = model.base.total - board.M as i64 * model.base.moves as i64;
            let new_k = model.base.matched.saturating_sub(lost_k) + 1;
            let delta_k = new_k as i64 - model.base.matched as i64;
            let delta_q = intrinsic - lost_t - board.M as i64 * node.rotations as i64;
            delta_k * old_q + new_k as i64 * delta_q
        } else { 0 };
        (if damage.is_some() { 40 * predicted_gain + 80 * intrinsic } else { 180 * intrinsic })
            - 12 * board.M as i64 * node.rotations as i64
            - 5 * heuristic
            - node.depth_sum as i64
    } else {
        let overflow = board.boundary_depth[node.cell].saturating_sub(width);
        -(24 * node.length as i64
            + 10 * board.M as i64 * node.rotations as i64
            + 30 * node.depth_sum as i64
            + NORMAL_BONUS_PENALTY * node.bonuses as i64
            + 220 * (overflow * overflow) as i64
            + 14 * heuristic)
    }
}

fn reconstruct(arena: &[Node], mut id: usize) -> Route {
    let last = &arena[id];
    let mut tiles = Vec::with_capacity(last.length);
    loop {
        let n = &arena[id];
        if n.parent == usize::MAX { break; }
        tiles.push((n.placed_cell, n.orientation));
        id = n.parent;
    }
    tiles.reverse();
    Route { tiles, length: last.length, bonuses: last.bonuses }
}

fn assigned_orientation(arena: &[Node], mut id: usize, cell: usize) -> Option<u8> {
    loop {
        let node = &arena[id];
        if node.placed_cell == cell { return Some(node.orientation); }
        if node.parent == usize::MAX { return None; }
        id = node.parent;
    }
}

fn find_route(
    board: &Board,
    base: &[u8],
    fixed: &[i8],
    source: usize,
    target: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
    depth_limit: Option<usize>,
    deadline: Instant,
) -> Option<Route> {
    if Instant::now() >= deadline { return None; }
    let (start_cell, start_side) = board.exits[source];
    let target_cell = board.exits[target].0;
    let n = (board.W + 1) / 2;
    let port_revisit = special && n <= 13;
    let words = (board.valid.len() * if port_revisit { 6 } else { 1 } + 63) / 64;
    let root = Node {
        cell: start_cell, enter: start_side, placed_cell: usize::MAX,
        parent: usize::MAX, orientation: 255,
        length: 0, bonuses: 0, rotations: 0, depth_sum: 0, seen: vec![0; words],
        damaged: 0,
    };
    let mut arena = vec![root];
    let mut beam = vec![0usize];
    let mut goals: Vec<(i64, usize)> = Vec::new();
    let beam_width = if special { SPECIAL_BEAM } else { NORMAL_BEAM };
    let max_len = if port_revisit {
        (3 * board.valid_count).min(10 * board.W + 160)
    } else if special {
        board.valid_count.min(6 * board.W + 80)
    } else { 5 * board.W + 20 };

    for _ in 0..max_len {
        if beam.is_empty() || Instant::now() >= deadline { break; }
        let mut next_beam = Vec::with_capacity(beam_width * 3);
        for &id in &beam {
            let p = arena[id].clone();
            if depth_limit.is_some_and(|limit| board.boundary_depth[p.cell] > limit) { continue; }
            let enter_key = if port_revisit { p.cell * 6 + p.enter } else { p.cell };
            if bit_test(&p.seen, enter_key) { continue; }
            let previous_o = port_revisit.then(|| assigned_orientation(&arena, id, p.cell)).flatten();
            let choices = if let Some(o) = previous_o {
                vec![(paired_dir(o, p.enter), o, 0)]
            } else {
                orientation_choices(board, fixed, base, p.cell, p.enter)
            };
            for (out, o, _step_rot) in choices {
                let mut seen = p.seen.clone();
                bit_set(&mut seen, enter_key);
                if port_revisit { bit_set(&mut seen, p.cell * 6 + out); }
                let node = Node {
                    cell: p.cell,
                    enter: p.enter,
                    placed_cell: p.cell,
                    parent: id,
                    orientation: o,
                    length: p.length + 1,
                    bonuses: p.bonuses
                        + usize::from(previous_o.is_none() && board.bonus[p.cell]),
                    rotations: p.rotations + if previous_o.is_none() {
                        rotation_cost(board.initial[p.cell], o)
                    } else { 0 },
                    depth_sum: p.depth_sum + board.boundary_depth[p.cell],
                    damaged: p.damaged | if o != base[p.cell] {
                        damage.map_or(0, |m| m.cell_masks[p.cell])
                    } else { 0 },
                    seen,
                };
                if let Some((nc, ne)) = board.next(p.cell, out) {
                    if depth_limit.is_some_and(|limit| board.boundary_depth[nc] > limit) { continue; }
                    let next_key = if port_revisit { nc * 6 + ne } else { nc };
                    if bit_test(&node.seen, next_key) { continue; }
                    let mut child = node;
                    child.cell = nc;
                    child.enter = ne;
                    let nid = arena.len();
                    arena.push(child);
                    next_beam.push(nid);
                } else {
                    let exit = board.exit_id[p.cell * 6 + out] as usize;
                    if exit == target {
                        let nid = arena.len();
                        arena.push(node);
                        let value = if special {
                            let n = &arena[nid];
                            (n.length * (n.bonuses + 1)) as i64
                                - board.M as i64 * n.rotations as i64
                        } else {
                            -((arena[nid].length + arena[nid].depth_sum) as i64)
                                - board.M as i64 * arena[nid].rotations as i64
                        };
                        goals.push((value, nid));
                    }
                }
            }
        }
        next_beam.sort_unstable_by_key(|&id| Reverse(route_rank(
            board, &arena[id], target_cell, width, special, damage,
        )));
        next_beam.truncate(beam_width);
        beam = next_beam;
        if !special && !goals.is_empty() { break; }
    }
    goals.into_iter().max_by_key(|x| x.0).map(|(_, id)| reconstruct(&arena, id))
}

fn apply_route(orientation: &mut [u8], fixed: &mut [i8], route: &Route, protect: bool) {
    for &(cell, o) in &route.tiles {
        orientation[cell] = o;
        if protect { fixed[cell] = o as i8; }
    }
}

fn pair_priority(board: &Board, pair: [usize; 2]) -> usize {
    let a = board.exits[pair[0]].0;
    let b = board.exits[pair[1]].0;
    let ar = a / board.W;
    let ac = a % board.W;
    let br = b / board.W;
    let bc = b % board.W;
    ar.abs_diff(br) + ac.abs_diff(bc)
}

fn build_outer(
    board: &Board,
    width: usize,
    reserved: &[usize],
    deadline: Instant,
) -> (Vec<u8>, Vec<i8>) {
    let mut orientation = board.initial.clone();
    let mut fixed = vec![-1i8; orientation.len()];
    let mut best = orientation.clone();
    let mut best_fixed = fixed.clone();
    let mut best_stats = board.evaluate(&best);
    let mut order: Vec<usize> = (0..board.pairs.len())
        .filter(|i| !reserved.contains(i))
        .collect();
    order.sort_unstable_by_key(|&i| pair_priority(board, board.pairs[i]));
    for i in order {
        if Instant::now() >= deadline { break; }
        let pair = board.pairs[i];
        if let Some(route) = find_route(
            board, &orientation, &fixed, pair[0], pair[1], width, false, None, None, deadline,
        ) {
            apply_route(&mut orientation, &mut fixed, &route, true);
            let stats = board.evaluate(&orientation);
            if (stats.score, stats.matched, stats.total - board.M as i64 * stats.moves as i64)
                > (best_stats.score, best_stats.matched, best_stats.total - board.M as i64 * best_stats.moves as i64)
            {
                best_stats = stats;
                best = orientation.clone();
                best_fixed = fixed.clone();
            }
        }
    }
    (best, best_fixed)
}

fn special_order(board: &Board) -> Vec<usize> {
    let mut ids: Vec<usize> = (0..board.pairs.len()).collect();
    ids.sort_unstable_by_key(|&i| Reverse(pair_priority(board, board.pairs[i])));
    ids.truncate(SPECIAL_CANDIDATES.min(ids.len()));
    ids
}

fn optimistic_reachable_pairs(board: &Board, fixed: &[i8]) -> Vec<bool> {
    let ports = board.valid.len() * 6;
    let total = ports + board.exits.len();
    let mut parent: Vec<usize> = (0..total).collect();
    fn root(parent: &mut [usize], mut x: usize) -> usize {
        while parent[x] != x {
            parent[x] = parent[parent[x]];
            x = parent[x];
        }
        x
    }
    fn join(parent: &mut [usize], a: usize, b: usize) {
        let a = root(parent, a);
        let b = root(parent, b);
        if a != b { parent[b] = a; }
    }
    for cell in 0..board.valid.len() {
        if !board.valid[cell] { continue; }
        let first = if fixed[cell] >= 0 { fixed[cell] as u8 } else { 0 };
        let last = if fixed[cell] >= 0 { fixed[cell] as u8 } else { 5 };
        for o in first..=last {
            for enter in 0..6 {
                join(&mut parent, cell * 6 + enter, cell * 6 + paired_dir(o, enter));
            }
        }
        for side in 0..6 {
            if let Some((next, next_side)) = board.next(cell, side) {
                join(&mut parent, cell * 6 + side, next * 6 + next_side);
            } else {
                let exit = board.exit_id[cell * 6 + side];
                if exit >= 0 { join(&mut parent, cell * 6 + side, ports + exit as usize); }
            }
        }
    }
    board.pairs.iter().map(|pair| {
        root(&mut parent, ports + pair[0]) == root(&mut parent, ports + pair[1])
    }).collect()
}

fn build_layered_one_special(
    board: &Board,
    reserved: usize,
    outer_deadline: Instant,
    special_deadline: Instant,
) -> (Vec<u8>, [usize; OUTER_LAYERS], usize, i64) {
    let mut orientation = board.initial.clone();
    let mut fixed = vec![-1i8; orientation.len()];
    let mut connected = vec![false; board.pairs.len()];
    let mut layer_counts = [0usize; OUTER_LAYERS];
    let mut order: Vec<usize> = (0..board.pairs.len()).filter(|&id| id != reserved).collect();
    order.sort_unstable_by_key(|&id| pair_priority(board, board.pairs[id]));

    for layer in 0..OUTER_LAYERS {
        for &id in &order {
            if connected[id] || Instant::now() >= outer_deadline { continue; }
            let pair = board.pairs[id];
            let Some(route) = find_route(
                board, &orientation, &fixed, pair[0], pair[1], layer + 1,
                false, None, Some(layer), outer_deadline,
            ) else { continue; };

            let before = optimistic_reachable_pairs(board, &fixed);
            let mut trial_orientation = orientation.clone();
            let mut trial_fixed = fixed.clone();
            apply_route(&mut trial_orientation, &mut trial_fixed, &route, true);
            let after = optimistic_reachable_pairs(board, &trial_fixed);
            let keeps_future_open = (0..board.pairs.len()).all(|other| {
                connected[other] || other == id || !before[other] || after[other]
            });
            if keeps_future_open {
                orientation = trial_orientation;
                fixed = trial_fixed;
                connected[id] = true;
                layer_counts[layer] += 1;
            }
        }
    }

    let pair = board.pairs[reserved];
    let use_damage_dp = (board.W + 1) / 2 >= 16 && board.M <= 2;
    let damage = use_damage_dp.then(|| board.damage_model(&orientation));
    let mut special_value = 0i64;
    let mut special_done = 0usize;
    if let Some(route) = find_route(
        board, &orientation, &fixed, pair[0], pair[1], OUTER_LAYERS,
        true, damage.as_ref(), None, special_deadline,
    ) {
        special_value = (route.length * (route.bonuses + 1)) as i64;
        special_done = 1;
        apply_route(&mut orientation, &mut fixed, &route, true);
    }
    (orientation, layer_counts, special_done, special_value)
}

fn open_reserved_gates(board: &Board, fixed: &mut [i8], chosen: &[usize], width: usize) {
    let mut dist = vec![usize::MAX; board.valid.len()];
    let mut q = VecDeque::new();
    for &id in chosen {
        for &exit in &board.pairs[id] {
            let cell = board.exits[exit].0;
            if dist[cell] != 0 {
                dist[cell] = 0;
                q.push_back(cell);
            }
        }
    }
    // A small open patch around each reserved endpoint is the gate.  Normal paths
    // outside it remain protected; paths crossing the patch may be repaired later.
    let radius = width + 1;
    while let Some(cell) = q.pop_front() {
        fixed[cell] = -1;
        if dist[cell] == radius { continue; }
        for d in 0..6 {
            if let Some((next, _)) = board.next(cell, d) {
                if dist[next] == usize::MAX {
                    dist[next] = dist[cell] + 1;
                    q.push_back(next);
                }
            }
        }
    }
}

fn build_with_specials(
    board: &Board,
    outer: &[u8],
    outer_fixed: &[i8],
    width: usize,
    chosen: &[usize],
    deadline: Instant,
) -> (Vec<u8>, i64, usize) {
    let mut orientation = outer.to_vec();
    let mut fixed = outer_fixed.to_vec();
    for cell in 0..fixed.len() {
        if board.valid[cell] && board.boundary_depth[cell] > width {
            fixed[cell] = -1;
        }
    }
    open_reserved_gates(board, &mut fixed, chosen, width);
    let mut special_value = 0i64;
    let mut special_done = 0usize;
    for &id in chosen {
        if Instant::now() >= deadline { break; }
        let p = board.pairs[id];
        let use_damage_dp = (board.W + 1) / 2 >= 16 && board.M <= 2;
        let damage = use_damage_dp.then(|| board.damage_model(&orientation));
        if let Some(route) = find_route(
            board, &orientation, &fixed, p[0], p[1], width, true,
            damage.as_ref(), None, deadline,
        ) {
            special_value += (route.length * (route.bonuses + 1)) as i64;
            special_done += 1;
            apply_route(&mut orientation, &mut fixed, &route, true);
        }
    }
    let mut best_orientation = orientation.clone();
    let mut best_stats = board.evaluate(&orientation);

    // Rebuild the many ordinary connections around the protected special paths.
    let mut order: Vec<usize> = (0..board.pairs.len()).filter(|i| !chosen.contains(i)).collect();
    order.sort_unstable_by_key(|&i| pair_priority(board, board.pairs[i]));
    for id in order {
        if Instant::now() >= deadline { break; }
        let p = board.pairs[id];
        if let Some(route) = find_route(
            board, &orientation, &fixed, p[0], p[1], width, false, None, None, deadline,
        ) {
            apply_route(&mut orientation, &mut fixed, &route, true);
            let stats = board.evaluate(&orientation);
            let q = stats.total - board.M as i64 * stats.moves as i64;
            let best_q = best_stats.total - board.M as i64 * best_stats.moves as i64;
            if (stats.score, q, stats.matched, stats.total, Reverse(stats.moves))
                > (best_stats.score, best_q, best_stats.matched, best_stats.total, Reverse(best_stats.moves))
            {
                best_stats = stats;
                best_orientation = orientation.clone();
            }
        }
    }
    (best_orientation, special_value, special_done)
}

fn polish(board: &Board, orientation: &mut Vec<u8>, deadline: Instant) {
    let mut best = board.evaluate(orientation);
    let mut changed = true;
    while changed && Instant::now() < deadline {
        changed = false;
        for cell in 0..orientation.len() {
            if !board.valid[cell] || Instant::now() >= deadline { break; }
            let old = orientation[cell];
            let mut best_o = old;
            for o in 0..6u8 {
                if o == old { continue; }
                orientation[cell] = o;
                let s = board.evaluate(orientation);
                let q = s.total - board.M as i64 * s.moves as i64;
                let best_q = best.total - board.M as i64 * best.moves as i64;
                if (s.score, q, s.matched, s.total, Reverse(s.moves))
                    > (best.score, best_q, best.matched, best.total, Reverse(best.moves))
                {
                    best = s;
                    best_o = o;
                }
            }
            orientation[cell] = best_o;
            changed |= best_o != old;
        }
    }
}

fn path_states(
    board: &Board,
    orientation: &[u8],
    start: usize,
) -> (usize, usize, usize, Vec<(usize, usize)>) {
    let (mut cell, mut enter) = board.exits[start];
    let mut states = Vec::new();
    let mut seen = vec![false; board.valid.len() * 6];
    let mut bonuses = 0usize;
    let mut bonus_seen = vec![false; board.valid.len()];
    for _ in 0..=3 * board.valid_count {
        let state = cell * 6 + enter;
        if seen[state] { return (usize::MAX, states.len(), bonuses, states); }
        seen[state] = true;
        states.push((cell, enter));
        if board.bonus[cell] && !bonus_seen[cell] {
            bonuses += 1;
            bonus_seen[cell] = true;
        }
        let out = paired_dir(orientation[cell], enter);
        let Some((next, next_enter)) = board.next(cell, out) else {
            return (board.exit_id[cell * 6 + out] as usize, states.len(), bonuses, states);
        };
        cell = next;
        enter = next_enter;
    }
    (usize::MAX, states.len(), bonuses, states)
}

fn local_extend_candidate(
    board: &Board,
    orientation: &[u8],
    rng: &mut Rng,
    deadline: Instant,
) -> Option<Vec<u8>> {
    let mut paths = Vec::new();
    for (id, pair) in board.pairs.iter().enumerate() {
        let (end, length, bonuses, states) = path_states(board, orientation, pair[0]);
        if end == pair[1] && states.len() >= 2 {
            paths.push((length * (bonuses + 1), id, length, states));
        }
    }
    if paths.is_empty() { return None; }
    paths.sort_unstable_by_key(|x| Reverse(x.0));
    let pick = rng.usize(paths.len().min(4));
    let (old_value, id, old_length, states) = &paths[pick];
    let pair = board.pairs[*id];
    let mut on_path = vec![false; board.valid.len()];
    for &(cell, _) in states { on_path[cell] = true; }

    let mut cluster = None;
    let offset = rng.usize(states.len());
    'centers: for step in 0..states.len() {
        let (center, enter) = states[(offset + step) % states.len()];
        let current_out = paired_dir(orientation[center], enter);
        let mut neighbors = Vec::new();
        for side in 0..6 {
            if side == enter || side == current_out { continue; }
            if let Some((next, _)) = board.next(center, side) {
                if !on_path[next] { neighbors.push(next); }
            }
        }
        for i in 0..neighbors.len() {
            for j in i + 1..neighbors.len() {
                let a = neighbors[i];
                let b = neighbors[j];
                let adjacent = (0..6).any(|side| board.next(a, side).is_some_and(|x| x.0 == b));
                if !adjacent { continue; }
                let mut cells = vec![center, a, b];
                if rng.usize(2) == 0 {
                    let mut fourth = None;
                    for &base in &[a, b] {
                        for side in 0..6 {
                            if let Some((next, _)) = board.next(base, side) {
                                if !on_path[next] && !cells.contains(&next) {
                                    fourth = Some(next);
                                    break;
                                }
                            }
                        }
                        if fourth.is_some() { break; }
                    }
                    if let Some(cell) = fourth { cells.push(cell); }
                }
                cluster = Some(cells);
                break 'centers;
            }
        }
    }
    let cells = cluster?;
    let total_patterns = 6usize.pow(cells.len() as u32);
    let checks = if cells.len() == 4 {
        LOCAL_PATTERN_LIMIT_4.min(total_patterns)
    } else { total_patterns };
    let pattern_offset = rng.usize(total_patterns);
    let mut candidates: Vec<(i64, usize, i32, Vec<u8>)> = Vec::new();
    let mut trial = orientation.to_vec();
    for step in 0..checks {
        if Instant::now() >= deadline { break; }
        let mut code = (pattern_offset + step) % total_patterns;
        let mut changed = false;
        for &cell in &cells {
            let o = (code % 6) as u8;
            code /= 6;
            changed |= o != orientation[cell];
            trial[cell] = o;
        }
        if !changed { continue; }
        let (end, length, bonuses) = board.trace(&trial, pair[0]);
        if end == pair[1] && length > *old_length {
            let old_rotations: i32 = cells.iter()
                .map(|&cell| rotation_cost(board.initial[cell], orientation[cell]))
                .sum();
            let rotations: i32 = cells.iter()
                .map(|&cell| rotation_cost(board.initial[cell], trial[cell]))
                .sum();
            let value = length * (bonuses + 1);
            let net_gain = value as i64 - *old_value as i64
                - board.M as i64 * (rotations - old_rotations) as i64;
            candidates.push((net_gain, value, rotations,
                cells.iter().map(|&cell| trial[cell]).collect()));
        }
        for &cell in &cells { trial[cell] = orientation[cell]; }
    }
    candidates.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1), x.2));
    candidates.truncate(8);
    let mut best: Option<(Stats, Vec<u8>)> = None;
    for (_, _, _, values) in candidates {
        let mut candidate = orientation.to_vec();
        for (&cell, &o) in cells.iter().zip(values.iter()) { candidate[cell] = o; }
        let stats = board.evaluate(&candidate);
        if best.as_ref().map_or(true, |x| {
            (stats.score, stats.matched, stats.total, Reverse(stats.moves))
                > (x.0.score, x.0.matched, x.0.total, Reverse(x.0.moves))
        }) {
            best = Some((stats, candidate));
        }
    }
    best.map(|x| x.1)
}

fn restore_repair_candidate(
    board: &Board,
    orientation: &[u8],
    base: Stats,
    differential: &DifferentialEval,
    scratch: &mut EvalScratch,
    rng: &mut Rng,
    deadline: Instant,
) -> Option<Vec<u8>> {
    let connected_mask = differential.contribution.iter().enumerate().fold(0u128, |mask, (id, &x)| {
        if x > 0 { mask | (1u128 << id) } else { mask }
    });
    let cells: Vec<usize> = (0..board.valid.len())
        .filter(|&cell| {
            if !board.valid[cell] { return false; }
            let paths = (differential.cell_masks[cell] & connected_mask).count_ones();
            paths == 1 || paths == 2
        })
        .collect();
    if cells.is_empty() { return None; }
    let max_depth = (3 + board.W / 8).clamp(3, 10);
    let beam_width = 8usize;
    let mut best: Option<(Stats, Vec<u8>)> = None;
    let mut updates = Vec::with_capacity(board.pairs.len());
    let mut route = Vec::with_capacity(3 * board.valid_count);
    let mut candidate_rank = vec![(usize::MAX, u32::MAX); board.valid.len()];

    // A node may temporarily lose connections, but it is never exposed to SA.
    // Grow a set of distinct tile changes until the original connection count is
    // restored, then return the whole set as a single transaction.
    for _ in 0..4 {
        if Instant::now() >= deadline { break; }
        let center = cells[rng.usize(cells.len())];
        let mut beam: Vec<(Stats, Vec<u8>, Vec<usize>, u128, u128)> = Vec::new();
        for oc in 0u8..6 {
            if oc == orientation[center] { continue; }
            let mut candidate = orientation.to_vec();
            candidate[center] = oc;
            let moves = base.moves
                - rotation_cost(board.initial[center], orientation[center])
                + rotation_cost(board.initial[center], oc);
            let affected = differential.cell_masks[center];
            let stats = differential.proposal(
                board, &candidate, base, moves, affected, scratch, &mut updates);
            if stats.matched < base.matched {
                let lost = updates.iter().fold(0u128, |mask, &(id, value)| {
                    if differential.contribution[id] > 0 && value == 0 {
                        mask | (1u128 << id)
                    } else { mask }
                });
                beam.push((stats, candidate, vec![center], affected, lost));
            }
        }
        beam.sort_unstable_by_key(|x| {
            (Reverse(x.0.matched), Reverse(x.0.score), Reverse(x.0.total), x.0.moves)
        });
        beam.truncate(beam_width);

        for _depth in 2..=max_depth {
            if beam.is_empty() || Instant::now() >= deadline { break; }
            let mut next_beam = Vec::new();
            for (_, state, touched, affected, lost) in beam.into_iter() {
                let mut ranked_pool: Vec<(usize, u32, usize)> = Vec::new();
                let mut pool_cells = Vec::new();
                for id in 0..board.pairs.len() {
                    if lost >> id & 1 == 0 { continue; }
                    route.clear();
                    board.trace_pair(&state, id, scratch, Some(&mut route));
                    let touched_positions: Vec<usize> = route.iter().enumerate()
                        .filter_map(|(pos, cell)| touched.contains(cell).then_some(pos))
                        .collect();
                    for (pos, &cell) in route.iter().enumerate() {
                        if touched.contains(&cell) { continue; }
                        let distance = touched_positions.iter()
                            .map(|&at| pos.abs_diff(at)).min().unwrap_or(usize::MAX / 2);
                        let damage = (differential.cell_masks[cell] & connected_mask).count_ones();
                        if candidate_rank[cell].0 == usize::MAX { pool_cells.push(cell); }
                        if (distance, damage) < candidate_rank[cell] {
                            candidate_rank[cell] = (distance, damage);
                        }
                    }
                }
                for cell in pool_cells {
                    let (distance, damage) = candidate_rank[cell];
                    ranked_pool.push((distance, damage, cell));
                    candidate_rank[cell] = (usize::MAX, u32::MAX);
                }
                ranked_pool.sort_unstable();
                let mut work = state.clone();
                for (_, _, cell) in ranked_pool {
                    for o in 0u8..6 {
                        if o == state[cell] { continue; }
                        if Instant::now() >= deadline { break; }
                        work[cell] = o;
                        let moves = base.moves + touched.iter().map(|&changed| {
                            rotation_cost(board.initial[changed], state[changed])
                                - rotation_cost(board.initial[changed], orientation[changed])
                        }).sum::<i32>()
                            + rotation_cost(board.initial[cell], o)
                            - rotation_cost(board.initial[cell], orientation[cell]);
                        let next_affected = affected | differential.cell_masks[cell];
                        let stats = differential.proposal(
                            board, &work, base, moves, next_affected, scratch, &mut updates);
                        let mut changed = touched.clone();
                        changed.push(cell);
                        if stats.matched >= base.matched {
                            if best.as_ref().map_or(true, |x| {
                                (stats.score, stats.matched, stats.total, Reverse(stats.moves))
                                    > (x.0.score, x.0.matched, x.0.total, Reverse(x.0.moves))
                            }) {
                                best = Some((stats, work.clone()));
                            }
                        } else {
                            let next_lost = updates.iter().fold(0u128, |mask, &(id, value)| {
                                if differential.contribution[id] > 0 && value == 0 {
                                    mask | (1u128 << id)
                                } else { mask }
                            });
                            next_beam.push((stats, work.clone(), changed, next_affected, next_lost));
                            if next_beam.len() > 2 * beam_width {
                                next_beam.sort_unstable_by_key(|x| {
                                    (Reverse(x.0.matched), Reverse(x.0.score),
                                     Reverse(x.0.total), x.0.moves)
                                });
                                next_beam.truncate(beam_width);
                            }
                        }
                        work[cell] = state[cell];
                    }
                }
            }
            next_beam.sort_unstable_by_key(|x| {
                (Reverse(x.0.matched), Reverse(x.0.score), Reverse(x.0.total), x.0.moves)
            });
            next_beam.truncate(beam_width);
            beam = next_beam;
        }
    }
    best.map(|x| x.1)
}

struct ConnectRepairResult {
    candidate: Option<Vec<u8>>,
    trials: usize,
    completed: usize,
    target: usize,
    area: usize,
    changed: usize,
    broken_peak: usize,
}

fn connect_repair_candidate(
    board: &Board,
    orientation: &[u8],
    base: Stats,
    differential: &DifferentialEval,
    scratch: &mut EvalScratch,
    deadline: Instant,
) -> ConnectRepairResult {
    let mut path_a = Vec::new();
    let mut path_b = Vec::new();
    let mut candidates: Vec<(usize, usize, Vec<usize>)> = Vec::new();
    let cells_count = board.valid.len();
    let mut goal_stamp = vec![false; cells_count];
    let mut seen = vec![false; cells_count];
    let mut parent = vec![usize::MAX; cells_count];
    let mut queue = VecDeque::new();

    for id in 0..board.pairs.len() {
        if differential.contribution[id] > 0 { continue; }
        board.trace_exit_cells(orientation, board.pairs[id][0], &mut path_a);
        board.trace_exit_cells(orientation, board.pairs[id][1], &mut path_b);
        for &cell in &path_b { goal_stamp[cell] = true; }
        seen.fill(false);
        parent.fill(usize::MAX);
        queue.clear();
        for &cell in &path_a {
            if !seen[cell] { seen[cell] = true; queue.push_back(cell); }
        }
        let mut goal = usize::MAX;
        while let Some(cell) = queue.pop_front() {
            if goal_stamp[cell] { goal = cell; break; }
            for side in 0..6 {
                let Some((next, _)) = board.next(cell, side) else { continue; };
                if !seen[next] {
                    seen[next] = true;
                    parent[next] = cell;
                    queue.push_back(next);
                }
            }
        }
        for &cell in &path_b { goal_stamp[cell] = false; }
        if goal == usize::MAX { continue; }
        let mut corridor = Vec::new();
        loop {
            corridor.push(goal);
            if parent[goal] == usize::MAX { break; }
            goal = parent[goal];
        }
        if corridor.len() <= 5 { candidates.push((corridor.len(), id, corridor)); }
    }
    candidates.sort_unstable_by_key(|x| x.0);

    let mut best: Option<(Stats, Vec<u8>, usize, usize, usize, usize)> = None;
    let mut trials = 0usize;
    let mut completed = 0usize;
    let mut updates = Vec::with_capacity(board.pairs.len());
    for (_, target, corridor) in candidates.into_iter().take(CONNECT_REPAIR_TARGETS) {
        if Instant::now() >= deadline { break; }
        let mut in_region = vec![false; cells_count];
        let mut region = Vec::new();
        for &cell in &corridor {
            if !in_region[cell] { in_region[cell] = true; region.push(cell); }
            for side in 0..6 {
                if let Some((next, _)) = board.next(cell, side) {
                    if !in_region[next] { in_region[next] = true; region.push(next); }
                }
            }
        }
        if region.len() > 9 { continue; }
        trials += 1;
        region.sort_unstable();
        let mut affected = 1u128 << target;
        for &cell in &region { affected |= differential.cell_masks[cell]; }

        // Monotone region indices avoid generating the same changed subset in
        // different orders. Intermediate states may lose matches; only a complete
        // transaction that adds a match and improves the exact score is returned.
        let mut beam: Vec<(Stats, i64, i32, usize, usize, Vec<u8>)> = vec![
            (base, 0, base.moves, 0, 0, orientation.to_vec())
        ];
        for _depth in 1..=region.len() {
            if Instant::now() >= deadline { break; }
            let mut next_beam = Vec::new();
            for (_, _, moves, next_at, broken_peak, state) in beam.into_iter() {
                for ri in next_at..region.len() {
                    let cell = region[ri];
                    for o in 0u8..6 {
                        if o == orientation[cell] { continue; }
                        let mut work = state.clone();
                        work[cell] = o;
                        let next_moves = moves
                            - rotation_cost(board.initial[cell], state[cell])
                            + rotation_cost(board.initial[cell], o);
                        let stats = differential.proposal(
                            board, &work, base, next_moves, affected, scratch, &mut updates);
                        let target_value = updates.iter().find_map(|&(id, value)|
                            (id == target).then_some(value)).unwrap_or(0);
                        if target_value > 0 { completed += 1; }
                        let next_broken_peak = broken_peak.max(base.matched.saturating_sub(stats.matched));
                        if stats.matched >= base.matched + 1 && stats.score > base.score {
                            if best.as_ref().map_or(true, |x| stats.score > x.0.score) {
                                let changed = region.iter().filter(|&&x|
                                    work[x] != orientation[x]).count();
                                best = Some((stats, work.clone(), target, region.len(),
                                             changed, next_broken_peak));
                            }
                        }
                        next_beam.push((stats, target_value, next_moves, ri + 1,
                                        next_broken_peak, work));
                    }
                }
            }
            next_beam.sort_unstable_by_key(|x| {
                (Reverse(x.1 > 0), Reverse(x.0.matched), Reverse(x.0.score),
                 Reverse(x.0.total), x.0.moves)
            });
            next_beam.truncate(CONNECT_REPAIR_BEAM);
            beam = next_beam;
            if beam.is_empty() { break; }
        }
    }
    if let Some((_, candidate, target, area, changed, broken_peak)) = best {
        ConnectRepairResult { candidate: Some(candidate), trials, completed,
            target, area, changed, broken_peak }
    } else {
        ConnectRepairResult { candidate: None, trials, completed, target: usize::MAX,
            area: 0, changed: 0, broken_peak: 0 }
    }
}

fn search_rotations(board: &Board, orientation: &mut Vec<u8>, start: Instant, deadline: Instant) {
    let cells: Vec<usize> = (0..board.valid.len()).filter(|&i| board.valid[i]).collect();
    let mut rng = Rng(0x9e3779b97f4a7c15 ^ board.W as u64 ^ ((board.M as u64) << 32));
    let mut eval_scratch = EvalScratch::new(board.valid.len());
    let mut current = orientation.clone();
    let mut current_stats = board.evaluate_with_scratch(&current, &mut eval_scratch);
    let use_differential = board.W >= 15;
    let mut differential = DifferentialEval::new(board, &current, &mut eval_scratch);
    let energy = |s: Stats| {
        let q = s.total - board.M as i64 * s.moves as i64;
        s.score as f64 + 3.0 * s.matched as f64 + 0.15 * q as f64
    };
    let mut best = current.clone();
    let mut best_stats = current_stats;
    let span = deadline.saturating_duration_since(start).as_secs_f64().max(0.001);
    let mut iterations = 0usize;
    let mut extend_attempts = 0usize;
    let mut extend_accepts = 0usize;
    let mut repair_attempts = 0usize;
    let mut repair_accepts = 0usize;
    let mut connect_attempts = 0usize;
    let mut connect_accepts = 0usize;
    let mut connect_trials = 0usize;
    let mut connect_completed = 0usize;
    let mut connect_events = Vec::new();
    let mut differential_pairs = 0usize;
    let mut next_extend = start + Duration::from_millis(LOCAL_EXTEND_INTERVAL_MS);
    let mut next_repair = start + Duration::from_secs_f64(0.65 * span);
    let mut next_connect = start + Duration::from_secs_f64(0.55 * span);
    let mut now = Instant::now();
    let mut temperature = SA_START_TEMP;
    let mut undo = Vec::with_capacity(4);
    let mut proposed = Vec::with_capacity(4);
    let mut updates = Vec::with_capacity(board.pairs.len());
    let mut route_cells = Vec::with_capacity(3 * board.valid_count);
    loop {
        // Time queries and powf are visible overhead on small boards, where an
        // evaluation itself is very cheap.  A slightly stale temperature is
        // harmless, so update the schedule once per batch instead of per move.
        if iterations & 255 == 0 {
            now = Instant::now();
            if now >= deadline { break; }
            let frac = (now.duration_since(start).as_secs_f64() / span).min(1.0);
            temperature = SA_START_TEMP.powf(1.0 - frac) * SA_END_TEMP.powf(frac);
        }
        if (board.W + 1) / 2 >= 17 && now >= next_extend {
            next_extend += Duration::from_millis(LOCAL_EXTEND_INTERVAL_MS);
            extend_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(LOCAL_EXTEND_BUDGET_MS)).min(deadline);
            if let Some(candidate) = local_extend_candidate(
                board, &current, &mut rng, local_deadline,
            ) {
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                let next_differential = DifferentialEval::new(board, &candidate, &mut eval_scratch);
                let diff = energy(next) - energy(current_stats);
                if diff >= 0.0 || rng.unit() < (diff / temperature).exp() {
                    current = candidate;
                    current_stats = next;
                    differential = next_differential;
                    extend_accepts += 1;
                    if (next.score, next.matched, next.total, Reverse(next.moves))
                        > (best_stats.score, best_stats.matched, best_stats.total, Reverse(best_stats.moves))
                        && board.tester_safe(&current)
                    {
                        best_stats = next;
                        best.clone_from(&current);
                    }
                }
            }
            now = Instant::now();
            iterations += 1;
            continue;
        }
        if now >= next_repair {
            next_repair += Duration::from_millis(RESTORE_REPAIR_INTERVAL_MS);
            repair_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(RESTORE_REPAIR_BUDGET_MS)).min(deadline);
            if let Some(candidate) = restore_repair_candidate(
                board, &current, current_stats, &differential, &mut eval_scratch,
                &mut rng, local_deadline,
            ) {
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                if (next.score, next.matched, next.total, Reverse(next.moves))
                    > (current_stats.score, current_stats.matched,
                        current_stats.total, Reverse(current_stats.moves))
                {
                    current = candidate;
                    current_stats = next;
                    differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                    repair_accepts += 1;
                    if (next.score, next.matched, next.total, Reverse(next.moves))
                        > (best_stats.score, best_stats.matched, best_stats.total, Reverse(best_stats.moves))
                        && board.tester_safe(&current)
                    {
                        best_stats = next;
                        best.clone_from(&current);
                    }
                }
            }
            now = Instant::now();
            iterations += 1;
            continue;
        }
        if ENABLE_CONNECT_REPAIR && now >= next_connect {
            next_connect += Duration::from_millis(CONNECT_REPAIR_INTERVAL_MS);
            connect_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(CONNECT_REPAIR_BUDGET_MS)).min(deadline);
            let outcome = connect_repair_candidate(
                board, &current, current_stats, &differential, &mut eval_scratch,
                local_deadline,
            );
            connect_trials += outcome.trials;
            connect_completed += outcome.completed;
            let event_meta = (outcome.target, outcome.area, outcome.changed,
                              outcome.broken_peak);
            if let Some(candidate) = outcome.candidate {
                let previous = current_stats;
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                if next.matched > current_stats.matched && next.score > current_stats.score {
                    current = candidate;
                    current_stats = next;
                    differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                    connect_accepts += 1;
                    connect_events.push((event_meta.0,
                        next.matched as i64 - previous.matched as i64,
                        next.total - previous.total,
                        next.moves - previous.moves,
                        next.score - previous.score,
                        event_meta.1, event_meta.2, event_meta.3));
                    if (next.score, next.matched, next.total, Reverse(next.moves))
                        > (best_stats.score, best_stats.matched, best_stats.total, Reverse(best_stats.moves))
                        && board.tester_safe(&current)
                    {
                        best_stats = next;
                        best.clone_from(&current);
                    }
                }
            }
            now = Instant::now();
            iterations += 1;
            continue;
        }
        let changes = 1 + rng.usize(if cells.len() < 80 { 4 } else { 3 });
        undo.clear();
        proposed.clear();
        let mut affected = 0u128;
        for _ in 0..changes {
            let cell = cells[rng.usize(cells.len())];
            if undo.iter().any(|&(x, _)| x == cell) { continue; }
            let old = current[cell];
            // On normal/large boards a +/-1 rotation preserves one of the tile's
            // three connections. Tiny boards can exhaust the wider neighborhood,
            // and restricting them caused a large reachability loss.
            let new_o = if board.valid_count <= 80 {
                let mut o = rng.usize(6) as u8;
                if o == old { o = (o + 1) % 6; }
                o
            } else if rng.usize(2) == 0 {
                (old + 1) % 6
            } else {
                (old + 5) % 6
            };
            undo.push((cell, old));
            proposed.push(new_o);
            if use_differential { affected |= differential.cell_masks[cell]; }
        }
        for (&(cell, _), &new_o) in undo.iter().zip(proposed.iter()) { current[cell] = new_o; }
        let next_moves = current_stats.moves + undo.iter().map(|&(cell, old)| {
            rotation_cost(board.initial[cell], current[cell])
                - rotation_cost(board.initial[cell], old)
        }).sum::<i32>();
        let next = if use_differential {
            differential_pairs += affected.count_ones() as usize;
            differential.proposal(board, &current, current_stats, next_moves,
                affected, &mut eval_scratch, &mut updates)
        } else {
            board.evaluate_with_moves(&current, next_moves, &mut eval_scratch)
        };
        let diff = energy(next) - energy(current_stats);
        if diff >= 0.0 || rng.unit() < (diff / temperature).exp() {
            current_stats = next;
            if use_differential {
                differential.commit(board, &current, &mut eval_scratch, &updates, &mut route_cells);
            }
            if (next.score, next.matched, next.total, Reverse(next.moves))
                > (best_stats.score, best_stats.matched, best_stats.total, Reverse(best_stats.moves))
                && board.tester_safe(&current)
            {
                best_stats = next;
                best.clone_from(&current);
            }
        } else {
            for &(cell, old) in &undo { current[cell] = old; }
        }
        iterations += 1;
        if use_differential && iterations & 65535 == 0 {
            let exact = board.evaluate_with_scratch(&current, &mut eval_scratch);
            assert_eq!((current_stats.matched, current_stats.total, current_stats.moves, current_stats.score),
                (exact.matched, exact.total, exact.moves, exact.score));
        }
    }
    orientation.clone_from(&best);
    let mut final_scratch = EvalScratch::new(board.valid.len());
    let mut actual: Vec<(i64, i64, usize)> = (0..board.pairs.len()).map(|id| {
        let (value, length) = board.trace_pair(orientation, id, &mut final_scratch, None);
        (length, if length > 0 { value / length - 1 } else { -1 }, id)
    }).collect();
    actual.sort_unstable_by_key(|x| Reverse(x.0));
    let bonus_count = board.bonus.iter().filter(|&&x| x).count() as i64;
    let full_bonus_paths = actual.iter()
        .filter(|&&(length, bonuses, _)| length > 0 && bonuses == bonus_count).count();
    let total_bonus_uses: i64 = actual.iter()
        .filter(|&&(length, _, _)| length > 0).map(|&(_, bonuses, _)| bonuses).sum();
    let mut weighted: Vec<(i64, i64, i64, usize)> = actual.iter()
        .filter(|&&(length, _, _)| length > 0)
        .map(|&(length, bonuses, id)| (length * (bonuses + 1), length, bonuses, id))
        .collect();
    weighted.sort_unstable_by_key(|x| Reverse(x.0));
    let bonus_multiplier = (board.bonus.iter().filter(|&&x| x).count() + 1) as i64;
    let hero_rotation_budget = if board.M > 0 {
        actual[0].0.max(0) * bonus_multiplier / board.M as i64
    } else { i64::MAX };
    eprintln!("rotation_search iterations={} extends={}/{} repairs={}/{} connects={}/{} diff_avg={:.2} bonuses={} full_bonus_paths={} total_bonus_uses={} rotation_budget={}/{} longest3={:?} weighted3={:?} best_score={}",
        iterations, extend_accepts, extend_attempts, repair_accepts, repair_attempts,
        connect_accepts, connect_attempts,
        differential_pairs as f64 / iterations.max(1) as f64,
        board.bonus.iter().filter(|&&x| x).count(),
        full_bonus_paths, total_bonus_uses, best_stats.moves, hero_rotation_budget,
        &actual[..3],
        &weighted[..weighted.len().min(3)],
        best_stats.score);
    eprintln!("connect_repair trials={} completed={} accepted={} events={:?}",
        connect_trials, connect_completed, connect_accepts, connect_events);
}

fn log_solution_diagnostics(board: &Board, orientation: &[u8], stats: Stats) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let bonus_count = board.bonus.iter().filter(|&&x| x).count();
    let mut bonus_index = vec![usize::MAX; board.valid.len()];
    let mut next_bonus = 0usize;
    for cell in 0..board.bonus.len() {
        if board.bonus[cell] {
            bonus_index[cell] = next_bonus;
            next_bonus += 1;
        }
    }
    let full_bonus_mask = (1u16 << bonus_count) - 1;
    let mut gap_count = vec![0usize; bonus_count + 1];
    let mut gap_length = vec![0i64; bonus_count + 1];
    let mut gap_potential = vec![0i64; bonus_count + 1];
    let mut near_full = Vec::new();
    let mut bonus_users = vec![Vec::new(); bonus_count];
    let mut bonus_visits = vec![0usize; bonus_count];
    let mut missing_d12_length = vec![0i64; bonus_count];
    let mut route_cells = Vec::new();
    let mut full_bonus_paths = 0usize;
    let mut full_bonus_length = 0i64;
    let mut matched_length = 0i64;
    let mut total_bonus_uses = 0i64;
    let mut weighted = Vec::new();
    let mut matched_details = Vec::new();
    for id in 0..board.pairs.len() {
        route_cells.clear();
        let (value, length) = board.trace_pair(
            orientation, id, &mut scratch, Some(&mut route_cells));
        if length == 0 { continue; }
        let mut bonus_mask = 0u16;
        for &cell in &route_cells {
            let index = bonus_index[cell];
            if index != usize::MAX {
                bonus_mask |= 1u16 << index;
                bonus_visits[index] += 1;
            }
        }
        let bonuses = bonus_mask.count_ones() as i64;
        debug_assert_eq!(bonuses, value / length - 1);
        let missing_mask = full_bonus_mask ^ bonus_mask;
        let gap = missing_mask.count_ones() as usize;
        gap_count[gap] += 1;
        gap_length[gap] += length;
        gap_potential[gap] += length * gap as i64;
        if gap <= 2 {
            near_full.push((gap, length, id, missing_mask, value));
            for index in 0..bonus_count {
                if missing_mask >> index & 1 != 0 {
                    missing_d12_length[index] += length;
                }
            }
        }
        for index in 0..bonus_count {
            if bonus_mask >> index & 1 != 0 { bonus_users[index].push(id); }
        }
        matched_length += length;
        total_bonus_uses += bonuses;
        matched_details.push((id, board.pairs[id][0], board.pairs[id][1],
            length, bonuses, value));
        if bonuses == bonus_count as i64 {
            full_bonus_paths += 1;
            full_bonus_length += length;
        }
        weighted.push((value, length, bonuses, id));
    }
    weighted.sort_unstable_by_key(|x| Reverse(x.0));
    near_full.sort_unstable_by_key(|x| (x.0, Reverse(x.1)));
    let gap_groups: Vec<_> = (0..=bonus_count)
        .filter(|&d| gap_count[d] != 0)
        .map(|d| (d, gap_count[d], gap_length[d], gap_potential[d]))
        .collect();
    let segment_capacity = (3 * board.valid_count) as f64;
    let bonus_capacity = (3 * bonus_count) as f64;
    let rotation_penalty = board.M as i64 * stats.moves as i64;
    let q = stats.total - rotation_penalty;
    let k_ratio = stats.matched as f64 / board.pairs.len().max(1) as f64;
    let full_length_ratio = full_bonus_length as f64 / segment_capacity.max(1.0);
    let matched_length_ratio = matched_length as f64 / segment_capacity.max(1.0);
    let bonus_util = if bonus_count == 0 { 1.0 }
        else { total_bonus_uses as f64 / bonus_capacity };
    let rotation_ratio = rotation_penalty as f64 / stats.total.max(1) as f64;
    let delta_h_10 = 0.1 * q.max(0) as f64 / (bonus_count + 1) as f64;
    eprintln!("diagnostic P={} V={} B={} k={} t={} m={} q={} k_ratio={:.6} full_paths={} full_len={} full_len_ratio={:.6} matched_len={} matched_len_ratio={:.6} bonus_uses={} bonus_util={:.6} rotation_ratio={:.6} delta_h_10={:.3} weighted3={:?}",
        board.pairs.len(), board.valid_count, bonus_count, stats.matched, stats.total,
        stats.moves, q, k_ratio, full_bonus_paths, full_bonus_length, full_length_ratio,
        matched_length, matched_length_ratio, total_bonus_uses, bonus_util,
        rotation_ratio, delta_h_10, &weighted[..weighted.len().min(3)]);
    eprintln!("bonus_gap groups={:?} near_full_top={:?} missing_d12_length={:?} bonus_visits={:?} bonus_users={:?}",
        gap_groups, &near_full[..near_full.len().min(12)], missing_d12_length,
        bonus_visits, bonus_users);
    eprintln!("score_breakdown k={} t={} rotation_moves={} M={} rotation_penalty={} q={} score={} formula={}*({}-{})",
        stats.matched, stats.total, stats.moves, board.M,
        board.M as i64 * stats.moves as i64, q, stats.score,
        stats.matched, stats.total, board.M as i64 * stats.moves as i64);
    eprintln!("matched_path_details fields=(pair_id,exit_a,exit_b,length,bonuses,value) count={} paths={:?}",
        matched_details.len(), matched_details);
    log_segment_decomposition(board, orientation, stats, matched_length);
    log_sacrifice_estimates(board, orientation, stats);
}

fn exit_cell_distance(board: &Board, a: usize, b: usize) -> usize {
    let a = board.exits[a].0;
    let b = board.exits[b].0;
    let dr = a as isize / board.W as isize - b as isize / board.W as isize;
    let dc = a as isize % board.W as isize - b as isize % board.W as isize;
    dr.unsigned_abs().max(dc.unsigned_abs()).max((dr + dc).unsigned_abs())
}

fn minimum_wrong_pairing(
    board: &Board, ids: &[usize],
) -> Option<(usize, Vec<[usize; 2]>)> {
    let endpoints: Vec<usize> = ids.iter().flat_map(|&id| board.pairs[id]).collect();
    let mut used = vec![false; endpoints.len()];
    let mut work = Vec::with_capacity(ids.len());
    let mut best: Option<(usize, Vec<[usize; 2]>)> = None;
    fn rec(
        board: &Board, ids: &[usize], endpoints: &[usize], used: &mut [bool],
        work: &mut Vec<[usize; 2]>, length: usize,
        best: &mut Option<(usize, Vec<[usize; 2]>)>,
    ) {
        if best.as_ref().is_some_and(|x| length >= x.0) { return; }
        let Some(i) = (0..endpoints.len()).find(|&i| !used[i]) else {
            *best = Some((length, work.clone()));
            return;
        };
        used[i] = true;
        for j in i + 1..endpoints.len() {
            if used[j] { continue; }
            let a = endpoints[i];
            let b = endpoints[j];
            let is_original = ids.iter().any(|&id| {
                let pair = board.pairs[id];
                (pair[0] == a && pair[1] == b) || (pair[0] == b && pair[1] == a)
            });
            if is_original { continue; }
            used[j] = true;
            work.push([a, b]);
            // A terminal path traverses both endpoint cells, hence distance + 1.
            rec(board, ids, endpoints, used, work,
                length + exit_cell_distance(board, a, b) + 1, best);
            work.pop();
            used[j] = false;
        }
        used[i] = false;
    }
    rec(board, ids, &endpoints, &mut used, &mut work, 0, &mut best);
    best
}

fn log_sacrifice_estimates(board: &Board, orientation: &[u8], stats: Stats) {
    const POOL: usize = 48;
    const REPORT: usize = 10;
    let bonus_count = board.bonus.iter().filter(|&&x| x).count() as i64;
    let q = stats.total - board.M as i64 * stats.moves as i64;
    let mut paths = Vec::new();
    let mut max_matched_bonus = 0i64;
    for id in 0..board.pairs.len() {
        let pair = board.pairs[id];
        let (end, length, bonuses) = board.trace(orientation, pair[0]);
        if end != pair[1] { continue; }
        let length = length as i64;
        let bonuses = bonuses as i64;
        max_matched_bonus = max_matched_bonus.max(bonuses);
        let value = length * (bonuses + 1);
        let optimistic_supply = length * (bonus_count - bonuses).max(0);
        paths.push((optimistic_supply, id, length, bonuses, value));
    }
    paths.sort_unstable_by_key(|x| (Reverse(x.0), x.4, Reverse(x.2)));
    paths.truncate(POOL.min(paths.len()));
    // margin_num = (k-r)*estimated_delta_q-r*Q. Positive is the exact k-loss test.
    let mut estimates: Vec<(i64, i64, usize, Vec<usize>, Vec<[usize; 2]>,
                            i64, i64, i64, i64)> = Vec::new();
    for r in 2..=3 {
        if stats.matched <= r { continue; }
        if r == 2 {
            for i in 0..paths.len() {
                for j in i + 1..paths.len() {
                    let selected = [&paths[i], &paths[j]];
                    let ids = vec![selected[0].1, selected[1].1];
                    let Some((short_length, virtual_pairs)) =
                        minimum_wrong_pairing(board, &ids) else { continue; };
                    let old_length: i64 = selected.iter().map(|x| x.2).sum();
                    let old_value: i64 = selected.iter().map(|x| x.4).sum();
                    let freed = old_length - short_length as i64;
                    let delta_q = freed * (bonus_count + 1) - old_value;
                    let margin_num = (stats.matched - r) as i64 * delta_q - r as i64 * q;
                    estimates.push((margin_num, delta_q, r, ids, virtual_pairs,
                        old_length, old_value, short_length as i64, freed));
                }
            }
        } else {
            for i in 0..paths.len() {
                for j in i + 1..paths.len() {
                    for h in j + 1..paths.len() {
                        let selected = [&paths[i], &paths[j], &paths[h]];
                        let ids = vec![selected[0].1, selected[1].1, selected[2].1];
                        let Some((short_length, virtual_pairs)) =
                            minimum_wrong_pairing(board, &ids) else { continue; };
                        let old_length: i64 = selected.iter().map(|x| x.2).sum();
                        let old_value: i64 = selected.iter().map(|x| x.4).sum();
                        let freed = old_length - short_length as i64;
                        let delta_q = freed * (bonus_count + 1) - old_value;
                        let margin_num = (stats.matched - r) as i64 * delta_q - r as i64 * q;
                        estimates.push((margin_num, delta_q, r, ids, virtual_pairs,
                            old_length, old_value, short_length as i64, freed));
                    }
                }
            }
        }
    }
    estimates.sort_unstable_by_key(|x| Reverse(x.0));
    let positive = estimates.iter().filter(|x| x.0 > 0).count();
    let report: Vec<_> = estimates.iter().take(REPORT).map(|x| {
        let gain_q_after_k = x.0 as f64 / (stats.matched - x.2) as f64;
        (x.2, x.3.clone(), x.4.clone(), x.5, x.6, x.7, x.8,
         x.1, gain_q_after_k)
    }).collect();
    eprintln!("sacrifice_estimate fields=(r,ids,virtual_pairs,old_length,old_value,Ls_lb,freed,delta_q,gain_q_after_k) pool={} candidates={} positive={} B={} hero_max_bonus={} q={} top={:?}",
        paths.len(), estimates.len(), positive, bonus_count, max_matched_bonus, q, report);
}

fn log_segment_decomposition(
    board: &Board, orientation: &[u8], stats: Stats, expected_matched_segments: i64,
) {
    let capacity = 3 * board.valid_count;
    let terminal_base = board.valid.len() * 6;
    let mut mate = vec![usize::MAX; board.exits.len()];
    for pair in &board.pairs {
        mate[pair[0]] = pair[1];
        mate[pair[1]] = pair[0];
    }
    let mut exit_done = vec![false; board.exits.len()];
    // 0=unseen, 1=matched terminal path, 2=invalid terminal path, 3=internal loop.
    // A segment is keyed by the smaller of its two local ports.
    let mut category = vec![0u8; board.valid.len() * 6];
    let mut matched_segments = 0usize;
    let mut invalid_segments = 0usize;
    let mut invalid_paths = Vec::new();

    for start in 0..board.exits.len() {
        if exit_done[start] { continue; }
        let (cell, enter) = board.exits[start];
        let mut state = cell * 6 + enter;
        let mut segments = Vec::new();
        let mut bonus_seen = vec![false; board.valid.len()];
        let mut bonuses = 0usize;
        let mut end = usize::MAX;
        for _ in 0..=capacity {
            let cell = state / 6;
            let enter = state % 6;
            let out = paired_dir(orientation[cell], enter);
            let key = cell * 6 + enter.min(out);
            segments.push(key);
            if board.bonus[cell] && !bonus_seen[cell] {
                bonus_seen[cell] = true;
                bonuses += 1;
            }
            let next = board.transition[state * 6 + orientation[cell] as usize];
            if next >= terminal_base {
                end = next - terminal_base;
                break;
            }
            state = next;
        }
        assert!(end < board.exits.len());
        exit_done[start] = true;
        exit_done[end] = true;
        let matched = mate[start] == end;
        let potential_value = (segments.len() * (bonuses + 1)) as i64;
        let code = if matched { 1 } else { 2 };
        for &key in &segments {
            assert!(category[key] == 0);
            category[key] = code;
        }
        if matched {
            matched_segments += segments.len();
        } else {
            invalid_segments += segments.len();
            invalid_paths.push((start, end, mate[start], mate[end],
                segments.len(), bonuses, potential_value));
        }
    }

    let mut loops = Vec::new();
    let mut loop_segments = 0usize;
    for cell in 0..board.valid.len() {
        if !board.valid[cell] { continue; }
        for enter in 0..6 {
            let out = paired_dir(orientation[cell], enter);
            let first_key = cell * 6 + enter.min(out);
            if category[first_key] != 0 { continue; }
            let start_state = cell * 6 + enter;
            let mut state = start_state;
            let mut length = 0usize;
            let mut bonus_seen = vec![false; board.valid.len()];
            let mut bonuses = 0usize;
            loop {
                let cell = state / 6;
                let enter = state % 6;
                let out = paired_dir(orientation[cell], enter);
                let key = cell * 6 + enter.min(out);
                if category[key] == 3 { break; }
                assert!(category[key] == 0);
                category[key] = 3;
                length += 1;
                if board.bonus[cell] && !bonus_seen[cell] {
                    bonus_seen[cell] = true;
                    bonuses += 1;
                }
                let next = board.transition[state * 6 + orientation[cell] as usize];
                assert!(next < terminal_base);
                state = next;
                if state == start_state { break; }
            }
            loop_segments += length;
            loops.push((length, bonuses, length * (bonuses + 1)));
        }
    }
    loops.sort_unstable_by_key(|x| Reverse(x.0));
    invalid_paths.sort_unstable_by_key(|x| Reverse(x.4));
    let unused_segments = invalid_segments + loop_segments;
    assert_eq!(matched_segments + unused_segments, capacity);
    assert_eq!(matched_segments as i64, expected_matched_segments);
    eprintln!("segment_breakdown capacity={} strictly_unassigned_segments=0 matched_segments={} invalid_connection_segments={} loop_segments={} reclaimable_segments={} unused_for_score={} unused_ratio={:.6} matched_ratio={:.6} matched_paths={} invalid_paths={} loops={} stats_matched={}",
        capacity, matched_segments, invalid_segments, loop_segments, unused_segments, unused_segments,
        unused_segments as f64 / capacity.max(1) as f64,
        matched_segments as f64 / capacity.max(1) as f64,
        stats.matched, invalid_paths.len(), loops.len(), stats.matched);
    eprintln!("invalid_connection_details fields=(exit_a,exit_b,expected_a,expected_b,length,bonuses,potential_value) paths={:?}",
        invalid_paths);
    eprintln!("internal_loop_details fields=(length,bonuses,potential_value) loops={:?}", loops);
}

fn region_signature(board: &Board, cells: &[usize], local: &[u8]) -> Vec<u8> {
    let mut boundary = Vec::with_capacity(12);
    for i in 0..cells.len() {
        for side in 0..6 {
            let inside = board.next(cells[i], side)
                .is_some_and(|(next, _)| cells.contains(&next));
            if !inside { boundary.push((i, side)); }
        }
    }
    let mut signature = Vec::with_capacity(boundary.len());
    for &(start_cell, start_side) in &boundary {
        let mut cell = start_cell;
        let mut enter = start_side;
        let mut result = u8::MAX;
        for _ in 0..=3 * cells.len() {
            let out = paired_dir(local[cell], enter);
            if let Some((next, next_enter)) = board.next(cells[cell], out) {
                if let Some(next_local) = cells.iter().position(|&x| x == next) {
                    cell = next_local;
                    enter = next_enter;
                    continue;
                }
            }
            result = boundary.iter().position(|&(i, side)| i == cell && side == out)
                .unwrap() as u8;
            break;
        }
        signature.push(result);
    }
    signature
}

fn region_geometry(board: &Board, cells: &[usize]) -> Vec<i8> {
    let mut geometry = vec![-1; cells.len() * 6];
    for i in 0..cells.len() {
        for side in 0..6 {
            if let Some((next, _)) = board.next(cells[i], side) {
                if let Some(j) = cells.iter().position(|&cell| cell == next) {
                    geometry[i * 6 + side] = j as i8;
                }
            }
        }
    }
    geometry
}

fn collect_connected_regions(board: &Board, max_size: usize) -> Vec<Vec<usize>> {
    let mut all = Vec::new();
    let mut level: Vec<Vec<usize>> = (0..board.valid.len())
        .filter(|&cell| board.valid[cell]).map(|cell| vec![cell]).collect();
    for size in 1..=max_size {
        if size >= 2 { all.extend(level.iter().cloned()); }
        if size == max_size { break; }
        let mut next_level = Vec::new();
        for cells in &level {
            for &cell in cells {
                for side in 0..6 {
                    let Some((next, _)) = board.next(cell, side) else { continue; };
                    if cells.contains(&next) { continue; }
                    let mut grown = cells.clone();
                    grown.push(next);
                    grown.sort_unstable();
                    next_level.push(grown);
                }
            }
        }
        next_level.sort_unstable();
        next_level.dedup();
        level = next_level;
    }
    all
}

fn transition_equivalence_table(board: &Board, cells: &[usize]) -> Vec<Vec<u16>> {
    let count = 6usize.pow(cells.len() as u32);
    let mut groups: HashMap<Vec<u8>, Vec<u16>> = HashMap::new();
    for code in 0..count {
        let mut x = code;
        let mut local = vec![0u8; cells.len()];
        for o in &mut local { *o = (x % 6) as u8; x /= 6; }
        groups.entry(region_signature(board, cells, &local))
            .or_default().push(code as u16);
    }
    let mut table = vec![Vec::new(); count];
    for group in groups.into_values() {
        for &code in &group { table[code as usize] = group.clone(); }
    }
    table
}

fn transition_descriptor(
    board: &Board, cells: &[usize], local: &[u8],
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let mut boundary = Vec::new();
    for i in 0..cells.len() {
        for side in 0..6 {
            if !board.next(cells[i], side).is_some_and(|(next, _)| cells.contains(&next)) {
                boundary.push((i, side));
            }
        }
    }
    let mut pairing = Vec::with_capacity(boundary.len());
    let mut lengths = Vec::with_capacity(boundary.len());
    let mut bonuses = Vec::with_capacity(boundary.len());
    for &(start_cell, start_side) in &boundary {
        let mut cell = start_cell;
        let mut enter = start_side;
        let mut length = 0u8;
        let mut bonus_mask = 0u8;
        loop {
            length += 1;
            if board.bonus[cells[cell]] { bonus_mask |= 1 << cell; }
            let out = paired_dir(local[cell], enter);
            if let Some((next, next_enter)) = board.next(cells[cell], out) {
                if let Some(next_local) = cells.iter().position(|&x| x == next) {
                    cell = next_local;
                    enter = next_enter;
                    continue;
                }
            }
            pairing.push(boundary.iter().position(|&(i, side)| i == cell && side == out)
                .unwrap() as u8);
            lengths.push(length);
            bonuses.push(bonus_mask);
            break;
        }
    }
    (pairing, lengths, bonuses)
}

fn improve_by_transition_tables(
    board: &Board, orientation: &mut Vec<u8>, deadline: Instant,
) -> usize {
    let started = Instant::now();
    let regions = collect_connected_regions(board, 4);
    let mut tables: HashMap<Vec<i8>, Vec<Vec<u16>>> = HashMap::new();
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
    let initial = stats;
    let mut accepted = 0usize;
    let mut tested = 0usize;
    let mut visited = 0usize;
    let mut tested_by_size = [0usize; 5];
    let mut accepted_by_size = [0usize; 5];
    let mut nontrivial_hits = 0usize;
    let mut raw_alternatives = 0usize;
    let mut pareto_alternatives = 0usize;
    let mut current_dominated = 0usize;
    let mut positive_candidates = 0usize;
    let mut improving_regions = 0usize;
    let mut delta_moves_by_size = [0i64; 5];
    let mut delta_total_by_size = [0i64; 5];
    let mut delta_score_by_size = [0i64; 5];
    let mut accepted_kind = [0usize; 3]; // rotation-only, value gain, tradeoff/other
    let mut updates = Vec::new();
    let mut route_cells = Vec::new();
    for cells in &regions {
        if Instant::now() >= deadline { break; }
        visited += 1;
        // Exhaustive enumeration shows that an adjacent two-cell region has no
        // non-trivial orientation with the same boundary transition.
        if cells.len() == 2 { continue; }
        let geometry = region_geometry(board, cells);
        if !tables.contains_key(&geometry) {
            tables.insert(geometry.clone(), transition_equivalence_table(board, cells));
        }
        let mut current = Vec::with_capacity(cells.len());
        let mut current_code = 0usize;
        let mut place = 1usize;
        for &cell in cells {
            current.push(orientation[cell]);
            current_code += place * orientation[cell] as usize;
            place *= 6;
        }
        let group = &tables[&geometry][current_code];
        if group.len() <= 1 { continue; }
        nontrivial_hits += 1;
        raw_alternatives += group.len() - 1;
        let mut options = Vec::new();
        for &raw in group {
            let mut code = raw as usize;
            let mut local = vec![0u8; cells.len()];
            for o in &mut local { *o = (code % 6) as u8; code /= 6; }
            let moves: i32 = cells.iter().enumerate().map(|(i, &cell)|
                rotation_cost(board.initial[cell], local[i])).sum();
            let (_, lengths, bonuses) = transition_descriptor(board, cells, &local);
            options.push((raw, moves, lengths, bonuses, local));
        }
        let mut pareto = Vec::new();
        let mut current_is_dominated = false;
        for i in 0..options.len() {
            let dominated = (0..options.len()).any(|j| i != j
                && options[j].1 <= options[i].1
                && options[j].2.iter().zip(&options[i].2).all(|(a, b)| a >= b)
                && options[j].3.iter().zip(&options[i].3).all(|(a, b)| a | b == *a)
                && (options[j].1 < options[i].1
                    || options[j].2 != options[i].2 || options[j].3 != options[i].3));
            if options[i].0 as usize == current_code && dominated {
                current_is_dominated = true;
            }
            if !dominated { pareto.push(i); }
        }
        if current_is_dominated { current_dominated += 1; }
        pareto_alternatives += pareto.iter()
            .filter(|&&i| options[i].0 as usize != current_code).count();
        let mut affected = 0u128;
        let mut old_local_moves = 0i32;
        for &cell in cells {
            affected |= differential.cell_masks[cell];
            old_local_moves += rotation_cost(board.initial[cell], orientation[cell]);
        }
        let mut best: Option<(Stats, Vec<u8>, Vec<(usize, i64)>)> = None;
        for i in pareto {
            if options[i].0 as usize == current_code { continue; }
            tested += 1;
            tested_by_size[cells.len()] += 1;
            for (at, &cell) in cells.iter().enumerate() { orientation[cell] = options[i].4[at]; }
            let moves = stats.moves - old_local_moves + options[i].1;
            let candidate = differential.proposal(
                board, orientation, stats, moves, affected, &mut scratch, &mut updates);
            if candidate.matched == stats.matched && candidate.score > stats.score {
                positive_candidates += 1;
            }
            if candidate.matched == stats.matched && candidate.score > stats.score
                && best.as_ref().map_or(true, |x| candidate.score > x.0.score)
            {
                best = Some((candidate, options[i].4.clone(), updates.clone()));
            }
            for (at, &cell) in cells.iter().enumerate() { orientation[cell] = current[at]; }
            if Instant::now() >= deadline { break; }
        }
        if let Some((next, local, best_updates)) = best {
            improving_regions += 1;
            let dm = next.moves as i64 - stats.moves as i64;
            let dt = next.total - stats.total;
            let ds = next.score - stats.score;
            delta_moves_by_size[cells.len()] += dm;
            delta_total_by_size[cells.len()] += dt;
            delta_score_by_size[cells.len()] += ds;
            if dt == 0 && dm < 0 { accepted_kind[0] += 1; }
            else if dt > 0 { accepted_kind[1] += 1; }
            else { accepted_kind[2] += 1; }
            for (at, &cell) in cells.iter().enumerate() { orientation[cell] = local[at]; }
            differential.commit(
                board, orientation, &mut scratch, &best_updates, &mut route_cells);
            stats = next;
            accepted += 1;
            accepted_by_size[cells.len()] += 1;
        }
    }
    let verified = board.evaluate_with_scratch(orientation, &mut scratch);
    assert!(verified.matched == stats.matched && verified.total == stats.total
        && verified.moves == stats.moves && verified.score == stats.score);
    eprintln!("transition_table regions={} visited={} geometries={} tested={} tested_by_size={:?} accepted={} accepted_by_size={:?} moves_delta={} total_delta={} score_delta={} elapsed_ms={}",
        regions.len(), visited, tables.len(), tested, &tested_by_size[2..], accepted,
        &accepted_by_size[2..], stats.moves - initial.moves,
        stats.total - initial.total, stats.score - initial.score, started.elapsed().as_millis());
    eprintln!("transition_table_usage nontrivial_hits={} raw_alternatives={} pareto_alternatives={} current_dominated={} positive_candidates={} improving_regions={} accepted_kind={:?} delta_moves_by_size={:?} delta_total_by_size={:?} delta_score_by_size={:?}",
        nontrivial_hits, raw_alternatives, pareto_alternatives, current_dominated,
        positive_candidates, improving_regions, accepted_kind, &delta_moves_by_size[2..],
        &delta_total_by_size[2..], &delta_score_by_size[2..]);
    accepted
}

fn collect_triangles(board: &Board) -> Vec<[usize; 3]> {
    let mut triangles = Vec::new();
    for a in 0..board.valid.len() {
        if !board.valid[a] { continue; }
        for side in 0..6 {
            let Some((b, _)) = board.next(a, side) else { continue; };
            let Some((c, _)) = board.next(a, (side + 1) % 6) else { continue; };
            if !(0..6).any(|d| board.next(b, d).is_some_and(|x| x.0 == c)) { continue; }
            let mut triangle = [a, b, c];
            triangle.sort_unstable();
            triangles.push(triangle);
        }
    }
    triangles.sort_unstable();
    triangles.dedup();
    triangles
}

fn reduce_rotations_by_triangles(
    board: &Board, orientation: &mut Vec<u8>, deadline: Instant,
) -> usize {
    let triangles = collect_triangles(board);

    let mut stats = board.evaluate(orientation);
    let initial_moves = stats.moves;
    let initial_total = stats.total;
    let initial_score = stats.score;
    let mut accepted = 0usize;
    loop {
        let mut changed = false;
        for cells in &triangles {
            if Instant::now() >= deadline {
                eprintln!("triangle_post accepted={} rotations_saved={} total_delta={} score_delta={}",
                    accepted, initial_moves - stats.moves, stats.total - initial_total,
                    stats.score - initial_score);
                return accepted;
            }
            let current = [orientation[cells[0]], orientation[cells[1]], orientation[cells[2]]];
            let signature = region_signature(board, cells, &current);
            let old_local_moves: i32 = cells.iter().map(|&cell| {
                rotation_cost(board.initial[cell], orientation[cell])
            }).sum();
            let mut best: Option<(Stats, [u8; 3])> = None;
            for code in 0..216usize {
                let local = [
                    (code % 6) as u8,
                    (code / 6 % 6) as u8,
                    (code / 36) as u8,
                ];
                let local_moves: i32 = (0..3).map(|i| {
                    rotation_cost(board.initial[cells[i]], local[i])
                }).sum();
                if local_moves >= old_local_moves
                    || region_signature(board, cells, &local) != signature
                {
                    continue;
                }
                for i in 0..3 { orientation[cells[i]] = local[i]; }
                let candidate = board.evaluate(orientation);
                if candidate.matched == stats.matched
                    && candidate.score > stats.score
                    && best.as_ref().map_or(true, |x| {
                    (candidate.score, candidate.total, Reverse(candidate.moves))
                        > (x.0.score, x.0.total, Reverse(x.0.moves))
                }) {
                    best = Some((candidate, local));
                }
                for i in 0..3 { orientation[cells[i]] = current[i]; }
            }
            if let Some((next, local)) = best {
                for i in 0..3 { orientation[cells[i]] = local[i]; }
                stats = next;
                accepted += 1;
                changed = true;
            }
        }
        if !changed { break; }
    }
    eprintln!("triangle_post accepted={} rotations_saved={} total_delta={} score_delta={}",
        accepted, initial_moves - stats.moves, stats.total - initial_total,
        stats.score - initial_score);
    accepted
}

fn collect_rhombi(board: &Board) -> Vec<[usize; 4]> {
    let mut rhombi = Vec::new();
    for a in 0..board.valid.len() {
        if !board.valid[a] { continue; }
        for side in 0..6 {
            let Some((b, _)) = board.next(a, side) else { continue; };
            let Some((c, _)) = board.next(a, (side + 1) % 6) else { continue; };
            let Some((d, _)) = board.next(b, (side + 1) % 6) else { continue; };
            if !board.next(c, side).is_some_and(|x| x.0 == d) { continue; }
            let mut cells = [a, b, c, d];
            cells.sort_unstable();
            rhombi.push(cells);
        }
    }
    rhombi.sort_unstable();
    rhombi.dedup();
    rhombi
}

fn rhombus_equivalence_table(board: &Board, cells: &[usize; 4]) -> Vec<Vec<u16>> {
    let mut groups: HashMap<Vec<u8>, Vec<u16>> = HashMap::new();
    for code in 0..1296usize {
        let local = [
            (code % 6) as u8,
            (code / 6 % 6) as u8,
            (code / 36 % 6) as u8,
            (code / 216) as u8,
        ];
        groups.entry(region_signature(board, cells, &local))
            .or_default().push(code as u16);
    }
    let mut table = vec![Vec::new(); 1296];
    for group in groups.into_values() {
        for &code in &group { table[code as usize] = group.clone(); }
    }
    table
}

fn reduce_rotations_by_rhombi(
    board: &Board, orientation: &mut Vec<u8>, deadline: Instant,
) -> usize {
    let rhombi = collect_rhombi(board);

    let mut tables: HashMap<Vec<i8>, Vec<Vec<u16>>> = HashMap::new();
    let mut stats = board.evaluate(orientation);
    let initial_moves = stats.moves;
    let initial_total = stats.total;
    let initial_score = stats.score;
    let mut accepted = 0usize;
    loop {
        let mut changed = false;
        for cells in &rhombi {
            if Instant::now() >= deadline {
                eprintln!("rhombus_post accepted={} rotations_saved={} total_delta={} score_delta={} tables={}",
                    accepted, initial_moves - stats.moves, stats.total - initial_total,
                    stats.score - initial_score, tables.len());
                return accepted;
            }
            let geometry = region_geometry(board, cells);
            if !tables.contains_key(&geometry) {
                tables.insert(geometry.clone(), rhombus_equivalence_table(board, cells));
            }
            let current = [orientation[cells[0]], orientation[cells[1]],
                orientation[cells[2]], orientation[cells[3]]];
            let current_code = current[0] as usize
                + 6 * current[1] as usize
                + 36 * current[2] as usize
                + 216 * current[3] as usize;
            let old_local_moves: i32 = cells.iter().map(|&cell| {
                rotation_cost(board.initial[cell], orientation[cell])
            }).sum();
            let mut best: Option<(Stats, [u8; 4])> = None;
            for &code in &tables[&geometry][current_code] {
                let code = code as usize;
                let local = [
                    (code % 6) as u8,
                    (code / 6 % 6) as u8,
                    (code / 36 % 6) as u8,
                    (code / 216) as u8,
                ];
                let local_moves: i32 = (0..4).map(|i| {
                    rotation_cost(board.initial[cells[i]], local[i])
                }).sum();
                if local_moves >= old_local_moves { continue; }
                for i in 0..4 { orientation[cells[i]] = local[i]; }
                let candidate = board.evaluate(orientation);
                if candidate.matched == stats.matched
                    && candidate.score > stats.score
                    && best.as_ref().map_or(true, |x| {
                        (candidate.score, candidate.total, Reverse(candidate.moves))
                            > (x.0.score, x.0.total, Reverse(x.0.moves))
                    })
                {
                    best = Some((candidate, local));
                }
                for i in 0..4 { orientation[cells[i]] = current[i]; }
            }
            if let Some((next, local)) = best {
                for i in 0..4 { orientation[cells[i]] = local[i]; }
                stats = next;
                accepted += 1;
                changed = true;
            }
        }
        if !changed { break; }
    }
    eprintln!("rhombus_post accepted={} rotations_saved={} total_delta={} score_delta={} tables={}",
        accepted, initial_moves - stats.moves, stats.total - initial_total,
        stats.score - initial_score, tables.len());
    accepted
}

fn improve_by_boundary_signatures(
    board: &Board, orientation: &mut Vec<u8>, deadline: Instant,
) {
    let table_accepted = if ENABLE_TRANSITION_TABLE {
        let table_deadline = (Instant::now() + Duration::from_millis(100)).min(deadline);
        improve_by_transition_tables(board, orientation, table_deadline)
    } else { 0 };
    let mut rounds = 0usize;
    let mut triangle_accepted = 0usize;
    let mut rhombus_accepted = 0usize;
    while Instant::now() < deadline {
        rounds += 1;
        let triangles = reduce_rotations_by_triangles(board, orientation, deadline);
        triangle_accepted += triangles;
        if Instant::now() >= deadline { break; }
        let rhombi = reduce_rotations_by_rhombi(board, orientation, deadline);
        rhombus_accepted += rhombi;
        if triangles == 0 && rhombi == 0 { break; }
    }
    eprintln!("signature_post rounds={} table_accepted={} triangle_accepted={} rhombus_accepted={}",
        rounds, table_accepted, triangle_accepted, rhombus_accepted);
}

fn virtualized_construction_board(
    board: &Board, r: usize,
) -> (Board, Vec<usize>, Vec<[usize; 2]>, usize, usize, usize) {
    const DISTANCE_CANDIDATES: usize = 8;
    const ROUTE_ESTIMATE_MS: u64 = 20;
    if r != 2 && r != 3 {
        return (board.clone(), Vec::new(), Vec::new(), 0, 0, 0);
    }
    let hero = special_order(board).into_iter().next().unwrap_or(usize::MAX);
    let ids: Vec<usize> = (0..board.pairs.len()).filter(|&id| id != hero).collect();
    let mut top: Vec<(usize, usize, usize, Vec<usize>, Vec<[usize; 2]>)> = Vec::new();
    let mut consider = |selected: Vec<usize>| {
        let original: usize = selected.iter().map(|&id| {
            let p = board.pairs[id];
            exit_cell_distance(board, p[0], p[1]) + 1
        }).sum();
        let Some((short, virtual_pairs)) = minimum_wrong_pairing(board, &selected) else {
            return;
        };
        let saved = original.saturating_sub(short);
        top.push((saved, original, short, selected, virtual_pairs));
        top.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1), x.2));
        top.truncate(DISTANCE_CANDIDATES);
    };
    if r == 2 {
        for i in 0..ids.len() {
            for j in i + 1..ids.len() { consider(vec![ids[i], ids[j]]); }
        }
    } else {
        for i in 0..ids.len() {
            for j in i + 1..ids.len() {
                for k in j + 1..ids.len() {
                    consider(vec![ids[i], ids[j], ids[k]]);
                }
            }
        }
    }
    if top.is_empty() { return (board.clone(), Vec::new(), Vec::new(), 0, 0, 0); }
    let mut route_ranked = Vec::new();
    for (saved_lb, original, short, selected, virtual_pairs) in top.iter().cloned() {
        let mut orientation = board.initial.clone();
        let mut fixed = vec![-1i8; orientation.len()];
        let mut order = virtual_pairs.clone();
        order.sort_unstable_by_key(|p| exit_cell_distance(board, p[0], p[1]));
        let estimate_deadline = Instant::now() + Duration::from_millis(ROUTE_ESTIMATE_MS);
        let mut route_length = 0usize;
        let mut complete = true;
        for pair in order {
            let Some(route) = find_route(
                board, &orientation, &fixed, pair[0], pair[1], 2,
                false, None, None, estimate_deadline,
            ) else {
                complete = false;
                break;
            };
            route_length += route.length;
            apply_route(&mut orientation, &mut fixed, &route, true);
        }
        if complete {
            let route_saved = original.saturating_sub(route_length);
            route_ranked.push((route_saved, saved_lb, Reverse(route_length),
                original, short, route_length, selected, virtual_pairs));
        }
    }
    route_ranked.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1), x.2));
    let (original, short, route_length, selected, virtual_pairs) =
        if let Some(x) = route_ranked.into_iter().next() {
            (x.3, x.4, x.5, x.6, x.7)
        } else {
            let x = top.into_iter().next().unwrap();
            (x.1, x.2, x.2, x.3, x.4)
        };
    let mut virtual_board = board.clone();
    for (at, &id) in selected.iter().enumerate() {
        virtual_board.pairs[id] = virtual_pairs[at];
    }
    (virtual_board, selected, virtual_pairs, original, short, route_length)
}

fn minimum_virtual_cycle(
    board: &Board, ids: &[usize],
) -> (usize, Vec<[usize; 2]>) {
    debug_assert!((2..=4).contains(&ids.len()));
    let mut order = vec![ids[0]];
    let mut used = vec![false; ids.len()];
    used[0] = true;
    let mut best = (usize::MAX, Vec::new());
    fn enumerate_orders(
        board: &Board, ids: &[usize], used: &mut [bool], order: &mut Vec<usize>,
        best: &mut (usize, Vec<[usize; 2]>),
    ) {
        if order.len() == ids.len() {
            for mask in 0..1usize << order.len() {
                let oriented: Vec<[usize; 2]> = order.iter().enumerate().map(|(at, &id)| {
                    let p = board.pairs[id];
                    if (mask >> at) & 1 == 0 { p } else { [p[1], p[0]] }
                }).collect();
                let mut cost = 0usize;
                let mut virtual_pairs = Vec::with_capacity(order.len());
                for at in 0..oriented.len() {
                    let edge = [oriented[at][1], oriented[(at + 1) % oriented.len()][0]];
                    cost += exit_cell_distance(board, edge[0], edge[1]) + 1;
                    virtual_pairs.push(edge);
                }
                if cost < best.0 {
                    *best = (cost, virtual_pairs);
                }
            }
            return;
        }
        for at in 1..ids.len() {
            if used[at] { continue; }
            used[at] = true;
            order.push(ids[at]);
            enumerate_orders(board, ids, used, order, best);
            order.pop();
            used[at] = false;
        }
    }
    enumerate_orders(board, ids, &mut used, &mut order, &mut best);
    best
}

fn beam_long_cycle_construction_board(
    board: &Board, threshold_num: usize, threshold_den: usize,
) -> (Board, Vec<usize>, Vec<[usize; 2]>, usize, usize, usize) {
    let radius = (board.W + 1) / 2;
    let threshold = (radius * threshold_num + threshold_den - 1) / threshold_den;
    let mut long_ids: Vec<usize> = (0..board.pairs.len())
        .filter(|&id| {
            let p = board.pairs[id];
            exit_cell_distance(board, p[0], p[1]) >= threshold
        })
        .collect();
    long_ids.sort_unstable_by_key(|&id| {
        let p = board.pairs[id];
        Reverse(exit_cell_distance(board, p[0], p[1]))
    });
    if long_ids.len() < MIN_LONG_PAIRS_FOR_VIRTUALIZATION {
        eprintln!("long_virtual disabled threshold={} long_pairs={} minimum={}",
            threshold, long_ids.len(), MIN_LONG_PAIRS_FOR_VIRTUALIZATION);
        return (board.clone(), Vec::new(), Vec::new(), 0, 0, 0);
    }

    #[derive(Clone)]
    struct PairingState {
        active: Vec<usize>,
        sacrificed: Vec<usize>,
        virtual_pairs: Vec<[usize; 2]>,
        cycle_sizes: Vec<usize>,
        original_distance: usize,
        virtual_distance: usize,
    }

    let initial_long_count = long_ids.len();
    let hero_id = long_ids[0];
    let bonus_count = board.bonus.iter().filter(|&&x| x).count();
    let segment_capacity = 3 * board.valid_count;
    let shortest_sum: usize = board.pairs.iter().map(|p| {
        exit_cell_distance(board, p[0], p[1]) + 1
    }).sum();
    let hero_pair = board.pairs[hero_id];
    let hero_shortest = exit_cell_distance(board, hero_pair[0], hero_pair[1]) + 1;
    let estimated_hero_length = segment_capacity.saturating_sub(shortest_sum)
        .saturating_add(hero_shortest);
    let estimated_rotation_penalty = board.M.max(0) as usize * board.valid_count / 3;
    let estimated_q = segment_capacity
        .saturating_add(bonus_count * estimated_hero_length)
        .saturating_sub(estimated_rotation_penalty).max(1);
    let coeff_num = std::env::var("MM166_VIRTUAL_GAIN_COEFF_NUM").ok()
        .and_then(|x| x.parse().ok()).unwrap_or(VIRTUAL_GAIN_COEFF_NUM);
    let coeff_den = std::env::var("MM166_VIRTUAL_GAIN_COEFF_DEN").ok()
        .and_then(|x| x.parse().ok()).unwrap_or(VIRTUAL_GAIN_COEFF_DEN).max(1);

    let mut best_choice: Option<(i128, i128, PairingState)> = None;
    // Keep the longest pair as the hero.  For every prefix beginning at the
    // second-longest pair, find the cheapest 2--4-cycle decomposition by Beam.
    for sacrifice_target in 2..initial_long_count {
        if sacrifice_target >= board.pairs.len() { break; }
        let mut beam = vec![PairingState {
            active: long_ids[1..=sacrifice_target].to_vec(),
            sacrificed: Vec::new(),
            virtual_pairs: Vec::new(),
            cycle_sizes: Vec::new(),
            original_distance: 0,
            virtual_distance: 0,
        }];
        while beam.iter().any(|s| !s.active.is_empty()) {
            let mut next = Vec::new();
            let current = std::mem::take(&mut beam);
            for state in current {
                if state.active.is_empty() {
                    next.push(state);
                    continue;
                }
                let first = state.active[0];
                let mut groups: Vec<(usize, Reverse<usize>, Vec<usize>, Vec<[usize; 2]>)> = Vec::new();
                let mut add_group = |group: Vec<usize>| {
                    let old_cost: usize = group.iter().map(|&id| {
                        let p = board.pairs[id];
                        exit_cell_distance(board, p[0], p[1]) + 1
                    }).sum();
                    let (cost, vp) = minimum_virtual_cycle(board, &group);
                    groups.push((cost * 12 / group.len(), Reverse(old_cost), group, vp));
                };
                for b in 1..state.active.len() {
                    add_group(vec![first, state.active[b]]);
                    for c in b + 1..state.active.len() {
                        add_group(vec![first, state.active[b], state.active[c]]);
                        for d in c + 1..state.active.len() {
                            add_group(vec![first, state.active[b], state.active[c], state.active[d]]);
                        }
                    }
                }
                groups.sort_unstable_by_key(|x| (x.0, x.1, x.2.clone()));
                groups.truncate(VIRTUAL_GROUP_CANDIDATES);
                for (_, Reverse(old_cost), group, vp) in groups {
                    let mut child = state.clone();
                    child.active.retain(|id| !group.contains(id));
                    child.sacrificed.extend(group.iter().copied());
                    child.virtual_pairs.extend(vp.iter().copied());
                    child.cycle_sizes.push(group.len());
                    child.original_distance += old_cost;
                    child.virtual_distance += vp.iter().map(|p| {
                        exit_cell_distance(board, p[0], p[1]) + 1
                    }).sum::<usize>();
                    next.push(child);
                }
            }
            if next.is_empty() { break; }
            next.sort_unstable_by_key(|s| {
                let done = s.sacrificed.len().max(1);
                (s.virtual_distance * sacrifice_target / done,
                 s.virtual_distance,
                 Reverse(s.original_distance.saturating_sub(s.virtual_distance)))
            });
            next.truncate(VIRTUAL_PAIRING_BEAM);
            beam = next;
        }
        beam.retain(|s| s.active.is_empty()
            && s.sacrificed.len() == sacrifice_target);
        beam.sort_unstable_by_key(|s| s.virtual_distance);
        let Some(candidate) = beam.into_iter().next() else { continue; };
        let saved = candidate.original_distance.saturating_sub(candidate.virtual_distance);
        let remaining_k = board.pairs.len() - sacrifice_target;
        let adjusted_gain_num = coeff_num as i128 * saved as i128
            * bonus_count as i128 * remaining_k as i128;
        let connection_loss_num = coeff_den as i128 * sacrifice_target as i128
            * estimated_q as i128;
        let margin_num = adjusted_gain_num - connection_loss_num;
        let normalized_margin = margin_num * 1_000_000 / remaining_k as i128;
        eprintln!("long_virtual_candidate hero={} r={} cycles={:?} saved={} gain={} loss={} margin_num={} coeff={}/{}",
            hero_id, sacrifice_target, candidate.cycle_sizes, saved,
            saved * bonus_count, sacrifice_target * estimated_q / remaining_k.max(1),
            margin_num, coeff_num, coeff_den);
        if margin_num > 0 && best_choice.as_ref().map_or(true, |x| normalized_margin > x.0) {
            best_choice = Some((normalized_margin, margin_num, candidate));
        }
    }
    let Some((_, best_margin, best)) = best_choice else {
        eprintln!("long_virtual rejected threshold={} long_pairs={} hero={} B={} estimated_q={} coeff={}/{}",
            threshold, initial_long_count, hero_id, bonus_count, estimated_q,
            coeff_num, coeff_den);
        return (board.clone(), Vec::new(), Vec::new(), 0, 0, 0);
    };

    let mut virtual_board = board.clone();
    for (&id, &edge) in best.sacrificed.iter().zip(&best.virtual_pairs) {
            virtual_board.pairs[id] = edge;
    }
    eprintln!("long_virtual threshold={} initial_long={} hero={} cycle_sizes={:?} sacrificed={} original_distance={} virtual_distance={} saved={} estimated_q={} B={} margin_num={} coeff={}/{}",
        threshold, initial_long_count, hero_id, best.cycle_sizes, best.sacrificed.len(),
        best.original_distance, best.virtual_distance,
        best.original_distance.saturating_sub(best.virtual_distance), estimated_q,
        bonus_count, best_margin, coeff_num, coeff_den);
    (virtual_board, best.sacrificed, best.virtual_pairs, best.original_distance,
        best.virtual_distance, best.virtual_distance)
}

fn build_exits(N: usize, valid: &[bool]) -> (Vec<(usize, usize)>, Vec<i32>) {
    let W = 2 * N - 1;
    let inside = |r: isize, c: isize| r >= 0 && c >= 0 && r < W as isize && c < W as isize
        && valid[r as usize * W + c as usize];
    let mut exits = Vec::new();
    let mut push = |r: usize, c: usize, d: usize| {
        debug_assert!(!inside(r as isize + DR[d], c as isize + DC[d]));
        exits.push((r * W + c, d));
    };
    for c in N - 1..W {
        if c == N - 1 { push(0, c, 5); }
        push(0, c, 0); push(0, c, 1);
        if c == W - 1 { push(0, c, 2); }
    }
    for r in 1..N - 1 { push(r, W - 1, 1); push(r, W - 1, 2); }
    push(N - 1, W - 1, 1); push(N - 1, W - 1, 2); push(N - 1, W - 1, 3);
    for r in N..W - 1 { let c = W + N - 2 - r; push(r, c, 2); push(r, c, 3); }
    for c in (0..N).rev() {
        if c == N - 1 { push(W - 1, c, 2); }
        push(W - 1, c, 3); push(W - 1, c, 4);
        if c == 0 { push(W - 1, c, 5); }
    }
    for r in (N..W - 1).rev() { push(r, 0, 4); push(r, 0, 5); }
    push(N - 1, 0, 4); push(N - 1, 0, 5); push(N - 1, 0, 0);
    for r in (1..N - 1).rev() { let c = N - 1 - r; push(r, c, 5); push(r, c, 0); }
    let mut id = vec![-1; valid.len() * 6];
    for (i, &(cell, d)) in exits.iter().enumerate() { id[cell * 6 + d] = i as i32; }
    (exits, id)
}

fn construct_initial(
    board: &Board, phase_start: Instant, construction_deadline: Instant, label: &str,
) -> Vec<u8> {
    let initial_stats = board.evaluate(&board.initial);
    let mut best_orientation = board.initial.clone();
    let mut best_stats = initial_stats;
    let specials = special_order(board);
    for &reserved in specials.iter().take(LAYERED_SPECIAL_TRIALS) {
        if Instant::now() >= construction_deadline { break; }
        let outer_deadline = (Instant::now() + Duration::from_millis(700)).min(construction_deadline);
        let special_deadline = (outer_deadline + Duration::from_millis(350)).min(construction_deadline);
        let (mut candidate, layers, done, special_t) = build_layered_one_special(
            board, reserved, outer_deadline, special_deadline,
        );
        polish(board, &mut candidate,
            (Instant::now() + Duration::from_millis(80)).min(construction_deadline));
        let stats = board.evaluate(&candidate);
        eprintln!("construct label={} layered reserved={} layers={:?} special_done={} special_t={} k={} t={} m={} score={}",
            label, reserved, layers, done, special_t,
            stats.matched, stats.total, stats.moves, stats.score);
        if stats.score > best_stats.score && board.tester_safe(&candidate) {
            best_stats = stats;
            best_orientation = candidate;
        }
    }
    for &width in &WIDTHS {
        if Instant::now() >= construction_deadline { break; }
        let outer_deadline = (Instant::now() + Duration::from_millis(450)).min(construction_deadline);
        let (outer, _) = build_outer(board, width, &[], outer_deadline);
        let outer_stats = board.evaluate(&outer);
        if outer_stats.score > best_stats.score && board.tester_safe(&outer) {
            best_stats = outer_stats;
            best_orientation = outer;
        }
        for count in 1..=MAX_SPECIAL {
            if Instant::now() >= construction_deadline { break; }
            let chosen = &specials[..count.min(specials.len())];
            let gate_deadline = (Instant::now() + Duration::from_millis(180)).min(construction_deadline);
            let (gated_outer, gated_fixed) = build_outer(board, width, chosen, gate_deadline);
            let special_deadline = (Instant::now() + Duration::from_millis(260)).min(construction_deadline);
            let (mut candidate, special_t, done) = build_with_specials(
                board, &gated_outer, &gated_fixed, width, chosen, special_deadline,
            );
            polish(board, &mut candidate,
                (Instant::now() + Duration::from_millis(30)).min(construction_deadline));
            let stats = board.evaluate(&candidate);
            eprintln!("construct label={} legacy width={} reserved={} done={} special_t={} k={} t={} m={} score={}",
                label, width, count, done, special_t,
                stats.matched, stats.total, stats.moves, stats.score);
            if stats.score > best_stats.score && board.tester_safe(&candidate) {
                best_stats = stats;
                best_orientation = candidate;
            }
        }
    }
    eprintln!("construct_done label={} k={} t={} m={} score={} elapsed_ms={}",
        label, best_stats.matched, best_stats.total, best_stats.moves, best_stats.score,
        phase_start.elapsed().as_millis());
    best_orientation
}

fn main() {
    let start = Instant::now();
    let mut sc = Scanner::new();
    let N: usize = sc.next();
    let M: i32 = sc.next();
    let B: usize = sc.next();
    let P: usize = sc.next();
    let mut pairs = Vec::with_capacity(P);
    for _ in 0..P {
        pairs.push([sc.next(), sc.next()]);
    }
    let W = 2 * N - 1;
    let mut valid = vec![false; W * W];
    let mut initial = vec![0u8; W * W];
    for cell in 0..W * W {
        let x: i32 = sc.next();
        if x >= 0 { valid[cell] = true; initial[cell] = x as u8; }
    }
    let mut bonus = vec![false; W * W];
    for _ in 0..B {
        let r: usize = sc.next();
        let c: usize = sc.next();
        bonus[r * W + c] = true;
    }
    let (exits, exit_id) = build_exits(N, &valid);
    assert_eq!(exits.len(), 6 * W);
    let mut boundary_depth = vec![usize::MAX; W * W];
    let mut q = VecDeque::new();
    for &(cell, _) in &exits {
        if boundary_depth[cell] != 0 { boundary_depth[cell] = 0; q.push_back(cell); }
    }
    while let Some(cell) = q.pop_front() {
        let r = cell / W;
        let c = cell % W;
        for d in 0..6 {
            let nr = r as isize + DR[d];
            let nc = c as isize + DC[d];
            if nr >= 0 && nc >= 0 && nr < W as isize && nc < W as isize {
                let next = nr as usize * W + nc as usize;
                if valid[next] && boundary_depth[next] == usize::MAX {
                    boundary_depth[next] = boundary_depth[cell] + 1;
                    q.push_back(next);
                }
            }
        }
    }
    let valid_count = valid.iter().filter(|&&x| x).count();
    let terminal_base = valid.len() * 6;
    let mut transition = vec![0usize; valid.len() * 36];
    for cell in 0..valid.len() {
        if !valid[cell] { continue; }
        let r = cell / W;
        let c = cell % W;
        for enter in 0..6 {
            let state = cell * 6 + enter;
            for o in 0u8..6 {
                let out = paired_dir(o, enter);
                let nr = r as isize + DR[out];
                let nc = c as isize + DC[out];
                transition[state * 6 + o as usize] = if nr >= 0 && nc >= 0
                    && nr < W as isize && nc < W as isize
                    && valid[nr as usize * W + nc as usize]
                {
                    (nr as usize * W + nc as usize) * 6 + (out + 3) % 6
                } else {
                    terminal_base + exit_id[cell * 6 + out] as usize
                };
            }
        }
    }
    let board = Board { W, M, initial: initial.clone(), valid, bonus, exits, exit_id,
        pairs, transition, boundary_depth, valid_count };
    let requested_variant = std::env::var("MM166_VIRTUAL_R").ok()
        .and_then(|x| x.parse::<usize>().ok());
    let auto_variants = std::env::var("MM166_VIRTUAL_AUTO")
        .map(|x| x != "0").unwrap_or(false);
    let disable_long_virtual = std::env::var("MM166_DISABLE_LONG_VIRTUAL")
        .map(|x| x != "0").unwrap_or(false);
    let long_threshold_num = std::env::var("MM166_LONG_THRESHOLD_NUM").ok()
        .and_then(|x| x.parse().ok()).unwrap_or(LONG_PAIR_DISTANCE_NUM);
    let long_threshold_den = std::env::var("MM166_LONG_THRESHOLD_DEN").ok()
        .and_then(|x| x.parse().ok()).unwrap_or(LONG_PAIR_DISTANCE_DEN).max(1);
    // The three-start oracle is useful in long experiments, but its construction
    // cost does not pay back inside ten seconds.  Keep baseline as production
    // default and expose both experiments through environment variables.
    let selected_mode = if auto_variants {
        None
    } else {
        Some(requested_variant.unwrap_or(0))
    };
    let (mut best_orientation, mut best_stats, _solve_start, deadline, selected_variant) =
        if let Some(virtual_r) = selected_mode {
            let (construction_board, sacrificed, virtual_pairs, original_distance,
                 virtual_distance, estimated_route_length) = if virtual_r == 0
                    && !disable_long_virtual {
                beam_long_cycle_construction_board(
                    &board, long_threshold_num, long_threshold_den)
            } else {
                virtualized_construction_board(&board, virtual_r)
            };
            let solve_start = Instant::now();
            let deadline = solve_start + Duration::from_millis(TIME_LIMIT_MS);
            eprintln!("variant r={} sacrificed={:?} virtual_pairs={:?} original_distance={} virtual_distance={} estimated_route_length={} saved_distance={} route_saved={} selection_ms={}",
                virtual_r, sacrificed, virtual_pairs, original_distance, virtual_distance,
                estimated_route_length, original_distance.saturating_sub(virtual_distance),
                original_distance.saturating_sub(estimated_route_length),
                solve_start.duration_since(start).as_millis());
            let construction_deadline =
                (solve_start + Duration::from_millis(CONSTRUCTION_LIMIT_MS)).min(deadline);
            let orientation = construct_initial(
                &construction_board, solve_start, construction_deadline, "single");
            let stats = board.evaluate(&orientation);
            (orientation, stats, solve_start, deadline, virtual_r)
        } else {
            let v0 = if disable_long_virtual {
                (board.clone(), Vec::new(), Vec::new(), 0, 0, 0)
            } else {
                beam_long_cycle_construction_board(
                    &board, long_threshold_num, long_threshold_den)
            };
            let v2 = virtualized_construction_board(&board, 2);
            let v3 = virtualized_construction_board(&board, 3);
            let variants = vec![(0usize, v0), (2usize, v2), (3usize, v3)];
            let solve_start = Instant::now();
            let deadline = solve_start + Duration::from_millis(TIME_LIMIT_MS);
            // Keep the reliable baseline construction deep.  Virtual pairings are
            // deliberately cheap probes; the winner still receives the common SA.
            let construction_ms = [2_400u64, 700, 700];
            let mut candidates: Vec<(usize, Vec<u8>, Stats)> = Vec::new();
            for (at, (r, (construction_board, sacrificed, virtual_pairs,
                          original_distance, virtual_distance, estimated_route_length)))
                in variants.into_iter().enumerate()
            {
                let phase_start = Instant::now();
                let phase_deadline = (phase_start
                    + Duration::from_millis(construction_ms[at])).min(deadline);
                eprintln!("auto_variant r={} sacrificed={:?} virtual_pairs={:?} original_distance={} virtual_distance={} estimated_route_length={} route_saved={}",
                    r, sacrificed, virtual_pairs, original_distance, virtual_distance,
                    estimated_route_length,
                    original_distance.saturating_sub(estimated_route_length));
                let orientation = construct_initial(
                    &construction_board, phase_start, phase_deadline,
                    if r == 0 { "r0" } else if r == 2 { "r2" } else { "r3" });
                let stats = board.evaluate(&orientation);
                candidates.push((r, orientation, stats));
            }
            for candidate in &mut candidates {
                if Instant::now() >= deadline { break; }
                let pilot_start = Instant::now();
                let pilot_deadline = (pilot_start + Duration::from_millis(150)).min(deadline);
                polish(&board, &mut candidate.1,
                    (pilot_start + Duration::from_millis(20)).min(pilot_deadline));
                search_rotations(&board, &mut candidate.1, Instant::now(), pilot_deadline);
                candidate.2 = board.evaluate(&candidate.1);
                eprintln!("auto_pilot r={} k={} t={} m={} score={}", candidate.0,
                    candidate.2.matched, candidate.2.total,
                    candidate.2.moves, candidate.2.score);
            }
            candidates.sort_unstable_by_key(|x| {
                (Reverse(x.2.score), Reverse(x.2.matched),
                 Reverse(x.2.total), x.2.moves)
            });
            let (r, orientation, stats) = candidates.into_iter().next().unwrap();
            eprintln!("auto_selected r={} k={} t={} m={} score={} phase_elapsed_ms={}",
                r, stats.matched, stats.total, stats.moves, stats.score,
                solve_start.elapsed().as_millis());
            (orientation, stats, solve_start, deadline, r)
        };

    if Instant::now() < deadline {
        polish(&board, &mut best_orientation, (Instant::now() + Duration::from_millis(100)).min(deadline));
        search_rotations(&board, &mut best_orientation, Instant::now(), deadline);
        let postprocess_deadline = Instant::now() + Duration::from_millis(POSTPROCESS_LIMIT_MS);
        improve_by_boundary_signatures(
            &board, &mut best_orientation, postprocess_deadline);
        best_stats = board.evaluate(&best_orientation);
    }
    log_solution_diagnostics(&board, &best_orientation, best_stats);
    eprintln!("final selected_r={} k={} t={} m={} score={} elapsed_ms={}", selected_variant,
        best_stats.matched, best_stats.total, best_stats.moves, best_stats.score,
        start.elapsed().as_millis());

    let mut moves = Vec::new();
    for cell in 0..best_orientation.len() {
        if !board.valid[cell] { continue; }
        let from = board.initial[cell] as i32;
        let to = best_orientation[cell] as i32;
        let cw = (to - from + 6) % 6;
        let ccw = (from - to + 6) % 6;
        let (count, dir) = if cw <= ccw { (cw, 1) } else { (ccw, -1) };
        for _ in 0..count { moves.push((cell / W, cell % W, dir)); }
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    writeln!(out, "{}", moves.len()).unwrap();
    for (r, c, d) in moves { writeln!(out, "{} {} {}", r, c, d).unwrap(); }
}
