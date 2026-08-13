#![allow(non_snake_case)]

use std::cmp::Reverse;
use std::collections::VecDeque;
use std::io::{self, Write};
use std::str::FromStr;
use std::time::{Duration, Instant};

// Search parameters are kept here so experiments use one visible configuration.
const TIME_LIMIT_MS: u64 = 9_200;
const NORMAL_BEAM: usize = 72;
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
const RESTORE_REPAIR_INTERVAL_MS: u64 = 80;
const RESTORE_REPAIR_BUDGET_MS: u64 = 6;
const SA_START_TEMP: f64 = 240.0;
const SA_END_TEMP: f64 = 1.0;

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
    rng: &mut Rng,
    deadline: Instant,
) -> Option<Vec<u8>> {
    let rotated: Vec<usize> = (0..board.valid.len())
        .filter(|&cell| board.valid[cell] && orientation[cell] != board.initial[cell])
        .collect();
    if rotated.is_empty() { return None; }

    // Restore one center tile, then exhaustively choose two adjacent tile
    // orientations. This gives the three lines changed at the center a chance
    // to reconnect locally instead of accepting a destructive one-tile move.
    let attempts = rotated.len().min(8);
    let mut best: Option<(Stats, Vec<u8>)> = None;
    for attempt in 0..attempts {
        if Instant::now() >= deadline { break; }
        let center = rotated[(rng.usize(rotated.len()) + attempt) % rotated.len()];
        let mut neighbors = Vec::new();
        for side in 0..6 {
            if let Some((cell, _)) = board.next(center, side) {
                if !neighbors.contains(&cell) { neighbors.push(cell); }
            }
        }
        if neighbors.len() < 2 { continue; }
        let offset = rng.usize(neighbors.len());
        for step in 0..neighbors.len() {
            let a = neighbors[(offset + step) % neighbors.len()];
            let b = neighbors[(offset + step + 1) % neighbors.len()];
            if a == b { continue; }
            let mut candidate = orientation.to_vec();
            candidate[center] = board.initial[center];
            for oa in 0u8..6 {
                candidate[a] = oa;
                for ob in 0u8..6 {
                    if Instant::now() >= deadline { break; }
                    candidate[b] = ob;
                    let stats = board.evaluate(&candidate);
                    if best.as_ref().map_or(true, |x| {
                        (stats.score, stats.matched, stats.total, Reverse(stats.moves))
                            > (x.0.score, x.0.matched, x.0.total, Reverse(x.0.moves))
                    }) {
                        best = Some((stats, candidate.clone()));
                    }
                }
            }
        }
    }
    best.map(|x| x.1)
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
    let mut differential_pairs = 0usize;
    let mut next_extend = start + Duration::from_millis(LOCAL_EXTEND_INTERVAL_MS);
    let mut next_repair = start + Duration::from_secs_f64(0.65 * span);
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
                board, &current, &mut rng, local_deadline,
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
        let changes = 1 + rng.usize(if cells.len() < 80 { 4 } else { 3 });
        undo.clear();
        proposed.clear();
        let mut affected = 0u128;
        for _ in 0..changes {
            let cell = cells[rng.usize(cells.len())];
            if undo.iter().any(|&(x, _)| x == cell) { continue; }
            let old = current[cell];
            let mut new_o = rng.usize(6) as u8;
            if new_o == old { new_o = (new_o + 1) % 6; }
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
    let bonus_multiplier = (board.bonus.iter().filter(|&&x| x).count() + 1) as i64;
    let hero_rotation_budget = if board.M > 0 {
        actual[0].0.max(0) * bonus_multiplier / board.M as i64
    } else { i64::MAX };
    eprintln!("rotation_search iterations={} extends={}/{} repairs={}/{} diff_avg={:.2} bonuses={} rotation_budget={}/{} actual_top3={:?} best_score={}",
        iterations, extend_accepts, extend_attempts, repair_accepts, repair_attempts,
        differential_pairs as f64 / iterations.max(1) as f64,
        board.bonus.iter().filter(|&&x| x).count(),
        best_stats.moves, hero_rotation_budget,
        &actual[..3],
        best_stats.score);
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

fn main() {
    let start = Instant::now();
    let deadline = start + Duration::from_millis(TIME_LIMIT_MS);
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

    let initial_stats = board.evaluate(&initial);
    let mut best_orientation = initial.clone();
    let mut best_stats = initial_stats;
    eprintln!("initial k={} t={} m={} score={}", initial_stats.matched, initial_stats.total, initial_stats.moves, initial_stats.score);
    let specials = special_order(&board);
    // All construction locks are discarded after this point.  The selected board
    // is only an initial state; the remaining time anneals every tile freely.
    let construction_deadline =
        (start + Duration::from_millis(CONSTRUCTION_LIMIT_MS)).min(deadline);

    for &reserved in specials.iter().take(LAYERED_SPECIAL_TRIALS) {
        if Instant::now() >= construction_deadline { break; }
        let outer_deadline = (Instant::now() + Duration::from_millis(700)).min(construction_deadline);
        let special_deadline = (outer_deadline + Duration::from_millis(350)).min(construction_deadline);
        let (mut candidate, layers, done, special_t) = build_layered_one_special(
            &board, reserved, outer_deadline, special_deadline,
        );
        polish(&board, &mut candidate, (Instant::now() + Duration::from_millis(80)).min(deadline));
        let stats = board.evaluate(&candidate);
        eprintln!("layered reserved={} layers={:?} special_done={} special_t={} k={} t={} m={} score={}",
            reserved, layers, done, special_t,
            stats.matched, stats.total, stats.moves, stats.score);
        if stats.score > best_stats.score && board.tester_safe(&candidate) {
            best_stats = stats;
            best_orientation = candidate;
        }
    }

    for &width in &WIDTHS {
        if Instant::now() >= construction_deadline { break; }
        let outer_deadline = (Instant::now() + Duration::from_millis(450)).min(construction_deadline);
        let (outer, _) = build_outer(&board, width, &[], outer_deadline);
        let outer_stats = board.evaluate(&outer);
        if outer_stats.score > best_stats.score && board.tester_safe(&outer) {
            best_stats = outer_stats;
            best_orientation = outer;
        }
        for count in 1..=MAX_SPECIAL {
            if Instant::now() >= construction_deadline { break; }
            let chosen = &specials[..count.min(specials.len())];
            let gate_deadline = (Instant::now() + Duration::from_millis(180)).min(construction_deadline);
            let (gated_outer, gated_fixed) = build_outer(&board, width, chosen, gate_deadline);
            let special_deadline = (Instant::now() + Duration::from_millis(260)).min(construction_deadline);
            let (mut candidate, special_t, done) = build_with_specials(
                &board, &gated_outer, &gated_fixed, width, chosen, special_deadline,
            );
            polish(&board, &mut candidate,
                (Instant::now() + Duration::from_millis(30)).min(construction_deadline));
            let stats = board.evaluate(&candidate);
            eprintln!("legacy width={} reserved={} done={} special_t={} k={} t={} m={} score={}",
                width, count, done, special_t, stats.matched, stats.total, stats.moves, stats.score);
            if stats.score > best_stats.score && board.tester_safe(&candidate) {
                best_stats = stats;
                best_orientation = candidate;
            }
        }
    }

    if Instant::now() < deadline {
        polish(&board, &mut best_orientation, (Instant::now() + Duration::from_millis(100)).min(deadline));
        search_rotations(&board, &mut best_orientation, Instant::now(), deadline);
        best_stats = board.evaluate(&best_orientation);
    }
    eprintln!("final k={} t={} m={} score={} elapsed_ms={}", best_stats.matched,
        best_stats.total, best_stats.moves, best_stats.score, start.elapsed().as_millis());

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
