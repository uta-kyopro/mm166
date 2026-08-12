#![allow(non_snake_case, unused_variables)]

use std::collections::{HashSet, VecDeque};
use std::io::{self, BufWriter, Write};
use std::str::FromStr;
use std::time::{Duration, Instant};

const BEAM_WIDTH: usize = 32;
const DOMAIN_BEAM_WIDTH: usize = 32;
const REPAIR_PATH_BEAM_WIDTH: usize = 32;
// Leave process startup/output headroom under the 10 second contest limit.
const SOLVER_TIME_LIMIT_MS: u64 = 9_000;
const ENABLE_COMPONENT_REPAIR: bool = true;
const RUIN_CANDIDATES: usize = 4;
const RECREATE_STEPS: usize = 6;
const RECREATE_CANDIDATES: usize = 8;
const PATH_BEAM_WIDTH: usize = 512;
const PATH_CANDIDATES: usize = 64;
const GOAL_POOL_SIZE: usize = PATH_CANDIDATES * 16;
const MAX_BONUS: usize = 10;
const INF_ROT: i16 = 30_000;

struct Scanner {
    stdin: io::Stdin,
    tokens: VecDeque<String>,
}

impl Scanner {
    fn new() -> Scanner {
        Scanner {
            stdin: io::stdin(),
            tokens: VecDeque::new(),
        }
    }

    fn next<T: FromStr>(&mut self) -> T {
        loop {
            if let Some(tok) = self.tokens.pop_front() {
                match tok.parse() {
                    Ok(v) => return v,
                    Err(_) => panic!("cannot parse token: {}", tok),
                }
            }
            let mut line = String::new();
            if self.stdin.read_line(&mut line).expect("read error") == 0 {
                panic!("unexpected end of input");
            }
            self.tokens
                .extend(line.split_whitespace().map(String::from));
        }
    }
}

// Edge directions, clockwise around a tile:
// 0=NW, 1=NE, 2=E, 3=SE, 4=SW, 5=W.
const DR: [isize; 6] = [-1, -1, 0, 1, 1, 0];
const DC: [isize; 6] = [0, 1, 1, 0, -1, -1];

fn opposite(d: usize) -> usize {
    (d + 3) % 6
}

// Orientation 0 connects (NW,NE), (E,SW), (SE,W).
// Increasing orientation by 1 is one clockwise rotation.
fn paired_dir(orientation: u8, enter: usize) -> usize {
    const BASE_PAIR: [usize; 6] = [1, 0, 4, 5, 2, 3];
    let o = orientation as usize;
    let base_enter = (enter + 6 - o) % 6;
    (BASE_PAIR[base_enter] + o) % 6
}

fn rotation_cost(from: u8, to: u8) -> i32 {
    let cw = (to as i32 - from as i32 + 6) % 6;
    let ccw = (from as i32 - to as i32 + 6) % 6;
    cw.min(ccw)
}

fn append_rotation_moves(
    moves: &mut Vec<(usize, usize, i32)>,
    r: usize,
    c: usize,
    from: u8,
    to: u8,
) {
    let cw = (to as i32 - from as i32 + 6) % 6;
    let ccw = (from as i32 - to as i32 + 6) % 6;
    if cw <= ccw {
        for _ in 0..cw {
            moves.push((r, c, 1));
        }
    } else {
        for _ in 0..ccw {
            moves.push((r, c, -1));
        }
    }
}

fn valid_cell(grid: &[i32], W: usize, r: isize, c: isize) -> bool {
    if r < 0 || c < 0 || r >= W as isize || c >= W as isize {
        return false;
    }
    grid[r as usize * W + c as usize] >= 0
}

// Exact exit order from the statement:
// clockwise, with exit 0 at the west edge of the top-left tile.
fn build_exits(N: usize, grid: &[i32]) -> (Vec<(usize, usize)>, Vec<i32>) {
    let W = 2 * N - 1;
    let mut exits: Vec<(usize, usize)> = Vec::new(); // (cell, edge_dir)

    let mut push_exit = |r: usize, c: usize, d: usize| {
        let cell = r * W + c;
        debug_assert!(grid[cell] >= 0);
        let nr = r as isize + DR[d];
        let nc = c as isize + DC[d];
        debug_assert!(!valid_cell(grid, W, nr, nc));
        exits.push((cell, d));
    };

    // Top boundary: left corner -> right corner.
    for c in (N - 1)..W {
        if c == N - 1 {
            push_exit(0, c, 5);
        }
        push_exit(0, c, 0);
        push_exit(0, c, 1);
        if c == W - 1 {
            push_exit(0, c, 2);
        }
    }

    // Upper-right slope.
    for r in 1..(N - 1) {
        push_exit(r, W - 1, 1);
        push_exit(r, W - 1, 2);
    }

    // Right corner.
    push_exit(N - 1, W - 1, 1);
    push_exit(N - 1, W - 1, 2);
    push_exit(N - 1, W - 1, 3);

    // Lower-right slope.
    for r in N..(W - 1) {
        let c = W + N - 2 - r;
        push_exit(r, c, 2);
        push_exit(r, c, 3);
    }

    // Bottom boundary: right corner -> left corner.
    for c in (0..N).rev() {
        if c == N - 1 {
            push_exit(W - 1, c, 2);
        }
        push_exit(W - 1, c, 3);
        push_exit(W - 1, c, 4);
        if c == 0 {
            push_exit(W - 1, c, 5);
        }
    }

    // Lower-left slope.
    for r in (N..(W - 1)).rev() {
        push_exit(r, 0, 4);
        push_exit(r, 0, 5);
    }

    // Left corner.
    push_exit(N - 1, 0, 4);
    push_exit(N - 1, 0, 5);
    push_exit(N - 1, 0, 0);

    // Upper-left slope.
    for r in (1..(N - 1)).rev() {
        let c = N - 1 - r;
        push_exit(r, c, 5);
        push_exit(r, c, 0);
    }

    debug_assert_eq!(exits.len(), 6 * (2 * N - 1));

    let mut exit_id = vec![-1i32; W * W * 6];
    for (id, &(cell, d)) in exits.iter().enumerate() {
        exit_id[cell * 6 + d] = id as i32;
    }
    (exits, exit_id)
}

fn can_connect(cell: usize, enter: usize, out: usize, orientation: &[u8], fixed: &[bool]) -> bool {
    if fixed[cell] {
        paired_dir(orientation[cell], enter) == out
    } else {
        (0u8..6).any(|o| paired_dir(o, enter) == out)
    }
}

// Optimistic reverse BFS from the target exit.
// Fixed tiles keep their orientation; unfixed tiles may take any orientation.
// Beam-local used tiles are ignored, therefore dist==-1 is a safe prune while
// dist>=0 only means "possibly reachable".
//
// dist[(cell, enter)] = minimum number of tiles from that state to the target,
// including the current tile. -1 means definitely unreachable.
fn build_reverse_dist(
    W: usize,
    grid: &[i32],
    orientation: &[u8],
    fixed: &[bool],
    exits: &[(usize, usize)],
    target_exit: usize,
) -> Vec<i16> {
    let states = W * W * 6;
    let mut dist = vec![-1i16; states];
    let mut q = VecDeque::new();
    let (target_cell, target_edge) = exits[target_exit];

    for enter in 0..6 {
        if can_connect(target_cell, enter, target_edge, orientation, fixed) {
            let s = target_cell * 6 + enter;
            dist[s] = 1;
            q.push_back(s);
        }
    }

    while let Some(state) = q.pop_front() {
        let cell = state / 6;
        let enter = state % 6;
        let r = cell / W;
        let c = cell % W;

        // Current state entered through `enter`, so its predecessor is across
        // exactly that edge.
        let pr = r as isize + DR[enter];
        let pc = c as isize + DC[enter];
        if !valid_cell(grid, W, pr, pc) {
            continue;
        }

        let pcell = pr as usize * W + pc as usize;
        let required_out = opposite(enter);
        for penter in 0..6 {
            if !can_connect(pcell, penter, required_out, orientation, fixed) {
                continue;
            }
            let ps = pcell * 6 + penter;
            if dist[ps] >= 0 {
                continue;
            }
            dist[ps] = dist[state] + 1;
            q.push_back(ps);
        }
    }

    dist
}

#[derive(Clone)]
struct ReverseEstimate {
    // Shortest remaining path length (number of tiles, including this state).
    dist: Vec<i16>,
    // For each state and each exact number of bonus tiles on a shortest
    // continuation, the minimum number of rotations required.
    // INF_ROT means no shortest continuation with that bonus count exists.
    min_rot_by_bonus: Vec<[i16; MAX_BONUS + 1]>,
}

// First compute optimistic shortest distance by reverse BFS.  Then, only on
// edges that decrease that distance by exactly one, run a DP that keeps the
// minimum rotation count for every possible remaining bonus count.
//
// This gives a concrete estimate of "if we stop detouring now and connect to
// the target by a shortest route, how long will the final path be, how many
// more rotations are needed, and how many more bonus tiles can be collected?"
fn build_reverse_estimate(
    W: usize,
    grid: &[i32],
    orientation: &[u8],
    rotation_reference: &[u8],
    fixed: &[bool],
    bonus: &[bool],
    exits: &[(usize, usize)],
    target_exit: usize,
) -> ReverseEstimate {
    let dist = build_reverse_dist(W, grid, orientation, fixed, exits, target_exit);
    let states = W * W * 6;
    let mut min_rot_by_bonus = vec![[INF_ROT; MAX_BONUS + 1]; states];
    let max_dist = dist.iter().copied().max().unwrap_or(-1).max(0) as usize;
    let (target_cell, target_edge) = exits[target_exit];

    // Bucket states once so the DP touches each reachable state only once.
    let mut by_dist = vec![Vec::<usize>::new(); max_dist + 1];
    for state in 0..states {
        if dist[state] > 0 {
            by_dist[dist[state] as usize].push(state);
        }
    }

    // dist=1 states can leave the board directly through the target exit.
    // Larger distances depend only on dist-1, so ascending distance is a DAG DP.
    for d in 1..=max_dist {
        for &state in &by_dist[d] {
            let cell = state / 6;
            let enter = state % 6;
            let r = cell / W;
            let c = cell % W;
            let add_bonus = usize::from(bonus[cell]);

            let first_o = if fixed[cell] { orientation[cell] } else { 0 };
            let last_o = if fixed[cell] { orientation[cell] } else { 5 };

            for o in first_o..=last_o {
                let add_rot = if fixed[cell] {
                    0
                } else {
                    rotation_cost(rotation_reference[cell], o)
                } as i16;
                let out_dir = paired_dir(o, enter);
                let nr = r as isize + DR[out_dir];
                let nc = c as isize + DC[out_dir];

                if d == 1 {
                    if cell == target_cell && out_dir == target_edge && !valid_cell(grid, W, nr, nc)
                    {
                        let slot = &mut min_rot_by_bonus[state][add_bonus];
                        *slot = (*slot).min(add_rot);
                    }
                    continue;
                }

                if !valid_cell(grid, W, nr, nc) {
                    continue;
                }
                let ncell = nr as usize * W + nc as usize;
                let nstate = ncell * 6 + opposite(out_dir);
                if dist[nstate] != d as i16 - 1 {
                    continue;
                }

                for future_bonus in 0..=MAX_BONUS - add_bonus {
                    let future_rot = min_rot_by_bonus[nstate][future_bonus];
                    if future_rot == INF_ROT {
                        continue;
                    }
                    let total_bonus = future_bonus + add_bonus;
                    let total_rot = add_rot + future_rot;
                    let slot = &mut min_rot_by_bonus[state][total_bonus];
                    *slot = (*slot).min(total_rot);
                }
            }
        }
    }

    ReverseEstimate {
        dist,
        min_rot_by_bonus,
    }
}

#[derive(Clone, Copy)]
struct ProjectedCompletion {
    score: i32,
    length: usize,
    bonuses: usize,
    rotations: i32,
}

fn estimate_shortest_completion(
    M: i32,
    current_len: usize,
    current_bonuses: usize,
    current_rotations: i32,
    state: usize,
    estimate: &ReverseEstimate,
) -> Option<ProjectedCompletion> {
    let rd = estimate.dist[state];
    if rd < 0 {
        return None;
    }

    let final_len = current_len + rd as usize;
    let mut best: Option<ProjectedCompletion> = None;

    for future_bonus in 0..=MAX_BONUS {
        let future_rot = estimate.min_rot_by_bonus[state][future_bonus];
        if future_rot == INF_ROT {
            continue;
        }

        let final_bonuses = current_bonuses + future_bonus;
        let final_rotations = current_rotations + future_rot as i32;
        let score = final_len as i32 * (final_bonuses as i32 + 1) - M * final_rotations;
        let candidate = ProjectedCompletion {
            score,
            length: final_len,
            bonuses: final_bonuses,
            rotations: final_rotations,
        };

        let better = match best {
            None => true,
            Some(old) => {
                candidate.score > old.score
                    || (candidate.score == old.score && candidate.length > old.length)
                    || (candidate.score == old.score
                        && candidate.length == old.length
                        && candidate.bonuses > old.bonuses)
                    || (candidate.score == old.score
                        && candidate.length == old.length
                        && candidate.bonuses == old.bonuses
                        && candidate.rotations < old.rotations)
            }
        };
        if better {
            best = Some(candidate);
        }
    }

    best
}

#[derive(Clone, Copy)]
struct PathNode {
    cell: usize,
    enter: u8,
    out: u8,
    orientation: u8,
    first_assignment: bool,
    parent: Option<usize>,
    depth: usize,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
struct PathStep {
    cell: usize,
    enter: u8,
    out: u8,
    orientation: u8,
}

#[derive(Clone, Copy)]
struct BeamItem {
    state: usize,
    rotations: i32,
    length: usize,
    bonuses: usize,
    tail: Option<usize>,
}

#[derive(Clone, Copy)]
struct Candidate {
    state: usize,
    rotations: i32,
    length: usize,
    bonuses: usize,
    parent_tail: Option<usize>,
    path_cell: usize,
    path_enter: u8,
    path_out: u8,
    path_orientation: u8,
    first_assignment: bool,
    projected_length: usize,
    projected_bonuses: usize,
    projected_rotations: i32,
    beam_score: i32,
}

// One mutable board is shared by all Beam states.  Moving between two leaves
// applies/undoes only the PathNodes between them, following the differential
// tree-state Beam Search pattern.
struct DifferentialState {
    local_orientation: Vec<i8>,
    visit_count: Vec<u8>,
    used_edge: Vec<bool>,
}

impl DifferentialState {
    fn new(cells: usize) -> Self {
        Self {
            local_orientation: vec![-1; cells],
            visit_count: vec![0; cells],
            used_edge: vec![false; cells * 6],
        }
    }

    fn apply(&mut self, node: PathNode) {
        if node.first_assignment {
            debug_assert_eq!(self.local_orientation[node.cell], -1);
            self.local_orientation[node.cell] = node.orientation as i8;
        } else if self.local_orientation[node.cell] >= 0 {
            debug_assert_eq!(self.local_orientation[node.cell], node.orientation as i8);
        }
        debug_assert!(!self.used_edge[node.cell * 6 + node.enter as usize]);
        debug_assert!(!self.used_edge[node.cell * 6 + node.out as usize]);
        self.used_edge[node.cell * 6 + node.enter as usize] = true;
        self.used_edge[node.cell * 6 + node.out as usize] = true;
        self.visit_count[node.cell] += 1;
    }

    fn undo(&mut self, node: PathNode) {
        self.visit_count[node.cell] -= 1;
        self.used_edge[node.cell * 6 + node.enter as usize] = false;
        self.used_edge[node.cell * 6 + node.out as usize] = false;
        if node.first_assignment {
            debug_assert_eq!(self.visit_count[node.cell], 0);
            self.local_orientation[node.cell] = -1;
        }
    }

    fn segment_used(&self, cell: usize, enter: usize, out: usize) -> bool {
        self.used_edge[cell * 6 + enter] || self.used_edge[cell * 6 + out]
    }
}

fn node_depth(tail: Option<usize>, arena: &[PathNode]) -> usize {
    tail.map_or(0, |idx| arena[idx].depth)
}

fn switch_differential_state(
    current: &mut Option<usize>,
    target: Option<usize>,
    arena: &[PathNode],
    state: &mut DifferentialState,
) {
    if *current == target {
        return;
    }

    let mut a = *current;
    let mut b = target;
    let mut da = node_depth(a, arena);
    let mut db = node_depth(b, arena);
    let mut apply_nodes = Vec::new();

    while da > db {
        let idx = a.unwrap();
        state.undo(arena[idx]);
        a = arena[idx].parent;
        da -= 1;
    }
    while db > da {
        let idx = b.unwrap();
        apply_nodes.push(idx);
        b = arena[idx].parent;
        db -= 1;
    }
    while a != b {
        let ai = a.unwrap();
        state.undo(arena[ai]);
        a = arena[ai].parent;

        let bi = b.unwrap();
        apply_nodes.push(bi);
        b = arena[bi].parent;
    }
    for &idx in apply_nodes.iter().rev() {
        state.apply(arena[idx]);
    }
    *current = target;
}

#[derive(Clone, Copy)]
struct Goal {
    score: i32,
    length: usize,
    bonuses: usize,
    rotations: i32,
    tail: usize,
}

fn goal_is_better(
    score: i32,
    length: usize,
    bonuses: usize,
    rotations: i32,
    best: Option<Goal>,
) -> bool {
    match best {
        None => true,
        Some(g) => {
            score > g.score
                || (score == g.score && bonuses > g.bonuses)
                || (score == g.score && bonuses == g.bonuses && length > g.length)
                || (score == g.score
                    && bonuses == g.bonuses
                    && length == g.length
                    && rotations < g.rotations)
        }
    }
}

fn find_path_candidates(
    W: usize,
    M: i32,
    grid: &[i32],
    orientation: &[u8],
    rotation_reference: &[u8],
    fixed: &[bool],
    base_domains: Option<&[u8]>,
    base_used_sides: Option<&[u8]>,
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    source_exit: usize,
    target_exit: usize,
    valid_cells: usize,
    beam_width: usize,
    deadline: Option<Instant>,
) -> Vec<Vec<PathStep>> {
    let (start_cell, start_enter) = exits[source_exit];
    let start = start_cell * 6 + start_enter;
    let reverse = build_reverse_estimate(
        W,
        grid,
        orientation,
        rotation_reference,
        fixed,
        bonus,
        exits,
        target_exit,
    );

    if reverse.dist[start] < 0 {
        return Vec::new();
    }

    let mut arena: Vec<PathNode> = Vec::with_capacity(beam_width * valid_cells.min(256));
    let mut beam = vec![BeamItem {
        state: start,
        rotations: 0,
        length: 0,
        bonuses: 0,
        tail: None,
    }];
    let mut goals: Vec<Goal> = Vec::new();
    let mut differential = DifferentialState::new(grid.len());
    let mut current_tail = None;
    let max_segments = valid_cells * 3;

    // A tile has three independent line segments.  Re-entering a tile through
    // another segment is legal, but traversing an already-used segment closes a
    // loop, so a non-looping path contains at most 3 * valid_cells segments.
    for depth in 0..max_segments {
        if deadline.is_some_and(|limit| Instant::now() >= limit) {
            break;
        }
        let mut candidates: Vec<Candidate> = Vec::with_capacity(beam.len() * 6);

        // Nearby arena indices often share a long prefix.  This ordering does not
        // affect Beam selection, but reduces apply/revert work while enumerating.
        beam.sort_unstable_by_key(|item| item.tail.unwrap_or(usize::MAX));
        for item in &beam {
            if deadline.is_some_and(|limit| Instant::now() >= limit) {
                break;
            }
            switch_differential_state(&mut current_tail, item.tail, &arena, &mut differential);

            let cell = item.state / 6;
            let enter = item.state % 6;
            let r = cell / W;
            let c = cell % W;

            let local_o = differential.local_orientation[cell];
            let mut allowed = base_domains.map_or(0x3f, |domains| domains[cell]);
            if fixed[cell] {
                allowed &= 1 << orientation[cell];
            }
            if local_o >= 0 {
                allowed &= 1 << local_o as u8;
            }

            for o in 0u8..6 {
                if allowed & (1 << o) == 0 {
                    continue;
                }
                let first_assignment = !fixed[cell] && local_o < 0;
                let add_rot = if first_assignment {
                    rotation_cost(rotation_reference[cell], o)
                } else {
                    0
                };
                let new_rot = item.rotations + add_rot;
                let new_len = item.length + 1;
                let out_dir = paired_dir(o, enter);
                if differential.segment_used(cell, enter, out_dir) {
                    continue;
                }
                let side_mask = (1u8 << enter) | (1u8 << out_dir);
                if base_used_sides.map_or(false, |used| used[cell] & side_mask != 0) {
                    continue;
                }
                let new_bonuses =
                    item.bonuses + usize::from(bonus[cell] && differential.visit_count[cell] == 0);
                let nr = r as isize + DR[out_dir];
                let nc = c as isize + DC[out_dir];

                if !valid_cell(grid, W, nr, nc) {
                    if exit_id[cell * 6 + out_dir] == target_exit as i32 {
                        // For one fixed pair, choosing the path that maximizes
                        // path_score - move_penalty is the natural local objective.
                        let path_score = new_len as i32 * (new_bonuses as i32 + 1);
                        let score = path_score - M * new_rot;

                        let tail = arena.len();
                        arena.push(PathNode {
                            cell,
                            enter: enter as u8,
                            out: out_dir as u8,
                            orientation: o,
                            first_assignment,
                            parent: item.tail,
                            depth: new_len,
                        });
                        goals.push(Goal {
                            score,
                            length: new_len,
                            bonuses: new_bonuses,
                            rotations: new_rot,
                            tail,
                        });
                        if goals.len() > GOAL_POOL_SIZE * 2 {
                            goals.sort_unstable_by(|a, b| {
                                b.score
                                    .cmp(&a.score)
                                    .then_with(|| a.rotations.cmp(&b.rotations))
                                    .then_with(|| a.length.cmp(&b.length))
                            });
                            goals.truncate(GOAL_POOL_SIZE);
                        }
                    }
                    continue;
                }

                let ncell = nr as usize * W + nc as usize;
                let nstate = ncell * 6 + opposite(out_dir);
                let rd = reverse.dist[nstate];
                if rd < 0 {
                    continue; // definitely cannot reach target
                }

                // Even the optimistic shortest continuation cannot fit before all
                // tile segments have been exhausted.
                if new_len + rd as usize > max_segments {
                    continue;
                }

                // Evaluate this branch by asking: if we stop detouring here and take a
                // shortest route to the target, what final path score would we get?
                // The reverse DP estimates both future rotations and future bonus tiles
                // on such shortest completions.  This makes path length part of the
                // score immediately instead of minimizing rotations lexicographically.
                let Some(projected) = estimate_shortest_completion(
                    M,
                    new_len,
                    new_bonuses,
                    new_rot,
                    nstate,
                    &reverse,
                ) else {
                    continue;
                };

                candidates.push(Candidate {
                    state: nstate,
                    rotations: new_rot,
                    length: new_len,
                    bonuses: new_bonuses,
                    parent_tail: item.tail,
                    path_cell: cell,
                    path_enter: enter as u8,
                    path_out: out_dir as u8,
                    path_orientation: o,
                    first_assignment,
                    projected_length: projected.length,
                    projected_bonuses: projected.bonuses,
                    projected_rotations: projected.rotations,
                    beam_score: projected.score,
                });
            }
        }

        if candidates.is_empty() {
            break;
        }

        candidates.sort_unstable_by(|a, b| {
            b.beam_score
                .cmp(&a.beam_score)
                .then_with(|| b.projected_length.cmp(&a.projected_length))
                .then_with(|| b.projected_bonuses.cmp(&a.projected_bonuses))
                .then_with(|| a.projected_rotations.cmp(&b.projected_rotations))
                .then_with(|| b.bonuses.cmp(&a.bonuses))
                .then_with(|| a.rotations.cmp(&b.rotations))
                .then_with(|| a.state.cmp(&b.state))
        });
        if candidates.len() > beam_width {
            candidates.truncate(beam_width);
        }

        let mut next_beam = Vec::with_capacity(candidates.len());
        for cand in candidates {
            let tail = arena.len();
            arena.push(PathNode {
                cell: cand.path_cell,
                enter: cand.path_enter,
                out: cand.path_out,
                orientation: cand.path_orientation,
                first_assignment: cand.first_assignment,
                parent: cand.parent_tail,
                depth: cand.length,
            });
            next_beam.push(BeamItem {
                state: cand.state,
                rotations: cand.rotations,
                length: cand.length,
                bonuses: cand.bonuses,
                tail: Some(tail),
            });
        }
        beam = next_beam;

        let shortest = reverse.dist[start] as usize;
        if goals.len() >= GOAL_POOL_SIZE && depth + 1 >= shortest + 24 {
            break;
        }
    }

    let mut ordered = goals.clone();
    ordered.sort_unstable_by(|a, b| {
        a.rotations
            .cmp(&b.rotations)
            .then_with(|| a.length.cmp(&b.length))
            .then_with(|| b.score.cmp(&a.score))
    });
    goals.sort_unstable_by(|a, b| {
        b.score
            .cmp(&a.score)
            .then_with(|| a.rotations.cmp(&b.rotations))
            .then_with(|| a.length.cmp(&b.length))
    });

    // Mix low-conflict/low-move candidates with locally high-scoring ones.
    let mut mixed = Vec::with_capacity(ordered.len() + goals.len());
    for i in 0..ordered.len().max(goals.len()) {
        if i < ordered.len() {
            mixed.push(ordered[i]);
        }
        if i < goals.len() {
            mixed.push(goals[i]);
        }
    }

    let mut seen = HashSet::new();
    let mut paths = Vec::new();
    for goal in mixed {
        let mut rev_path = Vec::with_capacity(goal.length);
        let mut tail = Some(goal.tail);
        while let Some(idx) = tail {
            let node = arena[idx];
            rev_path.push(PathStep {
                cell: node.cell,
                enter: node.enter,
                out: node.out,
                orientation: node.orientation,
            });
            tail = node.parent;
        }
        rev_path.reverse();
        let geometry: Vec<(usize, u8, u8)> = rev_path
            .iter()
            .map(|s| (s.cell, s.enter.min(s.out), s.enter.max(s.out)))
            .collect();
        if seen.insert(geometry) {
            paths.push(rev_path);
            if paths.len() >= PATH_CANDIDATES {
                break;
            }
        }
    }
    paths
}

fn find_path_beam(
    W: usize,
    M: i32,
    grid: &[i32],
    orientation: &[u8],
    fixed: &[bool],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    source_exit: usize,
    target_exit: usize,
    valid_cells: usize,
) -> Option<Vec<(usize, u8)>> {
    find_path_candidates(
        W,
        M,
        grid,
        orientation,
        orientation,
        fixed,
        None,
        None,
        bonus,
        exits,
        exit_id,
        source_exit,
        target_exit,
        valid_cells,
        BEAM_WIDTH,
        None,
    )
    .into_iter()
    .max_by_key(|path| {
        let mut seen = vec![false; grid.len()];
        let mut rotations = 0i32;
        let mut bonuses = 0usize;
        for step in path {
            if !seen[step.cell] {
                seen[step.cell] = true;
                bonuses += usize::from(bonus[step.cell]);
                if !fixed[step.cell] {
                    rotations += rotation_cost(orientation[step.cell], step.orientation);
                }
            }
        }
        path.len() as i32 * (bonuses as i32 + 1) - M * rotations
    })
    .map(|path| {
        path.into_iter()
            .map(|step| (step.cell, step.orientation))
            .collect()
    })
}

#[derive(Clone)]
struct TileRequirement {
    cell: usize,
    domain_mask: u8,
    used_sides: u8,
}

#[derive(Clone)]
struct RouteCandidate {
    path: Vec<PathStep>,
    requirements: Vec<TileRequirement>,
    length: usize,
    bonuses: usize,
}

fn connection_mask(enter: usize, out: usize) -> u8 {
    let mut mask = 0u8;
    for o in 0u8..6 {
        if paired_dir(o, enter) == out {
            mask |= 1 << o;
        }
    }
    mask
}

fn make_route_candidate(
    path: Vec<PathStep>,
    bonus: &[bool],
    cells: usize,
) -> Option<RouteCandidate> {
    let mut masks = vec![0x3fu8; cells];
    let mut sides = vec![0u8; cells];
    let mut touched = Vec::new();
    let mut seen_tile = vec![false; cells];
    let mut bonuses = 0usize;

    for step in &path {
        let cell = step.cell;
        if !seen_tile[cell] {
            seen_tile[cell] = true;
            touched.push(cell);
            bonuses += usize::from(bonus[cell]);
        }
        let required = connection_mask(step.enter as usize, step.out as usize);
        masks[cell] &= required;
        let used = (1u8 << step.enter) | (1u8 << step.out);
        if masks[cell] == 0 || sides[cell] & used != 0 {
            return None;
        }
        sides[cell] |= used;
    }

    let requirements = touched
        .into_iter()
        .map(|cell| TileRequirement {
            cell,
            domain_mask: masks[cell],
            used_sides: sides[cell],
        })
        .collect();
    Some(RouteCandidate {
        length: path.len(),
        path,
        requirements,
        bonuses,
    })
}

fn candidate_compatible(candidate: &RouteCandidate, domains: &[u8], used_sides: &[u8]) -> bool {
    candidate.requirements.iter().all(|req| {
        domains[req.cell] & req.domain_mask != 0 && used_sides[req.cell] & req.used_sides == 0
    })
}

fn domain_rotation_cost(initial: u8, mask: u8) -> i32 {
    (0u8..6)
        .filter(|&o| mask & (1 << o) != 0)
        .map(|o| rotation_cost(initial, o))
        .min()
        .unwrap_or(i32::MAX / 4)
}

struct UnionFind {
    parent: Vec<usize>,
    size: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n],
        }
    }

    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    fn union(&mut self, a: usize, b: usize) {
        let mut a = self.find(a);
        let mut b = self.find(b);
        if a == b {
            return;
        }
        if self.size[a] < self.size[b] {
            std::mem::swap(&mut a, &mut b);
        }
        self.parent[b] = a;
        self.size[a] += self.size[b];
    }
}

#[derive(Clone, Copy)]
struct DomainMetrics {
    singleton: usize,
    ambiguity: usize,
    matched: usize,
    move_lower_bound: i32,
}

#[derive(Clone)]
struct DomainBeamState {
    domains: Vec<u8>,
    metrics: DomainMetrics,
}

fn make_mate(exit_count: usize, matches: &[[usize; 2]]) -> Vec<usize> {
    let mut mate = vec![usize::MAX; exit_count];
    for pair in matches {
        mate[pair[0]] = pair[1];
        mate[pair[1]] = pair[0];
    }
    mate
}

fn add_neighbor_edges(uf: &mut UnionFind, W: usize, grid: &[i32]) {
    for cell in 0..grid.len() {
        if grid[cell] < 0 {
            continue;
        }
        let r = cell / W;
        let c = cell % W;
        for d in 0..6 {
            let nr = r as isize + DR[d];
            let nc = c as isize + DC[d];
            if valid_cell(grid, W, nr, nc) {
                let ncell = nr as usize * W + nc as usize;
                if cell < ncell {
                    uf.union(cell * 6 + d, ncell * 6 + opposite(d));
                }
            }
        }
    }
}

fn forced_components(
    W: usize,
    grid: &[i32],
    domains: &[u8],
    exits: &[(usize, usize)],
    mate: &[usize],
) -> Option<(Vec<usize>, Vec<Vec<usize>>, usize)> {
    let ports = grid.len() * 6;
    let mut uf = UnionFind::new(ports);
    add_neighbor_edges(&mut uf, W, grid);

    for cell in 0..grid.len() {
        let mask = domains[cell];
        if grid[cell] < 0 {
            continue;
        }
        if mask == 0 {
            return None;
        }
        for enter in 0..6 {
            let mut common_out = None;
            let mut forced = true;
            for o in 0u8..6 {
                if mask & (1 << o) == 0 {
                    continue;
                }
                let out = paired_dir(o, enter);
                if let Some(previous) = common_out {
                    if previous != out {
                        forced = false;
                        break;
                    }
                } else {
                    common_out = Some(out);
                }
            }
            if forced {
                uf.union(cell * 6 + enter, cell * 6 + common_out.unwrap());
            }
        }
    }

    let mut roots = vec![0usize; ports];
    for port in 0..ports {
        roots[port] = uf.find(port);
    }
    let mut root_exits = vec![Vec::new(); ports];
    for (exit, &(cell, side)) in exits.iter().enumerate() {
        root_exits[roots[cell * 6 + side]].push(exit);
    }

    let mut matched = 0usize;
    for connected_exits in &root_exits {
        match connected_exits.len() {
            0 | 1 => {}
            2 if mate[connected_exits[0]] == connected_exits[1] => matched += 1,
            _ => return None,
        }
    }
    Some((roots, root_exits, matched))
}

fn assignments_valid(
    assignments: &[(usize, u8)],
    roots: &[usize],
    root_exits: &[Vec<usize>],
    mate: &[usize],
) -> bool {
    // A local assignment cannot create a wrong exit pair unless at least two
    // exits already reach one of its ports.  Almost all inner-board patches
    // satisfy this shortcut, especially early in the outside-in search.
    let mut touched_roots = Vec::new();
    let mut touched_exit_count = 0usize;
    for &(cell, _) in assignments {
        for side in 0..6 {
            let root = roots[cell * 6 + side];
            if !touched_roots.contains(&root) {
                touched_roots.push(root);
                touched_exit_count += root_exits[root].len();
            }
        }
    }
    if touched_exit_count < 2 {
        return true;
    }

    let count = assignments.len() * 6;
    let mut base_roots = vec![0usize; count];
    for (i, &(cell, _)) in assignments.iter().enumerate() {
        for side in 0..6 {
            base_roots[i * 6 + side] = roots[cell * 6 + side];
        }
    }

    let mut local = UnionFind::new(count);
    for a in 0..count {
        for b in 0..a {
            if base_roots[a] == base_roots[b] {
                local.union(a, b);
            }
        }
    }
    for (i, &(_, orientation)) in assignments.iter().enumerate() {
        for enter in 0..6 {
            local.union(i * 6 + enter, i * 6 + paired_dir(orientation, enter));
        }
    }

    for group in 0..count {
        if local.find(group) != group {
            continue;
        }
        let mut distinct_roots = Vec::new();
        for port in 0..count {
            if local.find(port) == group && !distinct_roots.contains(&base_roots[port]) {
                distinct_roots.push(base_roots[port]);
            }
        }
        let mut connected_exits = Vec::new();
        for root in distinct_roots {
            connected_exits.extend_from_slice(&root_exits[root]);
        }
        match connected_exits.len() {
            0 | 1 => {}
            2 if mate[connected_exits[0]] == connected_exits[1] => {}
            _ => return false,
        }
    }
    true
}

fn patch_has_multiple_exits(cells: &[usize], roots: &[usize], root_exits: &[Vec<usize>]) -> bool {
    let mut touched_roots = [usize::MAX; 12];
    let mut root_count = 0usize;
    let mut exit_count = 0usize;
    for &cell in cells {
        for side in 0..6 {
            let root = roots[cell * 6 + side];
            if !touched_roots[..root_count].contains(&root) {
                touched_roots[root_count] = root;
                root_count += 1;
                exit_count += root_exits[root].len();
                if exit_count >= 2 {
                    return true;
                }
            }
        }
    }
    false
}

fn optimistic_pairs_reachable(
    W: usize,
    grid: &[i32],
    domains: &[u8],
    exits: &[(usize, usize)],
    mate: &[usize],
) -> bool {
    let mut uf = UnionFind::new(grid.len() * 6);
    add_neighbor_edges(&mut uf, W, grid);
    for cell in 0..grid.len() {
        if grid[cell] < 0 {
            continue;
        }
        for o in 0u8..6 {
            if domains[cell] & (1 << o) == 0 {
                continue;
            }
            for enter in 0..6 {
                uf.union(cell * 6 + enter, cell * 6 + paired_dir(o, enter));
            }
        }
    }
    for exit in 0..exits.len() {
        if exit > mate[exit] {
            continue;
        }
        let (cell_a, side_a) = exits[exit];
        let (cell_b, side_b) = exits[mate[exit]];
        if uf.find(cell_a * 6 + side_a) != uf.find(cell_b * 6 + side_b) {
            return false;
        }
    }
    true
}

fn propagate_domains(
    W: usize,
    grid: &[i32],
    initial: &[u8],
    exits: &[(usize, usize)],
    mate: &[usize],
    domains: &mut [u8],
) -> Option<DomainMetrics> {
    loop {
        let (roots, root_exits, _) = forced_components(W, grid, domains, exits, mate)?;
        let mut next = domains.to_vec();

        // Unary filtering relative to all currently forced path components.
        for cell in 0..grid.len() {
            if grid[cell] < 0 {
                continue;
            }
            if !patch_has_multiple_exits(&[cell], &roots, &root_exits) {
                continue;
            }
            let mut supported = 0u8;
            for o in 0u8..6 {
                if domains[cell] & (1 << o) != 0
                    && assignments_valid(&[(cell, o)], &roots, &root_exits, mate)
                {
                    supported |= 1 << o;
                }
            }
            next[cell] &= supported;
            if next[cell] == 0 {
                return None;
            }
        }

        // Two-tile boundary patches: retain only rotations having support in
        // every adjacent tile's domain.  Each edge checks at most 6 * 6 cases.
        for cell in 0..grid.len() {
            if grid[cell] < 0 {
                continue;
            }
            let r = cell / W;
            let c = cell % W;
            for d in 0..6 {
                let nr = r as isize + DR[d];
                let nc = c as isize + DC[d];
                if !valid_cell(grid, W, nr, nc) {
                    continue;
                }
                let other = nr as usize * W + nc as usize;
                if cell >= other {
                    continue;
                }
                if !patch_has_multiple_exits(&[cell, other], &roots, &root_exits) {
                    continue;
                }
                let mut support_a = 0u8;
                let mut support_b = 0u8;
                for oa in 0u8..6 {
                    if domains[cell] & (1 << oa) == 0 {
                        continue;
                    }
                    for ob in 0u8..6 {
                        if domains[other] & (1 << ob) != 0
                            && assignments_valid(
                                &[(cell, oa), (other, ob)],
                                &roots,
                                &root_exits,
                                mate,
                            )
                        {
                            support_a |= 1 << oa;
                            support_b |= 1 << ob;
                        }
                    }
                }
                next[cell] &= support_a;
                next[other] &= support_b;
                if next[cell] == 0 || next[other] == 0 {
                    return None;
                }
            }
        }

        if next == domains {
            break;
        }
        domains.copy_from_slice(&next);
    }

    if !optimistic_pairs_reachable(W, grid, domains, exits, mate) {
        return None;
    }
    let (_, _, matched) = forced_components(W, grid, domains, exits, mate)?;
    let mut metrics = DomainMetrics {
        singleton: 0,
        ambiguity: 0,
        matched,
        move_lower_bound: 0,
    };
    for cell in 0..grid.len() {
        if grid[cell] < 0 {
            continue;
        }
        let count = domains[cell].count_ones() as usize;
        metrics.singleton += usize::from(count == 1);
        metrics.ambiguity += count - 1;
        metrics.move_lower_bound += domain_rotation_cost(initial[cell], domains[cell]);
    }
    Some(metrics)
}

fn select_mrv_tile(W: usize, grid: &[i32], domains: &[u8]) -> Option<usize> {
    let mut best = None;
    for cell in 0..grid.len() {
        if grid[cell] < 0 || domains[cell].count_ones() <= 1 {
            continue;
        }
        let r = cell / W;
        let c = cell % W;
        let mut pressure = 0usize;
        for d in 0..6 {
            let nr = r as isize + DR[d];
            let nc = c as isize + DC[d];
            if !valid_cell(grid, W, nr, nc) {
                pressure += 2;
            } else {
                let other = nr as usize * W + nc as usize;
                pressure += usize::from(domains[other].count_ones() == 1);
            }
        }
        let key = (
            domains[cell].count_ones(),
            std::cmp::Reverse(pressure),
            cell,
        );
        if best.as_ref().map_or(true, |&(best_key, _)| key < best_key) {
            best = Some((key, cell));
        }
    }
    best.map(|(_, cell)| cell)
}

fn domain_beam_quality(metrics: DomainMetrics) -> i64 {
    metrics.matched as i64 * 1_000_000_000_000 + metrics.singleton as i64 * 1_000_000
        - metrics.ambiguity as i64 * 1_000
        - metrics.move_lower_bound as i64
}

#[derive(Clone, Copy, Default)]
struct BoardStats {
    matched: usize,
    total_length: usize,
    bonus_crossings: usize,
    tile_revisits: usize,
    total_path_score: i64,
    moves: i32,
    score: i64,
}

#[allow(dead_code)]
struct Component {
    ports: Vec<usize>,
    exits: Vec<usize>,
    length: usize,
    bonus_count: usize,
    unique_tiles: usize,
    matched_pair: bool,
}

#[allow(dead_code)]
struct BoardAnalysis {
    comp_id: Vec<usize>,
    components: Vec<Component>,
    exit_target: Vec<usize>,
    stats: BoardStats,
}

fn build_board_analysis(
    W: usize,
    M: i32,
    grid: &[i32],
    orientation: &[u8],
    initial: &[u8],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    mate: &[usize],
) -> BoardAnalysis {
    let port_count = grid.len() * 6;
    let mut comp_id = vec![usize::MAX; port_count];
    let mut components = Vec::new();
    let mut exit_target = vec![usize::MAX; exits.len()];
    let mut stats = BoardStats::default();
    for cell in 0..grid.len() {
        if grid[cell] >= 0 {
            stats.moves += rotation_cost(initial[cell], orientation[cell]);
        }
    }

    for start in 0..port_count {
        let start_cell = start / 6;
        if grid[start_cell] < 0 || comp_id[start] != usize::MAX {
            continue;
        }
        let id = components.len();
        let mut stack = vec![start];
        let mut ports = Vec::new();
        let mut component_exits = Vec::new();
        let mut touched_tiles = HashSet::new();
        while let Some(port) = stack.pop() {
            if comp_id[port] != usize::MAX {
                continue;
            }
            comp_id[port] = id;
            ports.push(port);
            let cell = port / 6;
            let side = port % 6;
            touched_tiles.insert(cell);

            let internal = cell * 6 + paired_dir(orientation[cell], side);
            if comp_id[internal] == usize::MAX {
                stack.push(internal);
            }

            let r = cell / W;
            let c = cell % W;
            let nr = r as isize + DR[side];
            let nc = c as isize + DC[side];
            if valid_cell(grid, W, nr, nc) {
                let neighbor = (nr as usize * W + nc as usize) * 6 + opposite(side);
                if comp_id[neighbor] == usize::MAX {
                    stack.push(neighbor);
                }
            } else {
                let exit = exit_id[port];
                debug_assert!(exit >= 0);
                component_exits.push(exit as usize);
            }
        }

        let length = ports.len() / 2;
        let bonus_count = touched_tiles.iter().filter(|&&cell| bonus[cell]).count();
        let matched_pair =
            component_exits.len() == 2 && mate[component_exits[0]] == component_exits[1];
        if component_exits.len() == 2 {
            exit_target[component_exits[0]] = component_exits[1];
            exit_target[component_exits[1]] = component_exits[0];
        }
        if matched_pair {
            stats.matched += 1;
            stats.total_length += length;
            stats.bonus_crossings += bonus_count;
            stats.tile_revisits += length - touched_tiles.len();
            stats.total_path_score += (length * (bonus_count + 1)) as i64;
        }
        components.push(Component {
            ports,
            exits: component_exits,
            length,
            bonus_count,
            unique_tiles: touched_tiles.len(),
            matched_pair,
        });
    }
    stats.score =
        stats.matched as i64 * (stats.total_path_score - stats.moves as i64 * M as i64).max(0);
    BoardAnalysis {
        comp_id,
        components,
        exit_target,
        stats,
    }
}

struct RegionEvaluation {
    exit_target: Vec<usize>,
    stats: BoardStats,
}

fn evaluate_changed_region(
    W: usize,
    M: i32,
    grid: &[i32],
    old_orientation: &[u8],
    new_orientation: &[u8],
    initial: &[u8],
    bonus: &[bool],
    exit_id: &[i32],
    mate: &[usize],
    old: &BoardAnalysis,
    changed_cells: &[usize],
) -> RegionEvaluation {
    let mut affected_components = HashSet::new();
    let mut unique_changed = HashSet::new();
    for &cell in changed_cells {
        if old_orientation[cell] == new_orientation[cell] || !unique_changed.insert(cell) {
            continue;
        }
        for side in 0..6 {
            affected_components.insert(old.comp_id[cell * 6 + side]);
        }
    }
    if affected_components.is_empty() {
        return RegionEvaluation {
            exit_target: old.exit_target.clone(),
            stats: old.stats,
        };
    }

    let mut stats = old.stats;
    for &cell in &unique_changed {
        stats.moves += rotation_cost(initial[cell], new_orientation[cell])
            - rotation_cost(initial[cell], old_orientation[cell]);
    }
    let mut exit_target = old.exit_target.clone();
    let mut in_region = vec![false; old.comp_id.len()];
    for &component_id in &affected_components {
        let component = &old.components[component_id];
        for &port in &component.ports {
            in_region[port] = true;
        }
        for &exit in &component.exits {
            exit_target[exit] = usize::MAX;
        }
        if component.matched_pair {
            stats.matched -= 1;
            stats.total_length -= component.length;
            stats.bonus_crossings -= component.bonus_count;
            stats.tile_revisits -= component.length - component.unique_tiles;
            stats.total_path_score -= (component.length * (component.bonus_count + 1)) as i64;
        }
    }

    let mut visited = vec![false; old.comp_id.len()];
    for start in 0..old.comp_id.len() {
        if !in_region[start] || visited[start] {
            continue;
        }
        let mut stack = vec![start];
        let mut ports = Vec::new();
        let mut component_exits = Vec::new();
        let mut touched_tiles = HashSet::new();
        while let Some(port) = stack.pop() {
            if visited[port] {
                continue;
            }
            debug_assert!(in_region[port]);
            visited[port] = true;
            ports.push(port);
            let cell = port / 6;
            let side = port % 6;
            touched_tiles.insert(cell);

            let internal = cell * 6 + paired_dir(new_orientation[cell], side);
            debug_assert!(in_region[internal]);
            if !visited[internal] {
                stack.push(internal);
            }
            let r = cell / W;
            let c = cell % W;
            let nr = r as isize + DR[side];
            let nc = c as isize + DC[side];
            if valid_cell(grid, W, nr, nc) {
                let neighbor = (nr as usize * W + nc as usize) * 6 + opposite(side);
                debug_assert!(in_region[neighbor]);
                if !visited[neighbor] {
                    stack.push(neighbor);
                }
            } else {
                component_exits.push(exit_id[port] as usize);
            }
        }
        let length = ports.len() / 2;
        let bonus_count = touched_tiles.iter().filter(|&&cell| bonus[cell]).count();
        if component_exits.len() == 2 {
            exit_target[component_exits[0]] = component_exits[1];
            exit_target[component_exits[1]] = component_exits[0];
            if mate[component_exits[0]] == component_exits[1] {
                stats.matched += 1;
                stats.total_length += length;
                stats.bonus_crossings += bonus_count;
                stats.tile_revisits += length - touched_tiles.len();
                stats.total_path_score += (length * (bonus_count + 1)) as i64;
            }
        }
    }
    stats.score =
        stats.matched as i64 * (stats.total_path_score - stats.moves as i64 * M as i64).max(0);
    RegionEvaluation { exit_target, stats }
}

fn analyze_board(
    W: usize,
    M: i32,
    grid: &[i32],
    orientation: &[u8],
    initial: &[u8],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    mate: &[usize],
) -> BoardStats {
    build_board_analysis(
        W,
        M,
        grid,
        orientation,
        initial,
        bonus,
        exits,
        exit_id,
        mate,
    )
    .stats
}

fn repair_key(stats: BoardStats) -> (usize, i64, i64, std::cmp::Reverse<i32>) {
    (
        stats.matched,
        stats.score,
        stats.total_path_score,
        std::cmp::Reverse(stats.moves),
    )
}

fn construction_key(stats: BoardStats) -> (usize, i64, std::cmp::Reverse<i32>, i64) {
    (
        stats.matched,
        stats.score,
        std::cmp::Reverse(stats.moves),
        stats.total_path_score,
    )
}

fn output_key(stats: BoardStats) -> (i64, usize, i64, std::cmp::Reverse<i32>) {
    (
        stats.score,
        stats.matched,
        stats.total_path_score,
        std::cmp::Reverse(stats.moves),
    )
}

fn repair_path_candidates(
    W: usize,
    M: i32,
    grid: &[i32],
    orientation: &[u8],
    initial: &[u8],
    no_fixed: &[bool],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    pair: [usize; 2],
    valid_cells: usize,
    deadline: Instant,
) -> Vec<Vec<PathStep>> {
    let mut paths = find_path_candidates(
        W,
        M,
        grid,
        orientation,
        initial,
        no_fixed,
        None,
        None,
        bonus,
        exits,
        exit_id,
        pair[0],
        pair[1],
        valid_cells,
        REPAIR_PATH_BEAM_WIDTH,
        Some(deadline),
    );
    if Instant::now() >= deadline {
        return paths;
    }
    paths.extend(find_path_candidates(
        W,
        M,
        grid,
        orientation,
        initial,
        no_fixed,
        None,
        None,
        bonus,
        exits,
        exit_id,
        pair[1],
        pair[0],
        valid_cells,
        REPAIR_PATH_BEAM_WIDTH,
        Some(deadline),
    ));
    paths
}

struct XorShift64 {
    state: u64,
}

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self { state: seed.max(1) }
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.state;
        x ^= x << 7;
        x ^= x >> 9;
        x ^= x << 8;
        self.state = x;
        x
    }

    fn next_f64(&mut self) -> f64 {
        (self.next_u64() >> 11) as f64 / ((1u64 << 53) as f64)
    }
}

fn apply_path_orientation(orientation: &[u8], path: Vec<PathStep>) -> Vec<u8> {
    let mut result = orientation.to_vec();
    for step in path {
        result[step.cell] = step.orientation;
    }
    result
}

fn required_connected_count(
    analysis: &BoardAnalysis,
    matches: &[[usize; 2]],
    required: &[bool],
) -> usize {
    matches
        .iter()
        .enumerate()
        .filter(|&(i, pair)| required[i] && analysis.exit_target[pair[0]] == pair[1])
        .count()
}

fn ruin_recreate_candidate(
    W: usize,
    M: i32,
    grid: &[i32],
    initial: &[u8],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    matches: &[[usize; 2]],
    valid_cells: usize,
    current_orientation: &[u8],
    current: &BoardAnalysis,
    target_pair: usize,
    deadline: Instant,
) -> Option<(Vec<u8>, BoardStats, u64)> {
    if Instant::now() >= deadline {
        return None;
    }
    let mate = make_mate(exits.len(), matches);
    let no_fixed = vec![false; grid.len()];
    let mut required = vec![false; matches.len()];
    for (i, pair) in matches.iter().enumerate() {
        required[i] = current.exit_target[pair[0]] == pair[1];
    }
    required[target_pair] = true;
    let required_total = required.iter().filter(|&&x| x).count();
    let ruin_paths = repair_path_candidates(
        W,
        M,
        grid,
        current_orientation,
        initial,
        &no_fixed,
        bonus,
        exits,
        exit_id,
        matches[target_pair],
        valid_cells,
        deadline,
    );

    let mut evaluated = 0u64;
    let mut best: Option<(usize, BoardStats, Vec<u8>)> = None;
    for ruin_path in ruin_paths.into_iter().take(RUIN_CANDIDATES) {
        if Instant::now() >= deadline {
            break;
        }
        let mut orientation = apply_path_orientation(current_orientation, ruin_path);
        let mut analysis = build_board_analysis(
            W,
            M,
            grid,
            &orientation,
            initial,
            bonus,
            exits,
            exit_id,
            &mate,
        );
        evaluated += 1;
        if analysis.exit_target[matches[target_pair][0]] != matches[target_pair][1] {
            continue;
        }

        for _ in 0..RECREATE_STEPS {
            if Instant::now() >= deadline {
                break;
            }
            let disconnected: Vec<usize> = matches
                .iter()
                .enumerate()
                .filter_map(|(i, pair)| {
                    (required[i] && analysis.exit_target[pair[0]] != pair[1]).then_some(i)
                })
                .collect();
            if disconnected.is_empty() {
                break;
            }

            let mut repair_best: Option<(usize, BoardStats, Vec<u8>)> = None;
            for &repair_pair in &disconnected {
                if Instant::now() >= deadline {
                    break;
                }
                let paths = repair_path_candidates(
                    W,
                    M,
                    grid,
                    &orientation,
                    initial,
                    &no_fixed,
                    bonus,
                    exits,
                    exit_id,
                    matches[repair_pair],
                    valid_cells,
                    deadline,
                );
                for path in paths.into_iter().take(RECREATE_CANDIDATES) {
                    if Instant::now() >= deadline {
                        break;
                    }
                    let candidate_orientation = apply_path_orientation(&orientation, path);
                    let candidate = build_board_analysis(
                        W,
                        M,
                        grid,
                        &candidate_orientation,
                        initial,
                        bonus,
                        exits,
                        exit_id,
                        &mate,
                    );
                    evaluated += 1;
                    if candidate.exit_target[matches[repair_pair][0]] != matches[repair_pair][1] {
                        continue;
                    }
                    let restored = required_connected_count(&candidate, matches, &required);
                    if repair_best
                        .as_ref()
                        .map_or(true, |(best_restored, stats, _)| {
                            (
                                candidate.stats.matched,
                                restored,
                                output_key(candidate.stats),
                            ) > (stats.matched, *best_restored, output_key(*stats))
                        })
                    {
                        repair_best = Some((restored, candidate.stats, candidate_orientation));
                    }
                }
            }
            let Some((_, _, next_orientation)) = repair_best else {
                break;
            };
            orientation = next_orientation;
            analysis = build_board_analysis(
                W,
                M,
                grid,
                &orientation,
                initial,
                bonus,
                exits,
                exit_id,
                &mate,
            );
        }

        let restored = required_connected_count(&analysis, matches, &required);
        if best.as_ref().map_or(true, |(best_restored, stats, _)| {
            (
                analysis.stats.matched,
                usize::from(restored == required_total),
                restored,
                output_key(analysis.stats),
            ) > (
                stats.matched,
                usize::from(*best_restored == required_total),
                *best_restored,
                output_key(*stats),
            )
        }) {
            best = Some((restored, analysis.stats, orientation));
        }
    }
    best.map(|(_, stats, orientation)| (orientation, stats, evaluated))
}

fn annealing_energy(stats: BoardStats, match_weight: f64) -> f64 {
    stats.score as f64 + match_weight * stats.matched as f64
}

fn solve_component_repair(
    W: usize,
    M: i32,
    grid: &[i32],
    initial: &[u8],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    matches: &[[usize; 2]],
    valid_cells: usize,
) -> (Vec<u8>, BoardStats, u64) {
    let started = Instant::now();
    let hard_deadline = started + Duration::from_millis(SOLVER_TIME_LIMIT_MS);
    let construction_deadline = started + Duration::from_millis(SOLVER_TIME_LIMIT_MS * 30 / 100);
    let ruin_deadline = hard_deadline;
    let mate = make_mate(exits.len(), matches);
    let no_fixed = vec![false; grid.len()];
    let mut orientation = initial.to_vec();
    let mut analysis = build_board_analysis(
        W,
        M,
        grid,
        &orientation,
        initial,
        bonus,
        exits,
        exit_id,
        &mate,
    );
    let mut evaluated = 0u64;
    let mut visited = HashSet::new();
    visited.insert(orientation.clone());
    let mut best_orientation = orientation.clone();
    let mut best_stats = analysis.stats;
    let mut output_orientation = orientation.clone();
    let mut output_stats = analysis.stats;

    while Instant::now() < construction_deadline {
        let mut accepted_in_pass = 0usize;
        for pair in matches {
            if Instant::now() >= construction_deadline {
                break;
            }
            analysis = build_board_analysis(
                W,
                M,
                grid,
                &orientation,
                initial,
                bonus,
                exits,
                exit_id,
                &mate,
            );
            if analysis.exit_target[pair[0]] == pair[1] {
                continue;
            }

            let paths = repair_path_candidates(
                W,
                M,
                grid,
                &orientation,
                initial,
                &no_fixed,
                bonus,
                exits,
                exit_id,
                *pair,
                valid_cells,
                construction_deadline,
            );
            let mut best: Option<(BoardStats, Vec<u8>)> = None;
            let mut seen_orientations = HashSet::new();
            for path in paths {
                if Instant::now() >= construction_deadline {
                    break;
                }
                let mut candidate_orientation = orientation.clone();
                let mut changed_cells = Vec::new();
                for step in path {
                    if candidate_orientation[step.cell] != step.orientation {
                        changed_cells.push(step.cell);
                    }
                    candidate_orientation[step.cell] = step.orientation;
                }
                if !seen_orientations.insert(candidate_orientation.clone()) {
                    continue;
                }
                if visited.contains(&candidate_orientation) {
                    continue;
                }
                evaluated += 1;
                let candidate = evaluate_changed_region(
                    W,
                    M,
                    grid,
                    &orientation,
                    &candidate_orientation,
                    initial,
                    bonus,
                    exit_id,
                    &mate,
                    &analysis,
                    &changed_cells,
                );
                if output_key(candidate.stats) > output_key(output_stats) {
                    output_stats = candidate.stats;
                    output_orientation = candidate_orientation.clone();
                }
                if candidate.exit_target[pair[0]] != pair[1]
                    || candidate.stats.matched < analysis.stats.matched
                {
                    continue;
                }
                if best.as_ref().map_or(true, |(stats, _)| {
                    construction_key(candidate.stats) > construction_key(*stats)
                }) {
                    best = Some((candidate.stats, candidate_orientation));
                }
            }
            if let Some((stats, next_orientation)) = best {
                orientation = next_orientation;
                visited.insert(orientation.clone());
                accepted_in_pass += 1;
                if repair_key(stats) > repair_key(best_stats) {
                    best_stats = stats;
                    best_orientation = orientation.clone();
                }
            }
        }
        analysis = build_board_analysis(
            W,
            M,
            grid,
            &orientation,
            initial,
            bonus,
            exits,
            exit_id,
            &mate,
        );
        if accepted_in_pass == 0 || best_stats.matched == matches.len() {
            break;
        }
    }

    // Ruin-and-recreate phase.  A macro move may temporarily lose matched
    // components while connecting a target pair, then repairs the pairs broken
    // by that change.  Only the completed macro state is annealed.
    let mut rng_seed = 0x9e3779b97f4a7c15u64;
    for (cell, &o) in initial.iter().enumerate() {
        rng_seed ^= (cell as u64 + 1).wrapping_mul(o as u64 + 0x100000001b3);
        rng_seed = rng_seed.rotate_left(11);
    }
    let mut rng = XorShift64::new(rng_seed);
    while Instant::now() < ruin_deadline && !matches.is_empty() {
        let offset = (rng.next_u64() as usize) % matches.len().max(1);
        for k in 0..matches.len() {
            if Instant::now() >= ruin_deadline {
                break;
            }
            let pair_id = (offset + k) % matches.len();
            analysis = build_board_analysis(
                W,
                M,
                grid,
                &orientation,
                initial,
                bonus,
                exits,
                exit_id,
                &mate,
            );
            if analysis.exit_target[matches[pair_id][0]] == matches[pair_id][1] {
                continue;
            }
            let Some((candidate_orientation, candidate_stats, macro_evaluated)) =
                ruin_recreate_candidate(
                    W,
                    M,
                    grid,
                    initial,
                    bonus,
                    exits,
                    exit_id,
                    matches,
                    valid_cells,
                    &orientation,
                    &analysis,
                    pair_id,
                    ruin_deadline,
                )
            else {
                continue;
            };
            evaluated += macro_evaluated;
            if output_key(candidate_stats) > output_key(output_stats) {
                output_stats = candidate_stats;
                output_orientation = candidate_orientation.clone();
            }

            let progress = Instant::now().duration_since(started).as_secs_f64()
                / Duration::from_millis(SOLVER_TIME_LIMIT_MS).as_secs_f64();
            let progress = progress.clamp(0.0, 1.0);
            let match_weight = 2_000.0 * (1.0 - progress) + 200.0 * progress;
            let temperature = 5_000.0 * (1.0 - progress) + 100.0 * progress;
            let current_energy = annealing_energy(analysis.stats, match_weight);
            let candidate_energy = annealing_energy(candidate_stats, match_weight);
            let delta = candidate_energy - current_energy;
            if delta >= 0.0 || rng.next_f64() < (delta / temperature).exp() {
                orientation = candidate_orientation;
                if repair_key(candidate_stats) > repair_key(best_stats) {
                    best_stats = candidate_stats;
                    best_orientation = orientation.clone();
                }
            }
        }
        analysis = build_board_analysis(
            W,
            M,
            grid,
            &orientation,
            initial,
            bonus,
            exits,
            exit_id,
            &mate,
        );
        if analysis.stats.matched == matches.len() {
            break;
        }
    }

    // Improvement phase: once every target is connected, reroute one complete
    // pair at a time while preserving all matches, and accept only an exact raw
    // score improvement.  This removes expensive construction detours without
    // risking the primary objective.
    if best_stats.matched == matches.len() {
        orientation = best_orientation.clone();
        while Instant::now() < hard_deadline {
            let mut improved = 0usize;
            for pair in matches {
                if Instant::now() >= hard_deadline {
                    break;
                }
                let current = build_board_analysis(
                    W,
                    M,
                    grid,
                    &orientation,
                    initial,
                    bonus,
                    exits,
                    exit_id,
                    &mate,
                );
                let paths = repair_path_candidates(
                    W,
                    M,
                    grid,
                    &orientation,
                    initial,
                    &no_fixed,
                    bonus,
                    exits,
                    exit_id,
                    *pair,
                    valid_cells,
                    hard_deadline,
                );
                let mut candidate_best: Option<(BoardStats, Vec<u8>)> = None;
                for path in paths {
                    if Instant::now() >= hard_deadline {
                        break;
                    }
                    let mut candidate_orientation = orientation.clone();
                    let mut changed_cells = Vec::new();
                    for step in path {
                        if candidate_orientation[step.cell] != step.orientation {
                            changed_cells.push(step.cell);
                        }
                        candidate_orientation[step.cell] = step.orientation;
                    }
                    evaluated += 1;
                    let candidate = evaluate_changed_region(
                        W,
                        M,
                        grid,
                        &orientation,
                        &candidate_orientation,
                        initial,
                        bonus,
                        exit_id,
                        &mate,
                        &current,
                        &changed_cells,
                    );
                    if output_key(candidate.stats) > output_key(output_stats) {
                        output_stats = candidate.stats;
                        output_orientation = candidate_orientation.clone();
                    }
                    if candidate.stats.matched != matches.len()
                        || repair_key(candidate.stats) <= repair_key(current.stats)
                    {
                        continue;
                    }
                    if candidate_best.as_ref().map_or(true, |(stats, _)| {
                        repair_key(candidate.stats) > repair_key(*stats)
                    }) {
                        candidate_best = Some((candidate.stats, candidate_orientation));
                    }
                }
                if let Some((stats, next_orientation)) = candidate_best {
                    orientation = next_orientation;
                    best_orientation = orientation.clone();
                    best_stats = stats;
                    improved += 1;
                }
            }
            if improved == 0 {
                break;
            }
        }

        // Final polish: after bulk reroutes have established every pair, remove
        // individually redundant rotations without ever losing a match.
        while Instant::now() < hard_deadline {
            let mut improved = 0usize;
            for cell in 0..grid.len() {
                if Instant::now() >= hard_deadline {
                    break;
                }
                if grid[cell] < 0 {
                    continue;
                }
                let current = build_board_analysis(
                    W,
                    M,
                    grid,
                    &orientation,
                    initial,
                    bonus,
                    exits,
                    exit_id,
                    &mate,
                );
                let current_stats = current.stats;
                let mut tile_best: Option<(BoardStats, u8)> = None;
                for o in 0u8..6 {
                    if Instant::now() >= hard_deadline {
                        break;
                    }
                    if o == orientation[cell] {
                        continue;
                    }
                    let mut candidate_orientation = orientation.clone();
                    candidate_orientation[cell] = o;
                    evaluated += 1;
                    let stats = evaluate_changed_region(
                        W,
                        M,
                        grid,
                        &orientation,
                        &candidate_orientation,
                        initial,
                        bonus,
                        exit_id,
                        &mate,
                        &current,
                        &[cell],
                    )
                    .stats;
                    if output_key(stats) > output_key(output_stats) {
                        output_stats = stats;
                        output_orientation = candidate_orientation;
                    }
                    if stats.matched == matches.len()
                        && repair_key(stats) > repair_key(current_stats)
                        && tile_best
                            .as_ref()
                            .map_or(true, |(best, _)| repair_key(stats) > repair_key(*best))
                    {
                        tile_best = Some((stats, o));
                    }
                }
                if let Some((stats, o)) = tile_best {
                    orientation[cell] = o;
                    best_orientation = orientation.clone();
                    best_stats = stats;
                    improved += 1;
                }
            }
            if improved == 0 {
                break;
            }
        }
    }
    (output_orientation, output_stats, evaluated)
}

fn solve_domain_beam(
    W: usize,
    M: i32,
    grid: &[i32],
    initial: &[u8],
    bonus: &[bool],
    exits: &[(usize, usize)],
    exit_id: &[i32],
    matches: &[[usize; 2]],
    valid_cells: usize,
) -> Option<(Vec<u8>, u64)> {
    let mate = make_mate(exits.len(), matches);
    let mut domains = vec![0u8; grid.len()];
    for cell in 0..grid.len() {
        if grid[cell] >= 0 {
            domains[cell] = 0x3f;
        }
    }
    let metrics = propagate_domains(W, grid, initial, exits, &mate, &mut domains)?;
    let mut beam = vec![DomainBeamState { domains, metrics }];
    let mut nodes = 1u64;
    let mut best_complete: Option<(i64, i32, Vec<u8>)> = None;

    for depth in 0..valid_cells {
        let mut children = Vec::with_capacity(beam.len() * 6);
        let mut seen = HashSet::new();
        for state in beam {
            let Some(cell) = select_mrv_tile(W, grid, &state.domains) else {
                if state.metrics.matched == matches.len() {
                    let orientation: Vec<u8> = state
                        .domains
                        .iter()
                        .map(|mask| mask.trailing_zeros() as u8)
                        .collect();
                    let stats = analyze_board(
                        W,
                        M,
                        grid,
                        &orientation,
                        initial,
                        bonus,
                        exits,
                        exit_id,
                        &mate,
                    );
                    let key = (stats.score, -stats.moves);
                    if best_complete
                        .as_ref()
                        .map_or(true, |&(score, neg_moves, _)| key > (score, neg_moves))
                    {
                        best_complete = Some((key.0, key.1, orientation));
                    }
                }
                continue;
            };
            for o in 0u8..6 {
                if state.domains[cell] & (1 << o) == 0 {
                    continue;
                }
                let mut child_domains = state.domains.clone();
                child_domains[cell] = 1 << o;
                nodes += 1;
                let Some(child_metrics) =
                    propagate_domains(W, grid, initial, exits, &mate, &mut child_domains)
                else {
                    continue;
                };
                if !seen.insert(child_domains.clone()) {
                    continue;
                }
                if child_metrics.singleton == valid_cells && child_metrics.matched == matches.len()
                {
                    let orientation: Vec<u8> = child_domains
                        .iter()
                        .map(|mask| mask.trailing_zeros() as u8)
                        .collect();
                    let stats = analyze_board(
                        W,
                        M,
                        grid,
                        &orientation,
                        initial,
                        bonus,
                        exits,
                        exit_id,
                        &mate,
                    );
                    let key = (stats.score, -stats.moves);
                    if best_complete
                        .as_ref()
                        .map_or(true, |&(score, neg_moves, _)| key > (score, neg_moves))
                    {
                        best_complete = Some((key.0, key.1, orientation));
                    }
                    continue;
                }
                children.push(DomainBeamState {
                    domains: child_domains,
                    metrics: child_metrics,
                });
            }
        }
        if children.is_empty() {
            break;
        }
        children
            .sort_unstable_by_key(|state| std::cmp::Reverse(domain_beam_quality(state.metrics)));
        children.truncate(DOMAIN_BEAM_WIDTH);
        if depth % 10 == 0 {
            let best = children[0].metrics;
            eprintln!(
                "domain beam depth={}, states={}, fixed={}/{}, matched={}/{}, ambiguity={}, move_lb={}",
                depth + 1,
                children.len(),
                best.singleton,
                valid_cells,
                best.matched,
                matches.len(),
                best.ambiguity,
                best.move_lower_bound
            );
        }
        beam = children;
    }
    best_complete.map(|(_, _, orientation)| (orientation, nodes))
}

struct CspContext<'a> {
    W: usize,
    M: i32,
    grid: &'a [i32],
    initial: &'a [u8],
    no_fixed: &'a [bool],
    bonus: &'a [bool],
    exits: &'a [(usize, usize)],
    exit_id: &'a [i32],
    matches: &'a [[usize; 2]],
    valid_cells: usize,
}

fn route_geometry(candidate: &RouteCandidate) -> Vec<(usize, u8, u8)> {
    candidate
        .path
        .iter()
        .map(|step| {
            (
                step.cell,
                step.enter.min(step.out),
                step.enter.max(step.out),
            )
        })
        .collect()
}

fn solve_path_csp_dfs(
    context: &CspContext,
    candidates: &[Vec<RouteCandidate>],
    domains: &mut [u8],
    used_sides: &mut [u8],
    assigned: &mut [bool],
    selected_routes: &mut [Option<RouteCandidate>],
    remaining: usize,
    nodes: &mut u64,
) -> bool {
    *nodes += 1;
    if remaining == 0 {
        return true;
    }

    // MRV: choose the unassigned pair with the fewest currently compatible
    // route candidates.
    let mut chosen_pair = usize::MAX;
    let mut compatible_ids = Vec::new();
    for pair in 0..candidates.len() {
        if assigned[pair] {
            continue;
        }
        let ids: Vec<usize> = candidates[pair]
            .iter()
            .enumerate()
            .filter_map(|(i, cand)| candidate_compatible(cand, domains, used_sides).then_some(i))
            .collect();
        if chosen_pair == usize::MAX || ids.len() < compatible_ids.len() {
            chosen_pair = pair;
            compatible_ids = ids;
        }
    }

    // The static pool is only a starting point.  Regenerate routes under the
    // domains and occupied sides of this exact CSP node, so a route omitted by
    // an earlier beam does not make the whole-board search falsely infeasible.
    let mut branch_candidates: Vec<RouteCandidate> = compatible_ids
        .into_iter()
        .map(|id| candidates[chosen_pair][id].clone())
        .collect();
    let pair = context.matches[chosen_pair];
    let dynamic_paths = find_path_candidates(
        context.W,
        context.M,
        context.grid,
        context.initial,
        context.initial,
        context.no_fixed,
        Some(domains),
        Some(used_sides),
        context.bonus,
        context.exits,
        context.exit_id,
        pair[0],
        pair[1],
        context.valid_cells,
        PATH_BEAM_WIDTH,
        None,
    );
    let mut seen: HashSet<Vec<(usize, u8, u8)>> =
        branch_candidates.iter().map(route_geometry).collect();
    for path in dynamic_paths {
        let Some(candidate) = make_route_candidate(path, context.bonus, context.grid.len()) else {
            continue;
        };
        let geometry = route_geometry(&candidate);
        if candidate_compatible(&candidate, domains, used_sides) && seen.insert(geometry) {
            branch_candidates.push(candidate);
        }
    }
    if branch_candidates.is_empty() {
        return false;
    }

    // Prefer candidates that increase the minimum required move count least;
    // use path score only as a secondary ordering criterion.
    branch_candidates.sort_unstable_by_key(|cand| {
        let mut move_delta = 0i32;
        for req in &cand.requirements {
            let old = domain_rotation_cost(context.initial[req.cell], domains[req.cell]);
            let new = domain_rotation_cost(
                context.initial[req.cell],
                domains[req.cell] & req.domain_mask,
            );
            move_delta += new - old;
        }
        let path_value = cand.length * (cand.bonuses + 1);
        (move_delta, std::cmp::Reverse(path_value))
    });

    for cand in branch_candidates {
        let mut changes = Vec::with_capacity(cand.requirements.len());
        for req in &cand.requirements {
            changes.push((req.cell, domains[req.cell], used_sides[req.cell]));
            domains[req.cell] &= req.domain_mask;
            used_sides[req.cell] |= req.used_sides;
        }
        assigned[chosen_pair] = true;
        selected_routes[chosen_pair] = Some(cand.clone());

        if solve_path_csp_dfs(
            context,
            candidates,
            domains,
            used_sides,
            assigned,
            selected_routes,
            remaining - 1,
            nodes,
        ) {
            return true;
        }

        assigned[chosen_pair] = false;
        selected_routes[chosen_pair] = None;
        for &(cell, old_domain, old_used) in changes.iter().rev() {
            domains[cell] = old_domain;
            used_sides[cell] = old_used;
        }
    }
    false
}

fn solve_path_csp(
    context: &CspContext,
    candidates: &[Vec<RouteCandidate>],
) -> Option<(Vec<u8>, Vec<RouteCandidate>, u64)> {
    let mut domains = vec![0x3fu8; context.initial.len()];
    let mut used_sides = vec![0u8; context.initial.len()];
    let mut assigned = vec![false; candidates.len()];
    let mut selected_routes = vec![None; candidates.len()];
    let mut nodes = 0u64;
    if !solve_path_csp_dfs(
        context,
        candidates,
        &mut domains,
        &mut used_sides,
        &mut assigned,
        &mut selected_routes,
        candidates.len(),
        &mut nodes,
    ) {
        eprintln!(
            "candidate CSP exhausted {} nodes without a full assignment",
            nodes
        );
        return None;
    }

    let mut final_orientation = context.initial.to_vec();
    for cell in 0..context.initial.len() {
        final_orientation[cell] = (0u8..6)
            .filter(|&o| domains[cell] & (1 << o) != 0)
            .min_by_key(|&o| rotation_cost(context.initial[cell], o))
            .unwrap();
    }
    Some((
        final_orientation,
        selected_routes.into_iter().map(Option::unwrap).collect(),
        nodes,
    ))
}

fn commit_path(
    path: &[(usize, u8)],
    W: usize,
    orientation: &mut [u8],
    fixed: &mut [bool],
    moves: &mut Vec<(usize, usize, i32)>,
) {
    // Transactional commit: build every move for this pair first.
    // find_path_beam() itself never changes the board, so a pair that has no
    // complete route to its target exit causes zero rotations and zero fixes.
    let mut pair_moves: Vec<(usize, usize, i32)> = Vec::new();
    let mut pair_orientation = vec![-1i8; orientation.len()];

    for &(cell, target_orientation) in path {
        if fixed[cell] {
            debug_assert_eq!(orientation[cell], target_orientation);
            continue;
        }
        if pair_orientation[cell] >= 0 {
            debug_assert_eq!(pair_orientation[cell], target_orientation as i8);
            continue;
        }

        let r = cell / W;
        let c = cell % W;
        append_rotation_moves(&mut pair_moves, r, c, orientation[cell], target_orientation);
        pair_orientation[cell] = target_orientation as i8;
    }

    // Only a fully completed source->target path reaches this function.
    for &(cell, target_orientation) in path {
        if !fixed[cell] && pair_orientation[cell] >= 0 {
            orientation[cell] = target_orientation;
            fixed[cell] = true;
            pair_orientation[cell] = -2; // mark committed; ignore repeated visits
        }
    }
    moves.extend(pair_moves);
}

fn main() {
    let mut sc = Scanner::new();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());

    let N: usize = sc.next();
    let M: i32 = sc.next();
    let B: usize = sc.next();
    let P: usize = sc.next();

    let mut matches = vec![[0usize; 2]; P];
    for pair in &mut matches {
        pair[0] = sc.next();
        pair[1] = sc.next();
    }

    let W = 2 * N - 1;
    let mut grid = vec![-1i32; W * W];
    let mut orientation = vec![0u8; W * W];
    let mut valid_cells = 0usize;
    for r in 0..W {
        for c in 0..W {
            let x: i32 = sc.next();
            grid[r * W + c] = x;
            if x >= 0 {
                orientation[r * W + c] = x as u8;
                valid_cells += 1;
            }
        }
    }

    let mut bonus = vec![false; W * W];
    for _ in 0..B {
        let r: usize = sc.next();
        let c: usize = sc.next();
        bonus[r * W + c] = true;
    }

    let (exits, exit_id) = build_exits(N, &grid);
    let initial_orientation = orientation.clone();
    let mut moves: Vec<(usize, usize, i32)> = Vec::new();
    let mut matched_count = 0usize;
    let mut total_path_length = 0usize;
    let mut total_bonus_crossings = 0usize;
    let mut total_tile_revisits = 0usize;
    let mut total_path_score = 0i64;
    let mut csp_nodes = 0u64;
    let method;

    let (repair_orientation, repair_stats, evaluated) = solve_component_repair(
        W,
        M,
        &grid,
        &initial_orientation,
        &bonus,
        &exits,
        &exit_id,
        &matches,
        valid_cells,
    );
    if ENABLE_COMPONENT_REPAIR {
        method = "component_repair";
        csp_nodes = evaluated;
        orientation = repair_orientation;
        for cell in 0..grid.len() {
            if grid[cell] < 0 {
                continue;
            }
            append_rotation_moves(
                &mut moves,
                cell / W,
                cell % W,
                initial_orientation[cell],
                orientation[cell],
            );
        }
        matched_count = repair_stats.matched;
        total_path_length = repair_stats.total_length;
        total_bonus_crossings = repair_stats.bonus_crossings;
        total_tile_revisits = repair_stats.tile_revisits;
        total_path_score = repair_stats.total_path_score;
    } else if let Some((final_orientation, nodes)) = solve_domain_beam(
        W,
        M,
        &grid,
        &initial_orientation,
        &bonus,
        &exits,
        &exit_id,
        &matches,
        valid_cells,
    ) {
        csp_nodes = nodes;
        method = "domain_propagation_beam";
        orientation = final_orientation;
        for cell in 0..grid.len() {
            if grid[cell] < 0 {
                continue;
            }
            append_rotation_moves(
                &mut moves,
                cell / W,
                cell % W,
                initial_orientation[cell],
                orientation[cell],
            );
        }
        let mate = make_mate(exits.len(), &matches);
        let stats = analyze_board(
            W,
            M,
            &grid,
            &orientation,
            &initial_orientation,
            &bonus,
            &exits,
            &exit_id,
            &mate,
        );
        matched_count = stats.matched;
        total_path_length = stats.total_length;
        total_bonus_crossings = stats.bonus_crossings;
        total_tile_revisits = stats.tile_revisits;
        total_path_score = stats.total_path_score;
    } else {
        eprintln!("domain propagation beam failed; trying candidate-path CSP");
        let no_fixed = vec![false; W * W];
        let mut all_candidates: Vec<Vec<RouteCandidate>> = Vec::with_capacity(P);

        for (pair_id, pair) in matches.iter().enumerate() {
            let paths = find_path_candidates(
                W,
                M,
                &grid,
                &initial_orientation,
                &initial_orientation,
                &no_fixed,
                None,
                None,
                &bonus,
                &exits,
                &exit_id,
                pair[0],
                pair[1],
                valid_cells,
                PATH_BEAM_WIDTH,
                None,
            );
            let candidates: Vec<RouteCandidate> = paths
                .into_iter()
                .filter_map(|path| make_route_candidate(path, &bonus, grid.len()))
                .collect();
            eprintln!("pair {}/{} candidates={}", pair_id + 1, P, candidates.len());
            all_candidates.push(candidates);
        }

        let csp_context = CspContext {
            W,
            M,
            grid: &grid,
            initial: &initial_orientation,
            no_fixed: &no_fixed,
            bonus: &bonus,
            exits: &exits,
            exit_id: &exit_id,
            matches: &matches,
            valid_cells,
        };
        if let Some((final_orientation, selected_routes, nodes)) =
            solve_path_csp(&csp_context, &all_candidates)
        {
            csp_nodes = nodes;
            method = "candidate_path_csp";
            orientation = final_orientation;
            for cell in 0..grid.len() {
                if grid[cell] < 0 {
                    continue;
                }
                append_rotation_moves(
                    &mut moves,
                    cell / W,
                    cell % W,
                    initial_orientation[cell],
                    orientation[cell],
                );
            }

            matched_count = P;
            for pair in 0..P {
                let cand = &selected_routes[pair];
                total_path_length += cand.length;
                total_bonus_crossings += cand.bonuses;
                total_tile_revisits += cand.length - cand.requirements.len();
                total_path_score += (cand.length * (cand.bonuses + 1)) as i64;
            }
        } else {
            // Candidate pools can omit the globally compatible route.  Keep the
            // previous pair-greedy method as a valid fallback while the CSP route
            // generator is being developed.
            method = "greedy_fallback";
            let mut fixed = vec![false; W * W];
            for pair in &matches {
                let Some(path) = find_path_beam(
                    W,
                    M,
                    &grid,
                    &orientation,
                    &fixed,
                    &bonus,
                    &exits,
                    &exit_id,
                    pair[0],
                    pair[1],
                    valid_cells,
                ) else {
                    continue;
                };

                let path_len = path.len();
                let mut bonus_seen = vec![false; grid.len()];
                let mut unique_tiles = 0usize;
                let path_bonus = path
                    .iter()
                    .filter(|(cell, _)| {
                        if !bonus_seen[*cell] {
                            unique_tiles += 1;
                        }
                        let first = bonus[*cell] && !bonus_seen[*cell];
                        bonus_seen[*cell] = true;
                        first
                    })
                    .count();
                total_tile_revisits += path_len - unique_tiles;
                total_path_length += path_len;
                total_bonus_crossings += path_bonus;
                total_path_score += (path_len * (path_bonus + 1)) as i64;

                commit_path(&path, W, &mut orientation, &mut fixed, &mut moves);
                matched_count += 1;
            }
        }
    }

    eprintln!(
        "matched {}/{} pairs, moves={}, total_len={}, tile_revisits={}, bonus_crossings={}, path_score={}, beam_width={}, path_candidates={}, csp_nodes={}, method={}",
        matched_count,
        P,
        moves.len(),
        total_path_length,
        total_tile_revisits,
        total_bonus_crossings,
        total_path_score,
        BEAM_WIDTH,
        PATH_CANDIDATES,
        csp_nodes,
        method
    );

    writeln!(out, "{}", moves.len()).unwrap();
    for (r, c, dir) in moves {
        writeln!(out, "{} {} {}", r, c, dir).unwrap();
    }
    out.flush().unwrap();
}
