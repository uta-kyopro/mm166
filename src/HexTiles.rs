#![allow(non_snake_case)]

use std::cmp::Reverse;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, VecDeque};
use std::io::{self, Write};
use std::str::FromStr;
use std::time::{Duration, Instant};

// Search parameters.
const TIME_LIMIT_MS: u64 = 9_600;
const OUTPUT_CONSTRUCTION_ONLY: bool = false;
const NORMAL_BEAM: usize = 72;
const NORMAL_BONUS_PENALTY: i64 = 300; // reserve bonus transitions for long paths
const PROTECT_OUTER_BONUS_FROM_ORDINARY: bool = true;
const ENABLE_REVERSE_ROUTE_BFS: bool = true;
const ENABLE_SHORT_ROUTE_DETOURS: bool = false;
const ENABLE_DEFERRED_ROUTE_CHOICES: bool = false;
const NORMAL_ROUTE_DETOUR_STEPS: usize = 2;
const NORMAL_ROUTE_DETOUR_MAX_DISTANCE: usize = 3;
const SPECIAL_BEAM: usize = 192;
const SPECIAL_CANDIDATES: usize = 24;
const WIDTHS: [usize; 3] = [1, 2, 3];
const MAX_SPECIAL: usize = 3;
const LAYERED_MAX_SPECIAL: usize = 3;
const OUTER_LAYERS: usize = 3;
const ENABLE_LAYERED_BOARD_BEAM: bool = true;
const ENABLE_FULL_BOARD_CONSTRUCTION_BEAM: bool = true;
const ENABLE_TREE_BOARD_BEAM: bool = true;
const COMPLETE_TREE_BOARD_BEAM: bool = true;
const COMPLETE_TREE_BOARD_BEAM_SAFETY_MS: u64 = 60_000;
const LAYERED_BOARD_BEAM_WIDTH: usize = 10;
const TREE_BOARD_K_LEVELS: usize = 4;
const TREE_BOARD_MAX_K_DIVERSE_STATES: usize = 4;
const PROJECTED_FREE_USE_NUM: i64 = 9;
const PROJECTED_FREE_USE_DEN: i64 = 10;
const PROJECTED_ROTATION_NUM: i32 = 11;
const PROJECTED_ROTATION_DEN: i32 = 10;
const LAYERED_DEFERRED_RESERVED_STATES: usize = 0;
const LAYERED_ROUTE_CANDIDATES: usize = 4;
const LAYERED_DEFERRED_CHOICES: usize = 1;
const LAYERED_DEFERRED_ASSIGNMENTS: usize = 4;
const ENABLE_EXACT_CSP_CONSTRUCTION: bool = false;
const EXACT_CSP_CONSTRUCTION_MS: u64 = 300;
const EXACT_CSP_PRESERVED_TRUNKS: usize = 3;
const ENABLE_SECOND_CONSTRUCTION_BEAM: bool = true;
const SECOND_CONSTRUCTION_BEAM_WIDTH: usize = 8;
const SECOND_CONSTRUCTION_ROUTE_CANDIDATES: usize = 4;
const SECOND_CONSTRUCTION_UNMATCHED: usize = 3;
const SECOND_CONSTRUCTION_LONG_PAIRS: usize = 6;
const SECOND_CONSTRUCTION_MIN_CELLS: usize = 0;
const SECOND_CONSTRUCTION_SA_FRACTION: f64 = 0.05;
const SECOND_FRESH_LIMIT_MS: u64 = 650;
const SECOND_FRESH_DOMAIN_RESOLVE_MS: u64 = 100;
const CONSTRUCTION_LIMIT_MS: u64 = 4_500;
const POST_CONSTRUCTION_POLISH_MS: u64 = 100;
const PATH_REALLOCATION_MS: u64 = 400;
const LAYERED_OUTER_LIMIT_MS: u64 = 700;
const LAYERED_SPECIAL_LIMIT_MS: u64 = 600;
const DIRECT_TWO_EXIT_IN_LAYERED: bool = true;
const DIRECT_TWO_EXIT_IN_LEGACY: bool = false;
const ENABLE_LEGACY_CONSTRUCTION: bool = false;
const ENABLE_CONNECT_REPAIR: bool = true;
const LOCAL_EXTEND_INTERVAL_MS: u64 = 60;
const LOCAL_EXTEND_BUDGET_MS: u64 = 7;
const LOCAL_PATTERN_LIMIT_4: usize = 480;
const LOW_BONUS_REALLOCATION_MS: u64 = 300;
const LOW_BONUS_REALLOCATION_HIGH_BONUS_MS: u64 = 500;
const LOW_BONUS_REALLOCATION_HIGH_BONUS_THRESHOLD: usize = 4;
const LOW_BONUS_REALLOCATION_TARGETS: usize = 8;
const LOW_BONUS_REALLOCATION_STEP_MS: u64 = 4;
const RESTORE_REPAIR_INTERVAL_MS: u64 = 120;
const RESTORE_REPAIR_BUDGET_MS: u64 = 5;
const CONNECT_REPAIR_INTERVAL_MS: u64 = 450;
const CONNECT_REPAIR_BUDGET_MS: u64 = 80;
const CONNECT_REPAIR_BEAM: usize = 96;
const CONNECT_REPAIR_TARGETS: usize = 10;
const NONBONUS_SHORTEN_INTERVAL_MS: u64 = 600;
const NONBONUS_SHORTEN_BUDGET_MS: u64 = 4;
const NONBONUS_SHORTEN_TOP_TARGETS: usize = 4;
const MULTITILE_CHOICE_LIMIT: usize = 24;
const COMPACT_REPRESENTATIVES: usize = 1;
const COMPACT_SA_START_TEMP: f64 = 2_000_000.0;
const COMPACT_SA_END_TEMP: f64 = 100.0;
const COMPACT_SEGMENT_INTERVAL_MS: u64 = 80;
const MULTI_TRUNK_LNS_HEROES: usize = 2;
const MULTI_TRUNK_LNS_VICTIMS: usize = 4;
const MULTI_TRUNK_LNS_HERO_PERCENT: u32 = 65;
const MULTI_TRUNK_LNS_LIMIT_MS: u64 = 150;
const ENABLE_TWO_PATH_LNS: bool = false;
const TWO_PATH_LNS_BUDGET_MS: u64 = 80;
const TWO_PATH_LNS_PAIR_CANDIDATES: usize = 8;
const ENABLE_DETACHED_LOOP_MERGE: bool = false;
const SA_SCORE_ESTIMATE_SCALE: f64 = 5.54;
const SA_SCORE_ESTIMATE_N_EXP: f64 = 3.66;
const SA_SCORE_ESTIMATE_B_EXP: f64 = 1.06;
const SA_START_SCORE_DIVISOR: f64 = 10_000.0;
const SA_END_SCORE_DIVISOR: f64 = 1_000_000.0;
const USE_SCORE_SCALED_SA_TEMPERATURE: bool = true;
const FIXED_SA_START_TEMP: f64 = 10.0;
const FIXED_SA_END_TEMP: f64 = 0.01;
const METROPOLIS_LOG_TABLE_SIZE: usize = 1 << 14;
const SA_CONTRIBUTION_SQ_BONUS: f64 = 2.0;
const SA_CYCLES: usize = 3;
const SINGLE_CYCLE_MIN_CELLS: usize = 721;
const SA_TIME_CHECK_MASK: usize = 255;
const DIFFERENTIAL_MIN_W: usize = 5;
const ENABLE_SA_TRIANGLE: bool = false;
const ENABLE_FINAL_TRIANGLE: bool = false;
const ENABLE_FINAL_RHOMBUS: bool = false;
// 0: current Metropolis moves, 1: disable random rotations, 2: allow only delta-k=0.
const RANDOM_ROTATION_MODE: u8 = 0;
const EXPECTED_ROUTE_INTERCEPT: f64 = -0.357_883_3;
const EXPECTED_ROUTE_SLOPE: f64 = 1.450_421_7;
const FINAL_MOVES_FROM_CONSTRUCTION_INTERCEPT: f64 = -14.174_81;
const FINAL_MOVES_FROM_N_COEFF: f64 = 5.926_529;
const FINAL_MOVES_FROM_CONSTRUCTION_COEFF: f64 = 0.556_145;
const FINAL_MOVES_FROM_N_CONSTRUCTION_COEFF: f64 = 0.011_909;
const BEAM_MOVE_MATURITY_RATIO: f64 = 2.0 / 3.0;
const ESTIMATED_FULL_BONUS_PATHS: usize = 2;
const CONNECTION_TARGET_COMBINATION_RADIUS: usize = 2;
const SMALL_TRIANGLE_INTERVAL_MS: u64 = 180;
const SMALL_TRIANGLE_BUDGET_MS: u64 = 2;
const POSTPROCESS_LIMIT_MS: u64 = 450;
const ALL_ORIENTATIONS: u8 = (1 << 6) - 1;

struct Scanner {
    input: io::Stdin,
    tokens: VecDeque<String>,
}

impl Scanner {
    fn new() -> Self {
        Self {
            input: io::stdin(),
            tokens: VecDeque::new(),
        }
    }
    fn next<T: FromStr>(&mut self) -> T {
        loop {
            if let Some(s) = self.tokens.pop_front() {
                return s.parse().ok().expect("invalid input token");
            }
            let mut line = String::new();
            assert!(
                self.input.read_line(&mut line).unwrap() > 0,
                "unexpected EOF"
            );
            self.tokens
                .extend(line.split_whitespace().map(str::to_owned));
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

impl Stats {
    fn quality(self) -> (i64, usize, i64, Reverse<i32>) {
        (self.score, self.matched, self.total, Reverse(self.moves))
    }
}

#[derive(Clone)]
struct Route {
    // (cell, representative orientation, remaining orientation domain)
    tiles: Vec<(usize, u8, u8)>,
    length: usize,
    bonuses: usize,
}

#[derive(Clone)]
struct DeferredRouteChoice {
    layer: usize,
    shortest_length: usize,
    routes: Vec<Route>,
}

#[derive(Clone)]
struct Node {
    cell: usize,
    enter: usize,
    placed_cell: usize,
    parent: usize,
    orientation: u8,
    domain: u8,
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
    exit_stamp: Vec<u32>,
    exit_epoch: u32,
}

struct ReverseBfsScratch {
    distance: Vec<usize>,
    stamp: Vec<u32>,
    epoch: u32,
    queue: Vec<usize>,
}

struct SafetyScratch {
    globally_seen: Vec<u32>,
    local_step: Vec<usize>,
    local_stamp: Vec<u32>,
    epoch: u32,
    touched: Vec<usize>,
}

#[derive(Clone, Copy)]
struct CompactMetrics {
    energy: i64,
    matched: usize,
    total_value: i64,
    representative_value: i64,
    compressible_length: usize,
    unmatched_length: usize,
    moves: i32,
}

#[derive(Clone)]
struct MultiTileChoice {
    cells: [usize; 3],
    variants: [[u8; 3]; 2],
    target_pair: [usize; 2],
}

struct DifferentialEval {
    contribution: Vec<i64>,
    cell_masks: Vec<u128>,
    pair_cells: Vec<Vec<usize>>,
    contribution_sq_sum: i64,
}

impl EvalScratch {
    fn new(cells: usize) -> Self {
        Self {
            bonus_stamp: vec![0; cells],
            epoch: 0,
            exit_stamp: Vec::new(),
            exit_epoch: 0,
        }
    }
    fn next_epoch(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.bonus_stamp.fill(0);
            self.epoch = 1;
        }
        self.epoch
    }

    fn next_exit_epoch(&mut self, exits: usize) -> u32 {
        if self.exit_stamp.len() < exits {
            self.exit_stamp.resize(exits, 0);
        }
        self.exit_epoch = self.exit_epoch.wrapping_add(1);
        if self.exit_epoch == 0 {
            self.exit_stamp.fill(0);
            self.exit_epoch = 1;
        }
        self.exit_epoch
    }
}

impl ReverseBfsScratch {
    fn new(states: usize) -> Self {
        Self {
            distance: vec![0; states],
            stamp: vec![0; states],
            epoch: 0,
            queue: Vec::with_capacity(states),
        }
    }

    fn begin(&mut self, states: usize) -> u32 {
        if self.distance.len() < states {
            self.distance.resize(states, 0);
            self.stamp.resize(states, 0);
        }
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.stamp.fill(0);
            self.epoch = 1;
        }
        self.queue.clear();
        self.epoch
    }

    fn reached(&self, state: usize, epoch: u32) -> bool {
        self.stamp[state] == epoch
    }
}

thread_local! {
    static ROUTE_REVERSE_SCRATCH: RefCell<ReverseBfsScratch> =
        RefCell::new(ReverseBfsScratch::new(0));
}

impl SafetyScratch {
    fn new(states: usize) -> Self {
        Self {
            globally_seen: vec![0; states],
            local_step: vec![0; states],
            local_stamp: vec![0; states],
            epoch: 0,
            touched: Vec::with_capacity(states),
        }
    }

    fn begin(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.globally_seen.fill(0);
            self.local_stamp.fill(0);
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
    partner: Vec<usize>,
    pair_id_by_exit: Vec<usize>,
    transition: Vec<u16>,
    neighbors: Vec<[usize; 6]>,
    domain_rotation: Vec<[i32; 64]>,
    boundary_depth: Vec<usize>,
    valid_cells: Vec<usize>,
    valid_count: usize,
}

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 7;
        self.0 ^= self.0 >> 9;
        self.0
    }
    fn usize(&mut self, n: usize) -> usize {
        self.next() as usize % n
    }
}

const fn neg_ln_const(mut x: f64) -> f64 {
    const LN_2: f64 = 0.6931471805599453;
    let mut shifts = 0usize;
    while x < 0.5 {
        x *= 2.0;
        shifts += 1;
    }
    let z = (x - 1.0) / (x + 1.0);
    let z2 = z * z;
    let mut power = z;
    let mut sum = 0.0;
    let mut denominator = 1usize;
    while denominator <= 25 {
        sum += power / denominator as f64;
        power *= z2;
        denominator += 2;
    }
    shifts as f64 * LN_2 - 2.0 * sum
}

const fn build_metropolis_log_table() -> [f32; METROPOLIS_LOG_TABLE_SIZE] {
    let mut table = [0.0f32; METROPOLIS_LOG_TABLE_SIZE];
    let mut i = 0usize;
    while i < METROPOLIS_LOG_TABLE_SIZE {
        let unit = (i as f64 + 0.5) / METROPOLIS_LOG_TABLE_SIZE as f64;
        table[i] = neg_ln_const(unit) as f32;
        i += 1;
    }
    table
}

const METROPOLIS_LOG_TABLE: [f32; METROPOLIS_LOG_TABLE_SIZE] =
    build_metropolis_log_table();

#[inline]
fn metropolis_accept(rng: &mut Rng, delta: f64, temperature: f64) -> bool {
    if delta >= 0.0 {
        return true;
    }
    let index = (rng.next() >> 50) as usize & (METROPOLIS_LOG_TABLE_SIZE - 1);
    let threshold = METROPOLIS_LOG_TABLE[index] as f64;
    delta + temperature * threshold > 0.0
}

const fn paired_dir(o: u8, enter: usize) -> usize {
    const TABLE: [[usize; 6]; 6] = [
        [1, 0, 4, 5, 2, 3],
        [4, 2, 1, 5, 0, 3],
        [4, 5, 3, 2, 0, 1],
        [2, 5, 0, 4, 3, 1],
        [2, 3, 0, 1, 5, 4],
        [5, 3, 4, 1, 2, 0],
    ];
    TABLE[o as usize][enter]
}

const fn build_domain_predecessor_enters() -> [[u8; 6]; 64] {
    let mut table = [[0u8; 6]; 64];
    let mut domain = 0usize;
    while domain < 64 {
        let mut orientation = 0u8;
        while orientation < 6 {
            if domain >> orientation & 1 != 0 {
                let mut enter = 0usize;
                while enter < 6 {
                    let out = paired_dir(orientation, enter);
                    table[domain][out] |= 1 << enter;
                    enter += 1;
                }
            }
            orientation += 1;
        }
        domain += 1;
    }
    table
}

const DOMAIN_PREDECESSOR_ENTERS: [[u8; 6]; 64] = build_domain_predecessor_enters();

const fn build_domain_out_orientations() -> [[[u8; 6]; 6]; 64] {
    let mut table = [[[0u8; 6]; 6]; 64];
    let mut domain = 0usize;
    while domain < 64 {
        let mut enter = 0usize;
        while enter < 6 {
            let mut orientation = 0u8;
            while orientation < 6 {
                if domain >> orientation & 1 != 0 {
                    let out = paired_dir(orientation, enter);
                    table[domain][enter][out] |= 1 << orientation;
                }
                orientation += 1;
            }
            enter += 1;
        }
        domain += 1;
    }
    table
}

const DOMAIN_OUT_ORIENTATIONS: [[[u8; 6]; 6]; 64] = build_domain_out_orientations();

const fn build_domain_port_components() -> [[u8; 6]; 64] {
    let mut table = [[0u8; 6]; 64];
    let mut domain = 0usize;
    while domain < 64 {
        let mut parent = [0u8, 1, 2, 3, 4, 5];
        let mut orientation = 0u8;
        while orientation < 6 {
            if domain >> orientation & 1 != 0 {
                let mut enter = 0usize;
                while enter < 6 {
                    let mut a = enter as u8;
                    while parent[a as usize] != a {
                        a = parent[a as usize];
                    }
                    let mut b = paired_dir(orientation, enter) as u8;
                    while parent[b as usize] != b {
                        b = parent[b as usize];
                    }
                    if a != b {
                        parent[b as usize] = a;
                    }
                    enter += 1;
                }
            }
            orientation += 1;
        }
        let mut side = 0usize;
        while side < 6 {
            let mut root = side as u8;
            while parent[root as usize] != root {
                root = parent[root as usize];
            }
            table[domain][side] = root;
            side += 1;
        }
        domain += 1;
    }
    table
}

const DOMAIN_PORT_COMPONENTS: [[u8; 6]; 64] = build_domain_port_components();

const fn rotation_cost(from: u8, to: u8) -> i32 {
    const TABLE: [[i32; 6]; 6] = [
        [0, 1, 2, 3, 2, 1],
        [1, 0, 1, 2, 3, 2],
        [2, 1, 0, 1, 2, 3],
        [3, 2, 1, 0, 1, 2],
        [2, 3, 2, 1, 0, 1],
        [1, 2, 3, 2, 1, 0],
    ];
    TABLE[from as usize][to as usize]
}

const fn build_best_domain_orientations() -> [[[u8; 64]; 6]; 6] {
    let mut table = [[[255u8; 64]; 6]; 6];
    let mut initial = 0u8;
    while initial < 6 {
        let mut base = 0u8;
        while base < 6 {
            let mut domain = 1usize;
            while domain < 64 {
                let mut best_orientation = 255u8;
                let mut best_cost = i32::MAX;
                let mut orientation = 0u8;
                while orientation < 6 {
                    if domain >> orientation & 1 != 0 {
                        let cost = rotation_cost(initial, orientation)
                            + if orientation == base { 0 } else { 1 };
                        if cost < best_cost {
                            best_cost = cost;
                            best_orientation = orientation;
                        }
                    }
                    orientation += 1;
                }
                table[initial as usize][base as usize][domain] = best_orientation;
                domain += 1;
            }
            base += 1;
        }
        initial += 1;
    }
    table
}

const BEST_DOMAIN_ORIENTATION: [[[u8; 64]; 6]; 6] = build_best_domain_orientations();

fn hex_cell_distance(width: usize, a: usize, b: usize) -> usize {
    let dr = a as isize / width as isize - b as isize / width as isize;
    let dc = a as isize % width as isize - b as isize % width as isize;
    dr.unsigned_abs()
        .max(dc.unsigned_abs())
        .max((dr + dc).unsigned_abs())
}

impl Board {
    fn next(&self, cell: usize, side: usize) -> Option<(usize, usize)> {
        let next = self.neighbors[cell][side];
        (next != usize::MAX).then_some((next, (side + 3) % 6))
    }

    fn trace_with_scratch(
        &self,
        orientation: &[u8],
        start: usize,
        scratch: &mut EvalScratch,
    ) -> (usize, usize, usize) {
        let (cell, enter) = self.exits[start];
        let mut state = cell * 6 + enter;
        let terminal_base = self.valid.len() * 6;
        let mut length = 0usize;
        let mut bonuses = 0usize;
        let epoch = scratch.next_epoch();
        // A port belongs to exactly one path. More than 3*tiles steps means a bug/cycle.
        for _ in 0..=3 * self.valid_count {
            length += 1;
            let cell = state / 6;
            if self.bonus[cell] && scratch.bonus_stamp[cell] != epoch {
                bonuses += 1;
                scratch.bonus_stamp[cell] = epoch;
            }
            let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                return (next - terminal_base, length, bonuses);
            }
            state = next;
        }
        (usize::MAX, length, bonuses)
    }

    fn trace_end(&self, orientation: &[u8], start: usize) -> usize {
        let (cell, enter) = self.exits[start];
        let mut state = cell * 6 + enter;
        let terminal_base = self.valid.len() * 6;
        for _ in 0..=3 * self.valid_count {
            let cell = state / 6;
            let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                return next - terminal_base;
            }
            state = next;
        }
        usize::MAX
    }

    fn alternating_cycles(&self, orientation: &[u8]) -> usize {
        let mut parent: Vec<usize> = (0..self.exits.len()).collect();
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
            if a != b {
                parent[b] = a;
            }
        }
        for pair in &self.pairs {
            join(&mut parent, pair[0], pair[1]);
        }
        for exit in 0..self.exits.len() {
            let end = self.trace_end(orientation, exit);
            if end != usize::MAX {
                join(&mut parent, exit, end);
            }
        }
        (0..self.exits.len())
            .filter(|&exit| root(&mut parent, exit) == exit)
            .count()
    }

    fn trace_exit_cells(&self, orientation: &[u8], start: usize, cells: &mut Vec<usize>) {
        cells.clear();
        let (cell, enter) = self.exits[start];
        let mut state = cell * 6 + enter;
        let terminal_base = self.valid.len() * 6;
        for _ in 0..=3 * self.valid_count {
            let cell = state / 6;
            cells.push(cell);
            let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                break;
            }
            state = next;
        }
    }

    fn evaluate(&self, orientation: &[u8]) -> Stats {
        let mut scratch = EvalScratch::new(self.valid.len());
        self.evaluate_with_scratch(orientation, &mut scratch)
    }

    fn evaluate_with_scratch(&self, orientation: &[u8], scratch: &mut EvalScratch) -> Stats {
        let mut moves = 0;
        for &cell in &self.valid_cells {
            moves += rotation_cost(self.initial[cell], orientation[cell]);
        }
        self.evaluate_with_moves(orientation, moves, scratch)
    }

    fn evaluate_with_moves(
        &self,
        orientation: &[u8],
        moves: i32,
        scratch: &mut EvalScratch,
    ) -> Stats {
        let mut s = Stats {
            moves,
            ..Stats::default()
        };
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
                let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
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
        &self,
        orientation: &[u8],
        id: usize,
        scratch: &mut EvalScratch,
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
            if let Some(path) = cells.as_deref_mut() {
                path.push(cell);
            }
            if self.bonus[cell] && scratch.bonus_stamp[cell] != epoch {
                scratch.bonus_stamp[cell] = epoch;
                bonuses += 1;
            }
            let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                return if next - terminal_base == pair[1] {
                    ((len * (bonuses + 1)) as i64, len as i64)
                } else {
                    (0, 0)
                };
            }
            state = next;
        }
        (0, 0)
    }

    fn damage_model(&self, orientation: &[u8]) -> DamageModel {
        let mut cell_masks = vec![0u128; self.valid.len()];
        let mut contributions = vec![0i64; self.pairs.len()];
        let mut scratch = EvalScratch::new(self.valid.len());
        let mut route_cells = Vec::new();
        for id in 0..self.pairs.len() {
            route_cells.clear();
            let (value, _) = self.trace_pair(
                orientation,
                id,
                &mut scratch,
                Some(&mut route_cells),
            );
            if value == 0 {
                continue;
            }
            contributions[id] = value;
            for &cell in &route_cells {
                cell_masks[cell] |= 1u128 << id;
            }
        }
        let base = self.evaluate_with_scratch(orientation, &mut scratch);
        DamageModel {
            cell_masks,
            contributions,
            base,
        }
    }

    fn tester_safe(&self, orientation: &[u8]) -> bool {
        let ports = self.valid.len() * 6;
        let mut scratch = SafetyScratch::new(ports);
        self.tester_safe_with_scratch(orientation, &mut scratch)
    }

    fn tester_safe_with_scratch(&self, orientation: &[u8], scratch: &mut SafetyScratch) -> bool {
        let ports = self.valid.len() * 6;
        let epoch = scratch.begin();
        for start in 0..ports {
            if !self.valid[start / 6] || scratch.globally_seen[start] == epoch {
                continue;
            }
            scratch.touched.clear();
            let mut state = start;
            let mut step = 0usize;
            loop {
                if scratch.globally_seen[state] == epoch {
                    break;
                }
                if scratch.local_stamp[state] == epoch {
                    let began = scratch.local_step[state];
                    if step - began > 400 {
                        return false;
                    }
                    break;
                }
                scratch.local_stamp[state] = epoch;
                scratch.local_step[state] = step;
                scratch.touched.push(state);
                step += 1;
                let cell = state / 6;
                let enter = state % 6;
                let out = paired_dir(orientation[cell], enter);
                let Some((next, next_enter)) = self.next(cell, out) else {
                    break;
                };
                state = next * 6 + next_enter;
            }
            for &state in &scratch.touched {
                scratch.globally_seen[state] = epoch;
            }
        }
        true
    }

    fn tester_safe_after_cell_change(
        &self,
        orientation: &[u8],
        changed_cell: usize,
        scratch: &mut SafetyScratch,
    ) -> bool {
        let terminal_base = self.valid.len() * 6;
        // The previous board is already safe.  A newly created cycle must use
        // one of the six transitions of the only changed tile, so checking the
        // six components through that tile is sufficient.
        for enter in 0..6 {
            let epoch = scratch.begin();
            let mut state = changed_cell * 6 + enter;
            let mut step = 0usize;
            loop {
                if scratch.local_stamp[state] == epoch {
                    if step - scratch.local_step[state] > 400 {
                        return false;
                    }
                    break;
                }
                scratch.local_stamp[state] = epoch;
                scratch.local_step[state] = step;
                step += 1;
                let cell = state / 6;
                let next = self.transition[state * 6 + orientation[cell] as usize] as usize;
                if next >= terminal_base {
                    break;
                }
                state = next;
            }
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
        let mut contribution_sq_sum = 0i64;
        for id in 0..board.pairs.len() {
            (contribution[id], _) =
                board.trace_pair(orientation, id, scratch, Some(&mut pair_cells[id]));
            if contribution[id] > 0 {
                contribution_sq_sum += contribution[id] * contribution[id];
            }
            for &cell in &pair_cells[id] {
                cell_masks[cell] |= 1u128 << id;
            }
        }
        Self {
            contribution,
            cell_masks,
            pair_cells,
            contribution_sq_sum,
        }
    }

    fn proposal_with_sq_sum(
        &self,
        board: &Board,
        orientation: &[u8],
        current: Stats,
        moves: i32,
        affected: u128,
        scratch: &mut EvalScratch,
        updates: &mut Vec<(usize, i64)>,
    ) -> (Stats, i64) {
        let mut next = Stats {
            moves,
            matched: current.matched,
            total: current.total,
            score: 0,
        };
        updates.clear();
        let mut next_sq_sum = self.contribution_sq_sum;
        let mut remaining = affected;
        while remaining != 0 {
            let id = remaining.trailing_zeros() as usize;
            remaining &= remaining - 1;
            let old = self.contribution[id];
            let (new, _) = board.trace_pair(orientation, id, scratch, None);
            if old > 0 {
                next.matched -= 1;
                next.total -= old;
                next_sq_sum -= old * old;
            }
            if new > 0 {
                next.matched += 1;
                next.total += new;
                next_sq_sum += new * new;
            }
            updates.push((id, new));
        }
        next.score = (next.matched as i64 * (next.total - board.M as i64 * moves as i64)).max(0);

        (next, next_sq_sum)
    }

    fn proposal(
        &self,
        board: &Board,
        orientation: &[u8],
        current: Stats,
        moves: i32,
        affected: u128,
        scratch: &mut EvalScratch,
        updates: &mut Vec<(usize, i64)>,
    ) -> Stats {
        let mut next = Stats {
            moves,
            matched: current.matched,
            total: current.total,
            score: 0,
        };
        updates.clear();
        let mut remaining = affected;
        while remaining != 0 {
            let id = remaining.trailing_zeros() as usize;
            remaining &= remaining - 1;
            let old = self.contribution[id];
            let (new, _) = board.trace_pair(orientation, id, scratch, None);
            if old > 0 {
                next.matched -= 1;
                next.total -= old;
            }
            if new > 0 {
                next.matched += 1;
                next.total += new;
            }
            updates.push((id, new));
        }
        next.score = (next.matched as i64 * (next.total - board.M as i64 * moves as i64)).max(0);
        next
    }

    fn commit(
        &mut self,
        board: &Board,
        orientation: &[u8],
        scratch: &mut EvalScratch,
        updates: &[(usize, i64)],
        route_cells: &mut Vec<usize>,
    ) {
        for &(id, value) in updates {
            let old_value = self.contribution[id];
            if old_value > 0 {
                self.contribution_sq_sum -= old_value * old_value;
            }
            let bit = 1u128 << id;
            for &cell in &self.pair_cells[id] {
                self.cell_masks[cell] &= !bit;
            }
            route_cells.clear();
            board.trace_pair(orientation, id, scratch, Some(route_cells));
            self.pair_cells[id].clear();
            self.pair_cells[id].extend_from_slice(route_cells);
            for &cell in &self.pair_cells[id] {
                self.cell_masks[cell] |= bit;
            }
            self.contribution[id] = value;
            if value > 0 {
                self.contribution_sq_sum += value * value;
            }
        }
    }
}

fn bit_test(bits: &[u64], cell: usize) -> bool {
    bits[cell >> 6] >> (cell & 63) & 1 != 0
}

fn bit_set(bits: &mut [u64], cell: usize) {
    bits[cell >> 6] |= 1u64 << (cell & 63);
}

fn best_orientation_in_domain(board: &Board, base: &[u8], cell: usize, domain: u8) -> (u8, i32) {
    let orientation = BEST_DOMAIN_ORIENTATION[board.initial[cell] as usize][base[cell] as usize]
        [domain as usize];
    assert!(orientation != 255, "empty orientation domain");
    let cost = rotation_cost(board.initial[cell], orientation)
        + if orientation == base[cell] { 0 } else { 1 };
    (orientation, cost)
}

fn orientation_choices(
    board: &Board,
    domains: &[u8],
    base: &[u8],
    cell: usize,
    enter: usize,
    previous_domain: Option<u8>,
) -> ([(usize, u8, u8); 6], usize) {
    let available = domains[cell] & previous_domain.unwrap_or(ALL_ORIENTATIONS);
    let masks = DOMAIN_OUT_ORIENTATIONS[available as usize][enter];
    let mut choices = [(0usize, 0u8, 0u8); 6];
    let mut len = 0usize;
    for (out, domain) in IntoIterator::into_iter(masks).enumerate() {
        if domain != 0 {
            let (o, _) = best_orientation_in_domain(board, base, cell, domain);
            choices[len] = (out, o, domain);
            len += 1;
        }
    }
    (choices, len)
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
    board: &Board,
    node: &Node,
    target_cell: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
) -> i64 {
    let heuristic = hex_cell_distance(board.W, node.cell, target_cell) as i64;
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
        } else {
            0
        };
        (if damage.is_some() {
            40 * predicted_gain + 80 * intrinsic
        } else {
            180 * intrinsic
        }) - 12 * board.M as i64 * node.rotations as i64
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

fn reverse_route_distances(
    board: &Board,
    fixed: &[u8],
    source_cell: usize,
    target_cell: usize,
    target_out: usize,
    depth_limit: Option<usize>,
    protect_outer_bonus: bool,
    scratch: &mut ReverseBfsScratch,
) -> u32 {
    let epoch = scratch.begin(board.valid.len() * 6);
    if depth_limit.is_some_and(|limit| board.boundary_depth[target_cell] > limit) {
        return epoch;
    }
    let mut target_enters =
        DOMAIN_PREDECESSOR_ENTERS[fixed[target_cell] as usize][target_out];
    while target_enters != 0 {
        let enter = target_enters.trailing_zeros() as usize;
        target_enters &= target_enters - 1;
        {
            let state = target_cell * 6 + enter;
            scratch.stamp[state] = epoch;
            scratch.distance[state] = 1;
            scratch.queue.push(state);
        }
    }
    let mut head = 0usize;
    while head < scratch.queue.len() {
        let state = scratch.queue[head];
        head += 1;
        let cell = state / 6;
        let enter = state % 6;
        let Some((previous_cell, previous_out)) = board.next(cell, enter) else {
            continue;
        };
        if protect_outer_bonus
            && previous_cell != source_cell
            && previous_cell != target_cell
            && board.bonus[previous_cell]
            && board.boundary_depth[previous_cell] == 0
        {
            continue;
        }
        if depth_limit.is_some_and(|limit| board.boundary_depth[previous_cell] > limit) {
            continue;
        }
        let mut previous_enters =
            DOMAIN_PREDECESSOR_ENTERS[fixed[previous_cell] as usize][previous_out];
        while previous_enters != 0 {
            let previous_enter = previous_enters.trailing_zeros() as usize;
            previous_enters &= previous_enters - 1;
            let previous_state = previous_cell * 6 + previous_enter;
            if scratch.stamp[previous_state] != epoch {
                scratch.stamp[previous_state] = epoch;
                scratch.distance[previous_state] = scratch.distance[state] + 1;
                scratch.queue.push(previous_state);
            }
        }
    }
    epoch
}

fn reconstruct(arena: &[Node], mut id: usize) -> Route {
    let last = &arena[id];
    let mut tiles = Vec::with_capacity(last.length);
    loop {
        let n = &arena[id];
        if n.parent == usize::MAX {
            break;
        }
        tiles.push((n.placed_cell, n.orientation, n.domain));
        id = n.parent;
    }
    tiles.reverse();
    Route {
        tiles,
        length: last.length,
        bonuses: last.bonuses,
    }
}

fn route_repeats_cell(route: &Route) -> bool {
    route.tiles.iter().enumerate().any(|(i, &(cell, _, _))| {
        route.tiles[..i]
            .iter()
            .any(|&(previous, _, _)| previous == cell)
    })
}

fn assigned_domain(arena: &[Node], mut id: usize, cell: usize) -> Option<u8> {
    loop {
        let node = &arena[id];
        if node.placed_cell == cell {
            return Some(node.domain);
        }
        if node.parent == usize::MAX {
            return None;
        }
        id = node.parent;
    }
}

fn find_routes_between_ports_with_reverse_scratch(
    board: &Board,
    base: &[u8],
    fixed: &[u8],
    start_cell: usize,
    start_side: usize,
    target_cell: usize,
    target_out: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
    depth_limit: Option<usize>,
    deadline: Instant,
    candidate_limit: usize,
    reverse_scratch: &mut ReverseBfsScratch,
) -> Vec<Route> {
    if Instant::now() >= deadline {
        return Vec::new();
    }
    let allow_short_detours = ENABLE_SHORT_ROUTE_DETOURS
        && !special
        && candidate_limit > 1
        && hex_cell_distance(board.W, start_cell, target_cell) <= NORMAL_ROUTE_DETOUR_MAX_DISTANCE;
    let n = (board.W + 1) / 2;
    let port_revisit = special && n <= 13;
    let protect_outer_bonus = PROTECT_OUTER_BONUS_FROM_ORDINARY && !special;
    let reverse_epoch = (ENABLE_REVERSE_ROUTE_BFS && !special)
        .then(|| {
            reverse_route_distances(
            board,
            fixed,
            start_cell,
            target_cell,
            target_out,
                depth_limit,
                protect_outer_bonus,
                reverse_scratch,
            )
        });
    if reverse_epoch
        .is_some_and(|epoch| !reverse_scratch.reached(start_cell * 6 + start_side, epoch))
    {
        return Vec::new();
    }
    let exact_shortest = reverse_epoch.is_some() && !allow_short_detours;
    let track_seen = !exact_shortest;
    let words = if track_seen {
        (board.valid.len() * if port_revisit { 6 } else { 1 } + 63) / 64
    } else {
        0
    };
    let root = Node {
        cell: start_cell,
        enter: start_side,
        placed_cell: usize::MAX,
        parent: usize::MAX,
        orientation: 255,
        domain: 0,
        length: 0,
        bonuses: 0,
        rotations: 0,
        depth_sum: 0,
        seen: vec![0; words],
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
    } else {
        5 * board.W + 20
    };

    let mut first_goal_depth = None;
    for depth in 0..max_len {
        if beam.is_empty() || Instant::now() >= deadline {
            break;
        }
        let mut next_beam = Vec::with_capacity(beam_width * 3);
        for &id in &beam {
            let p = &arena[id];
            let (cell, enter, length, bonuses, rotations, depth_sum, damaged) = (
                p.cell,
                p.enter,
                p.length,
                p.bonuses,
                p.rotations,
                p.depth_sum,
                p.damaged,
            );
            if protect_outer_bonus
                && cell != start_cell
                && cell != target_cell
                && board.bonus[cell]
                && board.boundary_depth[cell] == 0
            {
                continue;
            }
            if depth_limit.is_some_and(|limit| board.boundary_depth[cell] > limit) {
                continue;
            }
            let enter_key = if port_revisit { cell * 6 + enter } else { cell };
            if track_seen && bit_test(&p.seen, enter_key) {
                continue;
            }
            let mut seen_base = p.seen.clone();
            if track_seen {
                bit_set(&mut seen_base, enter_key);
            }
            let previous_domain = port_revisit
                .then(|| assigned_domain(&arena, id, cell))
                .flatten();
            let (choices, choice_count) =
                orientation_choices(board, fixed, base, cell, enter, previous_domain);
            for (choice_id, (out, o, domain)) in choices[..choice_count].iter().copied().enumerate()
            {
                let mut seen = if choice_id + 1 == choice_count {
                    std::mem::take(&mut seen_base)
                } else {
                    seen_base.clone()
                };
                if track_seen && port_revisit {
                    bit_set(&mut seen, cell * 6 + out);
                }
                let node = Node {
                    cell,
                    enter,
                    placed_cell: cell,
                    parent: id,
                    orientation: o,
                    domain,
                    length: length + 1,
                    bonuses: bonuses + usize::from(previous_domain.is_none() && board.bonus[cell]),
                    rotations: rotations
                        + if let Some(previous) = previous_domain {
                            board.domain_rotation[cell][domain as usize]
                                - board.domain_rotation[cell][previous as usize]
                        } else {
                            board.domain_rotation[cell][domain as usize]
                        },
                    depth_sum: depth_sum + board.boundary_depth[cell],
                    damaged: damaged
                        | if domain >> base[cell] & 1 == 0 {
                            damage.map_or(0, |m| m.cell_masks[cell])
                        } else {
                            0
                        },
                    seen,
                };
                if cell == target_cell && out == target_out {
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
                } else if let Some((nc, ne)) = board.next(cell, out) {
                    if depth_limit.is_some_and(|limit| board.boundary_depth[nc] > limit) {
                        continue;
                    }
                    let next_key = if port_revisit { nc * 6 + ne } else { nc };
                    if track_seen && bit_test(&node.seen, next_key) {
                        continue;
                    }
                    if exact_shortest {
                        let epoch = reverse_epoch.unwrap();
                        let current_state = cell * 6 + enter;
                        let next_state = nc * 6 + ne;
                        if !reverse_scratch.reached(next_state, epoch)
                            || reverse_scratch.distance[next_state] + 1
                                != reverse_scratch.distance[current_state]
                        {
                            continue;
                        }
                    }
                    let mut child = node;
                    child.cell = nc;
                    child.enter = ne;
                    if reverse_epoch
                        .is_some_and(|epoch| !reverse_scratch.reached(nc * 6 + ne, epoch))
                    {
                        continue;
                    }
                    let nid = arena.len();
                    arena.push(child);
                    next_beam.push(nid);
                }
            }
        }
        next_beam.sort_unstable_by_key(|&id| {
            Reverse(route_rank(
                board,
                &arena[id],
                target_cell,
                width,
                special,
                damage,
            ))
        });
        next_beam.truncate(beam_width);
        beam = next_beam;
        if !special && !goals.is_empty() {
            let first = *first_goal_depth.get_or_insert(depth);
            if !allow_short_detours || depth >= first + NORMAL_ROUTE_DETOUR_STEPS {
                break;
            }
        }
    }
    goals.sort_unstable_by_key(|&(value, _)| Reverse(value));
    let mut ranked_routes: Vec<(i64, Route)> = Vec::with_capacity(goals.len());
    for (value, id) in goals {
        let route = reconstruct(&arena, id);
        if exact_shortest && route_repeats_cell(&route) {
            continue;
        }
        if ranked_routes
            .iter()
            .any(|(_, old)| old.tiles == route.tiles)
        {
            continue;
        }
        ranked_routes.push((value, route));
    }
    let mut routes: Vec<Route> = Vec::with_capacity(candidate_limit);
    if allow_short_detours {
        if let Some(min_length) = ranked_routes.iter().map(|(_, route)| route.length).min() {
            for length in min_length..=min_length + NORMAL_ROUTE_DETOUR_STEPS {
                if let Some((_, route)) = ranked_routes
                    .iter()
                    .find(|(_, route)| route.length == length)
                {
                    routes.push(route.clone());
                    if routes.len() >= candidate_limit {
                        return routes;
                    }
                }
            }
        }
    }
    for (_, route) in ranked_routes {
        if routes.iter().any(|old| old.tiles == route.tiles) {
            continue;
        }
        routes.push(route);
        if routes.len() >= candidate_limit {
            break;
        }
    }
    routes
}

fn find_routes_with_reverse_scratch(
    board: &Board,
    base: &[u8],
    fixed: &[u8],
    source: usize,
    target: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
    depth_limit: Option<usize>,
    deadline: Instant,
    candidate_limit: usize,
    reverse_scratch: &mut ReverseBfsScratch,
) -> Vec<Route> {
    let (start_cell, start_side) = board.exits[source];
    let (target_cell, target_out) = board.exits[target];
    find_routes_between_ports_with_reverse_scratch(
        board,
        base,
        fixed,
        start_cell,
        start_side,
        target_cell,
        target_out,
        width,
        special,
        damage,
        depth_limit,
        deadline,
        candidate_limit,
        reverse_scratch,
    )
}

fn find_routes(
    board: &Board,
    base: &[u8],
    fixed: &[u8],
    source: usize,
    target: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
    depth_limit: Option<usize>,
    deadline: Instant,
    candidate_limit: usize,
) -> Vec<Route> {
    ROUTE_REVERSE_SCRATCH.with(|scratch| {
        find_routes_with_reverse_scratch(
            board,
            base,
            fixed,
            source,
            target,
            width,
            special,
            damage,
            depth_limit,
            deadline,
            candidate_limit,
            &mut scratch.borrow_mut(),
        )
    })
}

fn find_segment_route(
    board: &Board,
    base: &[u8],
    fixed: &[u8],
    start: (usize, usize),
    target: (usize, usize),
    deadline: Instant,
) -> Option<Route> {
    ROUTE_REVERSE_SCRATCH.with(|scratch| {
        find_routes_between_ports_with_reverse_scratch(
            board,
            base,
            fixed,
            start.0,
            start.1,
            target.0,
            target.1,
            OUTER_LAYERS,
            false,
            None,
            None,
            deadline,
            1,
            &mut scratch.borrow_mut(),
        )
        .into_iter()
        .next()
    })
}

fn find_route(
    board: &Board,
    base: &[u8],
    fixed: &[u8],
    source: usize,
    target: usize,
    width: usize,
    special: bool,
    damage: Option<&DamageModel>,
    depth_limit: Option<usize>,
    deadline: Instant,
) -> Option<Route> {
    find_routes(
        board,
        base,
        fixed,
        source,
        target,
        width,
        special,
        damage,
        depth_limit,
        deadline,
        1,
    )
    .into_iter()
    .next()
}

fn apply_route(orientation: &mut [u8], domains: &mut [u8], route: &Route, keep_domain: bool) {
    for &(cell, o, required_domain) in &route.tiles {
        orientation[cell] = o;
        if keep_domain {
            domains[cell] &= required_domain;
            debug_assert!(domains[cell] != 0 && domains[cell] >> o & 1 != 0);
        } else {
            domains[cell] = 1 << o;
        }
    }
}

fn intersect_route_domains(domains: &mut [u8], route: &Route) -> bool {
    if route
        .tiles
        .iter()
        .any(|&(cell, _, required_domain)| domains[cell] & required_domain == 0)
    {
        return false;
    }
    for &(cell, _, required_domain) in &route.tiles {
        domains[cell] &= required_domain;
    }
    true
}

fn deferred_route_selections(
    fixed: &[u8],
    choices: &[DeferredRouteChoice],
    limit: usize,
) -> Vec<Vec<usize>> {
    fn dfs(
        choice_id: usize,
        choices: &[DeferredRouteChoice],
        domains: Vec<u8>,
        current: &mut Vec<usize>,
        results: &mut Vec<Vec<usize>>,
        limit: usize,
    ) {
        if results.len() >= limit {
            return;
        }
        if choice_id == choices.len() {
            results.push(current.clone());
            return;
        }
        for (route_id, route) in choices[choice_id].routes.iter().enumerate() {
            let mut next_domains = domains.clone();
            if !intersect_route_domains(&mut next_domains, route) {
                continue;
            }
            current.push(route_id);
            dfs(
                choice_id + 1,
                choices,
                next_domains,
                current,
                results,
                limit,
            );
            current.pop();
            if results.len() >= limit {
                break;
            }
        }
    }

    let mut results = Vec::new();
    dfs(
        0,
        choices,
        fixed.to_vec(),
        &mut Vec::new(),
        &mut results,
        limit,
    );
    results
}

fn resolve_domains(board: &Board, orientation: &mut [u8], domains: &[u8], deadline: Instant) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
    let mut differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut updates = Vec::with_capacity(board.pairs.len());
    let mut best_updates = Vec::with_capacity(board.pairs.len());
    let mut route_cells = Vec::new();
    let mut ambiguous = 0usize;
    let mut changed = 0usize;
    for cell in 0..domains.len() {
        if Instant::now() >= deadline {
            break;
        }
        if !board.valid[cell] || domains[cell].count_ones() <= 1 {
            continue;
        }
        ambiguous += 1;
        let old = orientation[cell];
        let mut best_o = old;
        let mut best = stats;
        best_updates.clear();
        let affected = differential.cell_masks[cell];
        for o in 0..6u8 {
            if domains[cell] >> o & 1 == 0 {
                continue;
            }
            orientation[cell] = o;
            let moves = stats.moves - rotation_cost(board.initial[cell], old)
                + rotation_cost(board.initial[cell], o);
            let candidate = differential.proposal(
                board,
                orientation,
                stats,
                moves,
                affected,
                &mut scratch,
                &mut updates,
            );
            if candidate.quality() > best.quality() {
                best = candidate;
                best_o = o;
                best_updates.clone_from(&updates);
            }
        }
        orientation[cell] = best_o;
        if best_o != old {
            changed += 1;
            differential.commit(
                board,
                orientation,
                &mut scratch,
                &best_updates,
                &mut route_cells,
            );
        }
        stats = best;
    }
    eprintln!(
        "domain_resolve ambiguous={} changed={} k={} score={}",
        ambiguous, changed, stats.matched, stats.score
    );
}

fn materialize_domains_safely(board: &Board, orientation: &mut [u8], domains: &[u8]) -> bool {
    let routed = orientation.to_vec();
    for choice_rank in 0..6usize {
        orientation.clone_from_slice(&routed);
        for &cell in &board.valid_cells {
            let domain = domains[cell];
            if domain.count_ones() <= 1 {
                continue;
            }
            let mut choices: Vec<u8> = (0..6u8).filter(|&o| domain >> o & 1 != 0).collect();
            choices.sort_unstable_by_key(|&o| (rotation_cost(board.initial[cell], o), o));
            orientation[cell] = choices[choice_rank % choices.len()];
        }
        if board.tester_safe(orientation) {
            return true;
        }
    }
    orientation.clone_from_slice(&routed);
    false
}

fn pair_distance(board: &Board, pair: [usize; 2]) -> usize {
    let a = board.exits[pair[0]].0;
    let b = board.exits[pair[1]].0;
    hex_cell_distance(board.W, a, b)
}

fn expected_route_length_between_exits(board: &Board, a: usize, b: usize) -> f64 {
    let shortest =
        hex_cell_distance(board.W, board.exits[a].0, board.exits[b].0) as f64 + 1.0;
    shortest.max(EXPECTED_ROUTE_INTERCEPT + EXPECTED_ROUTE_SLOPE * shortest)
}

struct ConnectionTargetPlan {
    matched: usize,
    dropped_ids: Vec<usize>,
    rewired_pairs: Vec<[usize; 2]>,
    wrong_pairs: Vec<[usize; 2]>,
    offset: usize,
}

fn estimate_connection_target(
    board: &Board,
    construction_orientation: &[u8],
    construction_moves: i32,
    construction_archive: &[ConstructionArchiveEntry],
) -> ConnectionTargetPlan {
    let estimate_started = Instant::now();
    let mut tested_drop_combinations = 0usize;
    let pair_count = board.pairs.len();
    let n = (board.W + 1) / 2;
    let bonus_count = board.bonus.iter().filter(|&&value| value).count();
    let total_segments = 3.0 * board.valid_count as f64;
    let pair_lengths: Vec<f64> = board
        .pairs
        .iter()
        .map(|pair| expected_route_length_between_exits(board, pair[0], pair[1]))
        .collect();
    let mut trace_scratch = EvalScratch::new(board.valid.len());
    let mut drop_candidates = Vec::new();
    for id in 0..pair_count {
        let (value, length) = board.trace_pair(
            construction_orientation,
            id,
            &mut trace_scratch,
            None,
        );
        let bonuses = if value > 0 && length > 0 {
            value / length - 1
        } else {
            0
        };
        if bonuses == 0 {
            drop_candidates.push((pair_lengths[id], id));
        }
    }
    let estimated_moves = (FINAL_MOVES_FROM_CONSTRUCTION_INTERCEPT
        + FINAL_MOVES_FROM_N_COEFF * n as f64
        + FINAL_MOVES_FROM_CONSTRUCTION_COEFF * construction_moves as f64
        + FINAL_MOVES_FROM_N_CONSTRUCTION_COEFF * n as f64 * construction_moves as f64)
        .max(0.0);
    drop_candidates
        .sort_unstable_by(|a, b| b.0.total_cmp(&a.0).then_with(|| a.1.cmp(&b.1)));
    let all_correct_length: f64 = pair_lengths.iter().sum();
    let estimate_score =
        |matched: usize, correct_length: f64, wrong_length: f64, hero_shortest: f64| {
        // Retained hero pairs can be bonus trunks.  Their shortest parts are not
        // additional reservations: the remaining segments can extend those same
        // components through the bonus cells.
        let ordinary_length = (correct_length - hero_shortest).max(0.0);
        let bonus_length = (total_segments - ordinary_length - wrong_length).max(0.0);
        let total_value = ordinary_length + (bonus_count + 1) as f64 * bonus_length;
        let candidate_moves = construction_archive
            .iter()
            .find(|entry| {
                entry.stats.matched == matched
                    && entry.stats.total as f64 >= BEAM_MOVE_MATURITY_RATIO * total_value
            })
            .map_or(estimated_moves, |entry| entry.stats.moves as f64);
        let score = matched as f64 * (total_value - board.M as f64 * candidate_moves);
        (score.max(0.0), bonus_length, total_value, candidate_moves)
    };
    let (base_score, base_bonus_length, base_total, base_moves) =
        estimate_score(
            pair_count,
            all_correct_length,
            0.0,
            {
                let mut lengths = pair_lengths.clone();
                lengths.sort_unstable_by(|a, b| b.total_cmp(a));
                lengths.iter().take(ESTIMATED_FULL_BONUS_PATHS).sum()
            },
        );
    let mut best = (base_score, pair_count, 0usize, 0usize);
    let mut summaries = Vec::with_capacity(pair_count.saturating_mul(2));
    summaries.push((
        pair_count,
        0usize,
        0usize,
        0.0,
        base_bonus_length,
        base_total,
        base_moves,
        base_score,
    ));
    // First locate the promising drop count with the cheap longest-prefix
    // estimate.  The p+2 combination search below is needed only near this p.
    let mut preliminary_best = (base_score, 0usize);
    for drop_count in 2..=drop_candidates.len() {
        let ids: Vec<usize> = drop_candidates[..drop_count]
            .iter()
            .map(|entry| entry.1)
            .collect();
        let dropped_length: f64 = drop_candidates[..drop_count]
            .iter()
            .map(|entry| entry.0)
            .sum();
        let mut endpoints = Vec::with_capacity(2 * drop_count);
        for &id in &ids {
            endpoints.extend_from_slice(&board.pairs[id]);
        }
        endpoints.sort_unstable();
        let mut shortest_wrong = f64::INFINITY;
        for offset in 0..2 {
            let mut valid = true;
            let mut wrong_length = 0.0;
            for step in 0..drop_count {
                let a = endpoints[(offset + 2 * step) % endpoints.len()];
                let b = endpoints[(offset + 2 * step + 1) % endpoints.len()];
                if board.partner[a] == b {
                    valid = false;
                    break;
                }
                wrong_length += expected_route_length_between_exits(board, a, b);
            }
            if valid {
                shortest_wrong = shortest_wrong.min(wrong_length);
            }
        }
        if !shortest_wrong.is_finite() {
            continue;
        }
        let mut dropped = vec![false; pair_count];
        for &id in &ids {
            dropped[id] = true;
        }
        let mut retained_lengths: Vec<f64> = (0..pair_count)
            .filter(|&id| !dropped[id])
            .map(|id| pair_lengths[id])
            .collect();
        retained_lengths.sort_unstable_by(|a, b| b.total_cmp(a));
        let hero_shortest: f64 = retained_lengths
            .iter()
            .take(ESTIMATED_FULL_BONUS_PATHS)
            .sum();
        let (score, _, _, _) = estimate_score(
            pair_count - drop_count,
            all_correct_length - dropped_length,
            shortest_wrong,
            hero_shortest,
        );
        if score > preliminary_best.0 {
            preliminary_best = (score, drop_count);
        }
    }
    for drop_count in 1..=drop_candidates.len() {
        if drop_count < 2 {
            continue;
        }
        let exhaustive = drop_count.abs_diff(preliminary_best.1)
            <= CONNECTION_TARGET_COMBINATION_RADIUS;
        let pool_len = if exhaustive {
            (drop_count + 2).min(drop_candidates.len())
        } else {
            drop_count
        };
        let pool = &drop_candidates[..pool_len];
        let mut choice: Vec<usize> = (0..drop_count).collect();
        let mut selected: Option<(f64, f64, usize, Vec<usize>)> = None;
        loop {
            tested_drop_combinations += 1;
            let ids: Vec<usize> = choice.iter().map(|&index| pool[index].1).collect();
            let dropped_length: f64 = choice.iter().map(|&index| pool[index].0).sum();
            let mut endpoints = Vec::with_capacity(2 * drop_count);
            for &id in &ids {
                endpoints.extend_from_slice(&board.pairs[id]);
            }
            endpoints.sort_unstable();
            for offset in 0..2 {
                let mut valid = true;
                let mut wrong_length = 0.0;
                for step in 0..drop_count {
                    let a = endpoints[(offset + 2 * step) % endpoints.len()];
                    let b = endpoints[(offset + 2 * step + 1) % endpoints.len()];
                    if board.partner[a] == b {
                        valid = false;
                        break;
                    }
                    wrong_length += expected_route_length_between_exits(board, a, b);
                }
                if valid
                    && selected.as_ref().is_none_or(|current| {
                        wrong_length < current.0
                            || (wrong_length == current.0 && dropped_length > current.1)
                    })
                {
                    selected = Some((wrong_length, dropped_length, offset, ids.clone()));
                }
            }

            let mut position = drop_count;
            while position > 0
                && choice[position - 1] == pool_len - drop_count + position - 1
            {
                position -= 1;
            }
            if position == 0 {
                break;
            }
            choice[position - 1] += 1;
            for index in position..drop_count {
                choice[index] = choice[index - 1] + 1;
            }
        }
        if let Some((wrong_length, dropped_length, offset, ids)) = selected {
            let mut dropped = vec![false; pair_count];
            for &id in &ids {
                dropped[id] = true;
            }
            let mut retained_lengths: Vec<f64> = (0..pair_count)
                .filter(|&id| !dropped[id])
                .map(|id| pair_lengths[id])
                .collect();
            retained_lengths.sort_unstable_by(|a, b| b.total_cmp(a));
            let hero_shortest: f64 = retained_lengths
                .iter()
                .take(ESTIMATED_FULL_BONUS_PATHS)
                .sum();
            let matched = pair_count - drop_count;
            let correct_length = all_correct_length - dropped_length;
            let (score, bonus_length, total_value, estimated_moves) =
                estimate_score(matched, correct_length, wrong_length, hero_shortest);
            summaries.push((
                matched,
                drop_count,
                offset,
                wrong_length,
                bonus_length,
                total_value,
                estimated_moves,
                score,
            ));
            if score > best.0 {
                best = (score, matched, drop_count, offset);
            }
        }
    }
    summaries.sort_unstable_by(|a, b| b.7.total_cmp(&a.7));
    let mut best_by_matched = vec![None::<(f64, f64)>; pair_count + 1];
    for summary in &summaries {
        let slot = &mut best_by_matched[summary.0];
        if slot.is_none_or(|(score, _)| summary.7 > score) {
            *slot = Some((summary.7, summary.6));
        }
    }
    eprintln!(
        "connection_target_estimate best_k={} selected_drop={} offset={} score={:.0} moves={:.1} all_correct={:.1} segments={:.0} combinations={} elapsed_ms={} top={:?}",
        best.1,
        best.2,
        best.3,
        best.0,
        summaries[0].6,
        all_correct_length,
        total_segments,
        tested_drop_combinations,
        estimate_started.elapsed().as_millis(),
        summaries
            .iter()
            .take(8)
            .map(|x| (x.0, x.1, x.2, x.3.round() as i64, x.4.round() as i64, x.6.round() as i64, x.7.round() as i64))
            .collect::<Vec<_>>()
    );
    if pair_count <= 20 {
        eprintln!(
            "connection_target_by_k {:?}",
            best_by_matched
                .iter()
                .enumerate()
                .rev()
                .filter_map(|(matched, estimate)| {
                    estimate.map(|(score, moves)| {
                        (matched, score.round() as i64, moves.round() as i64)
                    })
                })
                .collect::<Vec<_>>()
        );
    }
    // The score estimator above decides only the target matched count.  Once k
    // is fixed, choose the abandoned originals separately so that the virtual
    // wrong wiring handed to the second construction beam is as short as
    // possible.  Restricting the pool to the longest p+2 originals preserves
    // most of the score-estimator intent while requiring only C(p+2, p)
    // (= C(p+2, 2)) combinations.
    let target_drop = pair_count - best.1;
    let prefix_dropped_ids: Vec<usize> = drop_candidates[..best.2]
        .iter()
        .map(|entry| entry.1)
        .collect();
    let mut dropped_ids = prefix_dropped_ids.clone();
    let mut selected_offset = best.3;
    let mut selected_wrong_length = f64::INFINITY;
    let mut selected_dropped_length: f64 =
        dropped_ids.iter().map(|&id| pair_lengths[id]).sum();
    if target_drop >= 2 && target_drop <= drop_candidates.len() {
        let pool_len = (target_drop + 2).min(drop_candidates.len());
        let pool = &drop_candidates[..pool_len];
        let mut choice: Vec<usize> = (0..target_drop).collect();
        loop {
            let mut candidate_ids: Vec<usize> =
                choice.iter().map(|&index| pool[index].1).collect();
            let dropped_length: f64 = choice.iter().map(|&index| pool[index].0).sum();
            let mut endpoints = Vec::with_capacity(2 * target_drop);
            for &id in &candidate_ids {
                endpoints.extend_from_slice(&board.pairs[id]);
            }
            endpoints.sort_unstable();
            for offset in 0..2 {
                let mut valid = true;
                let mut wrong_length = 0.0;
                for step in 0..target_drop {
                    let a = endpoints[(offset + 2 * step) % endpoints.len()];
                    let b = endpoints[(offset + 2 * step + 1) % endpoints.len()];
                    if board.partner[a] == b {
                        valid = false;
                        break;
                    }
                    wrong_length += expected_route_length_between_exits(board, a, b);
                }
                if valid
                    && (wrong_length < selected_wrong_length
                        || (wrong_length == selected_wrong_length
                            && dropped_length > selected_dropped_length))
                {
                    candidate_ids.sort_unstable();
                    dropped_ids = candidate_ids.clone();
                    selected_offset = offset;
                    selected_wrong_length = wrong_length;
                    selected_dropped_length = dropped_length;
                }
            }

            let mut position = target_drop;
            while position > 0
                && choice[position - 1] == pool_len - target_drop + position - 1
            {
                position -= 1;
            }
            if position == 0 {
                break;
            }
            choice[position - 1] += 1;
            for index in position..target_drop {
                choice[index] = choice[index - 1] + 1;
            }
        }
    }
    let mut endpoints = Vec::with_capacity(2 * dropped_ids.len());
    for &id in &dropped_ids {
        endpoints.extend_from_slice(&board.pairs[id]);
    }
    endpoints.sort_unstable();
    let mut wrong_pairs = Vec::with_capacity(dropped_ids.len());
    let mut rewired_pairs = Vec::with_capacity(dropped_ids.len());
    for step in 0..dropped_ids.len() {
        let a = endpoints[(selected_offset + 2 * step) % endpoints.len().max(1)];
        let b = endpoints[(selected_offset + 2 * step + 1) % endpoints.len().max(1)];
        rewired_pairs.push([a, b]);
        if board.partner[a] != b {
            wrong_pairs.push([a, b]);
        }
    }
    eprintln!(
        "connection_target_selection target_k={} drop={} pool={} wrong_length={:.1} ids={:?} prefix_ids={:?}",
        best.1,
        dropped_ids.len(),
        (target_drop + 2).min(drop_candidates.len()),
        wrong_pairs
            .iter()
            .map(|pair| expected_route_length_between_exits(board, pair[0], pair[1]))
            .sum::<f64>(),
        dropped_ids,
        prefix_dropped_ids
    );
    ConnectionTargetPlan {
        matched: best.1,
        dropped_ids,
        rewired_pairs,
        wrong_pairs,
        offset: selected_offset,
    }
}

fn ordinary_pair_priority(board: &Board, pair: [usize; 2]) -> usize {
    let a = board.exits[pair[0]].0;
    let b = board.exits[pair[1]].0;
    let dr = a as isize / board.W as isize - b as isize / board.W as isize;
    let dc = a as isize % board.W as isize - b as isize % board.W as isize;
    // This is not a geometric distance.  It delays pairs whose displacement
    // uses the NE/SW axis, leaving those difficult outer routes as hero candidates.
    let diagonal_contention = if dr.signum() != dc.signum() && dr != 0 && dc != 0 {
        dr.unsigned_abs().min(dc.unsigned_abs())
    } else {
        0
    };
    pair_distance(board, pair) + diagonal_contention
}

fn initialize_two_exit_direct_pairs(
    board: &Board,
    orientation: &mut [u8],
    fixed: &mut [u8],
    handled: &mut [bool],
    reserved: &[usize],
) -> usize {
    let mut direct_fixed = 0usize;
    for &cell in &board.valid_cells {
        if PROTECT_OUTER_BONUS_FROM_ORDINARY
            && board.bonus[cell]
            && board.boundary_depth[cell] == 0
        {
            continue;
        }
        let mut exits = [(usize::MAX, usize::MAX); 2];
        let mut exit_count = 0usize;
        for side in 0..6 {
            let exit = board.exit_id[cell * 6 + side];
            if exit >= 0 {
                if exit_count < exits.len() {
                    exits[exit_count] = (exit as usize, side);
                }
                exit_count += 1;
            }
        }
        if exit_count != 2 || board.partner[exits[0].0] != exits[1].0 {
            continue;
        }
        let Some(id) = board.pairs.iter().position(|&pair| {
            (pair[0] == exits[0].0 && pair[1] == exits[1].0)
                || (pair[0] == exits[1].0 && pair[1] == exits[0].0)
        }) else {
            continue;
        };
        if reserved.contains(&id) {
            continue;
        }
        let mut domain = 0u8;
        for o in 0..6u8 {
            if paired_dir(o, exits[0].1) == exits[1].1 {
                domain |= 1 << o;
            }
        }
        let (direct, _) = best_orientation_in_domain(board, orientation, cell, domain);
        orientation[cell] = direct;
        fixed[cell] = 1 << direct;
        handled[id] = true;
        direct_fixed += 1;
    }
    direct_fixed
}

fn build_outer(
    board: &Board,
    width: usize,
    reserved: &[usize],
    use_two_exit_direct: bool,
    deadline: Instant,
) -> (Vec<u8>, Vec<u8>) {
    let mut orientation = board.initial.clone();
    let mut fixed = vec![ALL_ORIENTATIONS; orientation.len()];
    let mut handled = vec![false; board.pairs.len()];
    if use_two_exit_direct {
        initialize_two_exit_direct_pairs(
            board,
            &mut orientation,
            &mut fixed,
            &mut handled,
            reserved,
        );
    }
    let mut best = orientation.clone();
    let mut best_fixed = fixed.clone();
    let mut best_stats = board.evaluate(&best);
    let mut order: Vec<usize> = (0..board.pairs.len())
        .filter(|i| !reserved.contains(i) && !handled[*i])
        .collect();
    order.sort_unstable_by_key(|&i| ordinary_pair_priority(board, board.pairs[i]));
    for i in order {
        if Instant::now() >= deadline {
            break;
        }
        let pair = board.pairs[i];
        if let Some(route) = find_route(
            board,
            &orientation,
            &fixed,
            pair[0],
            pair[1],
            width,
            false,
            None,
            None,
            deadline,
        ) {
            apply_route(&mut orientation, &mut fixed, &route, false);
            let stats = board.evaluate(&orientation);
            if (
                stats.score,
                stats.matched,
                stats.total - board.M as i64 * stats.moves as i64,
            ) > (
                best_stats.score,
                best_stats.matched,
                best_stats.total - board.M as i64 * best_stats.moves as i64,
            ) {
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
    ids.sort_unstable_by_key(|&i| Reverse(ordinary_pair_priority(board, board.pairs[i])));
    ids.truncate(SPECIAL_CANDIDATES.min(ids.len()));
    ids
}

fn optimistic_reachable_connections(
    board: &Board,
    fixed: &[u8],
    connections: &[[usize; 2]],
) -> Vec<bool> {
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
        if a != b {
            parent[b] = a;
        }
    }
    for cell in 0..board.valid.len() {
        if !board.valid[cell] {
            continue;
        }
        let components = DOMAIN_PORT_COMPONENTS[fixed[cell] as usize];
        for enter in 0..6 {
            let root = components[enter] as usize;
            if root != enter {
                join(
                    &mut parent,
                    cell * 6 + enter,
                    cell * 6 + root,
                );
            }
        }
        for side in 0..6 {
            if let Some((next, next_side)) = board.next(cell, side) {
                if cell < next {
                    join(&mut parent, cell * 6 + side, next * 6 + next_side);
                }
            } else {
                let exit = board.exit_id[cell * 6 + side];
                if exit >= 0 {
                    join(&mut parent, cell * 6 + side, ports + exit as usize);
                }
            }
        }
    }
    connections
        .iter()
        .map(|pair| root(&mut parent, ports + pair[0]) == root(&mut parent, ports + pair[1]))
        .collect()
}

fn optimistic_reachable_pairs(board: &Board, fixed: &[u8]) -> Vec<bool> {
    optimistic_reachable_connections(board, fixed, &board.pairs)
}

#[derive(Clone, Copy)]
struct TreeBoardChange {
    cell: usize,
    old_orientation: u8,
    new_orientation: u8,
    old_domain: u8,
    new_domain: u8,
}

struct TreeBoardNode {
    parent: usize,
    depth: usize,
    pair_id: usize,
    changes: Vec<TreeBoardChange>,
}

struct TreeBoardState {
    orientation: Vec<u8>,
    fixed: Vec<u8>,
    connected: Vec<bool>,
    rotated_tile_count: usize,
    rotation_lower_bound: i32,
}

struct CspDsuChange {
    root: usize,
    child: usize,
    root_size: usize,
    root_exit_count: u8,
    root_exit_a: usize,
    root_exit_b: usize,
}

struct RollbackPortDsu {
    parent: Vec<usize>,
    size: Vec<usize>,
    exit_count: Vec<u8>,
    exit_a: Vec<usize>,
    exit_b: Vec<usize>,
    history: Vec<CspDsuChange>,
}

impl RollbackPortDsu {
    fn new(port_nodes: usize, exit_count: usize) -> Self {
        let total = port_nodes + exit_count;
        let mut result = Self {
            parent: (0..total).collect(),
            size: vec![1; total],
            exit_count: vec![0; total],
            exit_a: vec![usize::MAX; total],
            exit_b: vec![usize::MAX; total],
            history: Vec::new(),
        };
        for exit in 0..exit_count {
            let node = port_nodes + exit;
            result.exit_count[node] = 1;
            result.exit_a[node] = exit;
        }
        result
    }

    #[inline]
    fn find(&self, mut node: usize) -> usize {
        while self.parent[node] != node {
            node = self.parent[node];
        }
        node
    }

    #[inline]
    fn snapshot(&self) -> usize {
        self.history.len()
    }

    fn rollback(&mut self, snapshot: usize) {
        while self.history.len() > snapshot {
            let change = self.history.pop().unwrap();
            self.parent[change.child] = change.child;
            self.size[change.root] = change.root_size;
            self.exit_count[change.root] = change.root_exit_count;
            self.exit_a[change.root] = change.root_exit_a;
            self.exit_b[change.root] = change.root_exit_b;
        }
    }

    fn union(&mut self, a: usize, b: usize, partner: &[usize]) -> bool {
        let mut ra = self.find(a);
        let mut rb = self.find(b);
        if ra == rb {
            return true;
        }
        let combined_count = self.exit_count[ra] + self.exit_count[rb];
        if combined_count > 2 {
            return false;
        }
        let mut exits = [usize::MAX; 2];
        let mut count = 0usize;
        for root in [ra, rb] {
            if self.exit_count[root] >= 1 {
                exits[count] = self.exit_a[root];
                count += 1;
            }
            if self.exit_count[root] >= 2 {
                exits[count] = self.exit_b[root];
                count += 1;
            }
        }
        if count == 2 && partner[exits[0]] != exits[1] {
            return false;
        }
        if self.size[ra] < self.size[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.history.push(CspDsuChange {
            root: ra,
            child: rb,
            root_size: self.size[ra],
            root_exit_count: self.exit_count[ra],
            root_exit_a: self.exit_a[ra],
            root_exit_b: self.exit_b[ra],
        });
        self.parent[rb] = ra;
        self.size[ra] += self.size[rb];
        self.exit_count[ra] = combined_count;
        self.exit_a[ra] = exits[0];
        self.exit_b[ra] = exits[1];
        true
    }
}

struct ExactCspSearch {
    dsu: RollbackPortDsu,
    orientation: Vec<u8>,
    assigned: Vec<bool>,
    domains: Vec<u8>,
    congestion: Vec<usize>,
    best_orientation: Option<Vec<u8>>,
    best_cost: i32,
    nodes: usize,
    forced: usize,
    solutions: usize,
    timed_out: bool,
}

fn csp_apply_orientation(
    board: &Board,
    dsu: &mut RollbackPortDsu,
    cell: usize,
    orientation: u8,
) -> bool {
    let snapshot = dsu.snapshot();
    for enter in 0..6 {
        let out = paired_dir(orientation, enter);
        if enter < out
            && !dsu.union(cell * 6 + enter, cell * 6 + out, &board.partner)
        {
            dsu.rollback(snapshot);
            return false;
        }
    }
    true
}

fn csp_boundary_congestion(board: &Board) -> Vec<usize> {
    let exits = board.exits.len();
    let mut difference = vec![0isize; exits + 1];
    for pair in &board.pairs {
        let a = pair[0].min(pair[1]);
        let b = pair[0].max(pair[1]);
        difference[a] += 1;
        difference[b] -= 1;
    }
    let mut cut_demand = vec![0usize; exits];
    let mut current = 0isize;
    for cut in 0..exits {
        current += difference[cut];
        cut_demand[cut] = current as usize;
    }
    let mut congestion = vec![0usize; board.valid.len()];
    for (exit, &(cell, _)) in board.exits.iter().enumerate() {
        congestion[cell] = congestion[cell]
            .max(cut_demand[exit])
            .max(cut_demand[(exit + exits - 1) % exits]);
    }
    congestion
}

fn exact_csp_dfs(board: &Board, search: &mut ExactCspSearch, current_cost: i32, deadline: Instant) {
    search.nodes += 1;
    if Instant::now() >= deadline {
        search.timed_out = true;
        return;
    }
    let mut selected = usize::MAX;
    let mut selected_mask = 0u8;
    let mut selected_count = 7u32;
    let mut selected_frontier = 0usize;
    let mut selected_frontier_size = 0usize;
    let mut lower_bound = current_cost;
    for &cell in &board.valid_cells {
        if search.assigned[cell] {
            continue;
        }
        let mut feasible = 0u8;
        let mut min_cost = i32::MAX;
        for orientation in 0..6u8 {
            if search.domains[cell] >> orientation & 1 == 0 {
                continue;
            }
            let snapshot = search.dsu.snapshot();
            if csp_apply_orientation(board, &mut search.dsu, cell, orientation) {
                feasible |= 1 << orientation;
                min_cost = min_cost.min(rotation_cost(board.initial[cell], orientation));
            }
            search.dsu.rollback(snapshot);
        }
        let count = feasible.count_ones();
        if count == 0 {
            return;
        }
        lower_bound += min_cost;
        let mut roots = [usize::MAX; 6];
        let mut root_count = 0usize;
        let mut frontier = 0usize;
        let mut frontier_size = 0usize;
        for side in 0..6 {
            let root = search.dsu.find(cell * 6 + side);
            if roots[..root_count].contains(&root) {
                continue;
            }
            roots[root_count] = root;
            root_count += 1;
            if search.dsu.exit_count[root] > 0 {
                frontier += 1;
                frontier_size += search.dsu.size[root];
            }
        }
        if count < selected_count
            || (count == selected_count
                && selected != usize::MAX
                && (
                    frontier,
                    frontier_size,
                    search.congestion[cell],
                    Reverse(board.boundary_depth[cell]),
                    Reverse(cell),
                ) > (
                    selected_frontier,
                    selected_frontier_size,
                    search.congestion[selected],
                    Reverse(board.boundary_depth[selected]),
                    Reverse(selected),
                ))
        {
            selected = cell;
            selected_mask = feasible;
            selected_count = count;
            selected_frontier = frontier;
            selected_frontier_size = frontier_size;
        }
    }
    if lower_bound >= search.best_cost {
        return;
    }
    if selected == usize::MAX {
        search.solutions += 1;
        let safe = board.tester_safe(&search.orientation);
        let stats = board.evaluate(&search.orientation);
        if safe {
            if stats.matched == board.pairs.len() && stats.moves < search.best_cost {
                search.best_cost = stats.moves;
                search.best_orientation = Some(search.orientation.clone());
            }
        }
        return;
    }
    search.forced += usize::from(selected_count == 1);
    let mut choices = [u8::MAX; 6];
    let mut choice_count = 0usize;
    for orientation in 0..6u8 {
        if selected_mask >> orientation & 1 != 0 {
            choices[choice_count] = orientation;
            choice_count += 1;
        }
    }
    choices[..choice_count].sort_unstable_by_key(|&orientation| {
        (
            rotation_cost(board.initial[selected], orientation),
            usize::from(orientation != search.orientation[selected]),
            orientation,
        )
    });
    for &orientation in &choices[..choice_count] {
        if search.timed_out {
            break;
        }
        let snapshot = search.dsu.snapshot();
        if !csp_apply_orientation(board, &mut search.dsu, selected, orientation) {
            search.dsu.rollback(snapshot);
            continue;
        }
        let previous = search.orientation[selected];
        search.orientation[selected] = orientation;
        search.assigned[selected] = true;
        exact_csp_dfs(
            board,
            search,
            current_cost + rotation_cost(board.initial[selected], orientation),
            deadline,
        );
        search.assigned[selected] = false;
        search.orientation[selected] = previous;
        search.dsu.rollback(snapshot);
    }
}

fn exact_csp_complete(
    board: &Board,
    orientation: &[u8],
    domains: &[u8],
    deadline: Instant,
) -> Option<Vec<u8>> {
    let started = Instant::now();
    let port_nodes = board.valid.len() * 6;
    let mut dsu = RollbackPortDsu::new(port_nodes, 0);
    for (exit, &(cell, side)) in board.exits.iter().enumerate() {
        let port = cell * 6 + side;
        dsu.exit_count[port] = 1;
        dsu.exit_a[port] = exit;
    }
    for &cell in &board.valid_cells {
        for side in 0..6 {
            let port = cell * 6 + side;
            if board.neighbors[cell][side] != usize::MAX {
                let target = board.neighbors[cell][side] * 6 + (side + 3) % 6;
                let joined = dsu.union(port, target, &board.partner);
                debug_assert!(joined);
            }
        }
    }
    dsu.history.clear();
    let mut search = ExactCspSearch {
        dsu,
        orientation: orientation.to_vec(),
        assigned: vec![false; board.valid.len()],
        domains: domains.to_vec(),
        congestion: csp_boundary_congestion(board),
        best_orientation: None,
        best_cost: i32::MAX,
        nodes: 0,
        forced: 0,
        solutions: 0,
        timed_out: false,
    };
    let mut fixed_cost = 0i32;
    let mut fixed_count = 0usize;
    let mut fixed_ok = true;
    let mut fixed_cells: Vec<usize> = board
        .valid_cells
        .iter()
        .copied()
        .filter(|&cell| domains[cell].count_ones() == 1)
        .collect();
    fixed_cells.sort_unstable_by_key(|&cell| Reverse(search.congestion[cell]));
    for cell in fixed_cells {
        let selected = domains[cell].trailing_zeros() as u8;
        if !csp_apply_orientation(board, &mut search.dsu, cell, selected) {
            fixed_ok = false;
            break;
        }
        search.orientation[cell] = selected;
        search.assigned[cell] = true;
        fixed_cost += rotation_cost(board.initial[cell], selected);
        fixed_count += 1;
    }
    if fixed_ok {
        exact_csp_dfs(board, &mut search, fixed_cost, deadline);
    }
    eprintln!(
        "exact_csp fixed={} free={} nodes={} forced={} solutions={} best_cost={} timeout={} elapsed_ms={}",
        fixed_count,
        board.valid_count.saturating_sub(fixed_count),
        search.nodes,
        search.forced,
        search.solutions,
        if search.best_cost == i32::MAX { -1 } else { search.best_cost },
        search.timed_out,
        started.elapsed().as_millis(),
    );
    search.best_orientation
}

fn exact_csp_repair_matched_paths(
    board: &Board,
    orientation: &[u8],
    deadline: Instant,
) -> Option<Vec<u8>> {
    let started = Instant::now();
    let mut domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        domains[cell] = ALL_ORIENTATIONS;
    }
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut ranked = Vec::new();
    for id in 0..board.pairs.len() {
        let (value, length) = board.trace_pair(orientation, id, &mut scratch, None);
        if value > 0 && length > 0 {
            ranked.push((value / length - 1, value, length, id));
        }
    }
    ranked.sort_unstable_by_key(|&(bonuses, value, length, id)| {
        (Reverse(bonuses), Reverse(value), Reverse(length), id)
    });
    let mut preserved = 0usize;
    for &(_, _, _, id) in ranked.iter().take(EXACT_CSP_PRESERVED_TRUNKS) {
        preserved += 1;
        let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(orientation[cell], enter);
            let mut required = 0u8;
            for candidate in 0..6u8 {
                if paired_dir(candidate, enter) == out {
                    required |= 1 << candidate;
                }
            }
            domains[cell] &= required;
            if domains[cell] == 0 {
                eprintln!(
                    "exact_csp_repair preserved={} conflict=true elapsed_ms={}",
                    preserved,
                    started.elapsed().as_millis(),
                );
                return None;
            }
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }
    let result = exact_csp_complete(board, orientation, &domains, deadline);
    if let Some(candidate) = &result {
        let stats = board.evaluate(candidate);
        eprintln!(
            "exact_csp_repair preserved={} k={} t={} m={} score={} elapsed_ms={}",
            preserved,
            stats.matched,
            stats.total,
            stats.moves,
            stats.score,
            started.elapsed().as_millis(),
        );
    }
    result
}

#[derive(Clone)]
struct TreeBoardCandidate {
    node: usize,
    connected_count: usize,
    optimistic_count: usize,
    route_length: usize,
    rotated_tile_count: usize,
    rotation_lower_bound: i32,
    layer_counts: [usize; OUTER_LAYERS],
}

#[derive(Clone)]
struct ConstructionArchiveEntry {
    stats: Stats,
    orientation: Vec<u8>,
}

fn store_construction_archive(
    archive: &mut Vec<ConstructionArchiveEntry>,
    stats: Stats,
    orientation: &[u8],
) -> bool {
    if let Some(entry) = archive
        .iter_mut()
        .find(|entry| entry.stats.matched == stats.matched)
    {
        if stats.quality() <= entry.stats.quality() {
            return false;
        }
        entry.stats = stats;
        entry.orientation.clone_from_slice(orientation);
        true
    } else {
        archive.push(ConstructionArchiveEntry {
            stats,
            orientation: orientation.to_vec(),
        });
        true
    }
}

fn tree_board_set_cell(
    board: &Board,
    state: &mut TreeBoardState,
    cell: usize,
    orientation: u8,
    domain: u8,
) {
    state.rotated_tile_count -= usize::from(state.orientation[cell] != board.initial[cell]);
    state.rotation_lower_bound -= board.domain_rotation[cell][state.fixed[cell] as usize];
    state.orientation[cell] = orientation;
    state.fixed[cell] = domain;
    state.rotated_tile_count += usize::from(orientation != board.initial[cell]);
    state.rotation_lower_bound += board.domain_rotation[cell][domain as usize];
}

fn tree_board_apply_node(board: &Board, state: &mut TreeBoardState, node: &TreeBoardNode) {
    for change in &node.changes {
        debug_assert_eq!(state.orientation[change.cell], change.old_orientation);
        debug_assert_eq!(state.fixed[change.cell], change.old_domain);
        tree_board_set_cell(
            board,
            state,
            change.cell,
            change.new_orientation,
            change.new_domain,
        );
    }
    state.connected[node.pair_id] = true;
}

fn tree_board_revert_node(board: &Board, state: &mut TreeBoardState, node: &TreeBoardNode) {
    state.connected[node.pair_id] = false;
    for change in node.changes.iter().rev() {
        debug_assert_eq!(state.orientation[change.cell], change.new_orientation);
        debug_assert_eq!(state.fixed[change.cell], change.new_domain);
        tree_board_set_cell(
            board,
            state,
            change.cell,
            change.old_orientation,
            change.old_domain,
        );
    }
}

fn tree_board_move_to(
    board: &Board,
    state: &mut TreeBoardState,
    nodes: &[TreeBoardNode],
    current: &mut usize,
    target: usize,
) {
    if *current == target {
        return;
    }
    let mut from = *current;
    let mut to = target;
    let mut apply_path = Vec::new();
    while nodes[from].depth > nodes[to].depth {
        tree_board_revert_node(board, state, &nodes[from]);
        from = nodes[from].parent;
    }
    while nodes[to].depth > nodes[from].depth {
        apply_path.push(to);
        to = nodes[to].parent;
    }
    while from != to {
        tree_board_revert_node(board, state, &nodes[from]);
        from = nodes[from].parent;
        apply_path.push(to);
        to = nodes[to].parent;
    }
    for &node in apply_path.iter().rev() {
        tree_board_apply_node(board, state, &nodes[node]);
    }
    *current = target;
}

fn tree_board_route_node(
    state: &TreeBoardState,
    parent: usize,
    pair_id: usize,
    route: &Route,
    keep_domains: bool,
    parent_depth: usize,
) -> TreeBoardNode {
    let mut changes = Vec::with_capacity(route.tiles.len());
    for &(cell, new_orientation, required_domain) in &route.tiles {
        // Ordinary route search never revisits a cell, so each delta can read
        // its parent value directly without a temporary board copy or map.
        let old_orientation = state.orientation[cell];
        let old_domain = state.fixed[cell];
        let new_domain = if keep_domains {
            old_domain & required_domain
        } else {
            1 << new_orientation
        };
        changes.push(TreeBoardChange {
            cell,
            old_orientation,
            new_orientation,
            old_domain,
            new_domain,
        });
    }
    TreeBoardNode {
        parent,
        depth: parent_depth + 1,
        pair_id,
        changes,
    }
}

fn run_tree_board_beam(
    board: &Board,
    orientation: Vec<u8>,
    fixed: Vec<u8>,
    connected: Vec<bool>,
    initial_layer_counts: [usize; OUTER_LAYERS],
    order: &[usize],
    keep_domains: bool,
    deadline: Instant,
    archive: &mut Vec<ConstructionArchiveEntry>,
) -> (Vec<u8>, Vec<u8>, [usize; OUTER_LAYERS]) {
    let started = Instant::now();
    let search_deadline = if COMPLETE_TREE_BOARD_BEAM {
        started + Duration::from_millis(COMPLETE_TREE_BOARD_BEAM_SAFETY_MS)
    } else {
        deadline
    };
    let reachable = optimistic_reachable_pairs(board, &fixed);
    let rotated_tile_count = board
        .valid_cells
        .iter()
        .filter(|&&cell| orientation[cell] != board.initial[cell])
        .count();
    let rotation_lower_bound = board
        .valid_cells
        .iter()
        .map(|&cell| board.domain_rotation[cell][fixed[cell] as usize])
        .sum();
    let mut state = TreeBoardState {
        orientation,
        fixed,
        connected,
        rotated_tile_count,
        rotation_lower_bound,
    };
    let mut nodes = vec![TreeBoardNode {
        parent: usize::MAX,
        depth: 0,
        pair_id: usize::MAX,
        changes: Vec::new(),
    }];
    let mut beam = vec![TreeBoardCandidate {
        node: 0,
        connected_count: state.connected.iter().filter(|&&value| value).count(),
        optimistic_count: reachable.iter().filter(|&&value| value).count(),
        route_length: 0,
        rotated_tile_count: state.rotated_tile_count,
        rotation_lower_bound: state.rotation_lower_bound,
        layer_counts: initial_layer_counts,
    }];
    let rank = |candidate: &TreeBoardCandidate| {
        Reverse((
            candidate.connected_count,
            Reverse(candidate.rotation_lower_bound),
            Reverse(candidate.route_length),
            candidate.optimistic_count,
            Reverse(candidate.rotated_tile_count),
        ))
    };
    let mut current = 0usize;
    let mut reachability_calls = 1usize;
    let mut expanded = 0usize;
    let mut reverse_scratch = ReverseBfsScratch::new(board.valid.len() * 6);
    let mut archive_updates = 0usize;

    'layers: for layer in 0..OUTER_LAYERS {
        for &id in order {
            if Instant::now() >= search_deadline {
                break 'layers;
            }
            let pair = board.pairs[id];
            let mut next_beam = Vec::with_capacity(beam.len() * (LAYERED_ROUTE_CANDIDATES + 1));
            for candidate in &beam {
                tree_board_move_to(board, &mut state, &nodes, &mut current, candidate.node);
                next_beam.push(candidate.clone());
                if state.connected[id] || Instant::now() >= search_deadline {
                    continue;
                }
                let routes = find_routes_with_reverse_scratch(
                    board,
                    &state.orientation,
                    &state.fixed,
                    pair[0],
                    pair[1],
                    if ENABLE_FULL_BOARD_CONSTRUCTION_BEAM {
                        board.W
                    } else {
                        layer + 1
                    },
                    false,
                    None,
                    if ENABLE_FULL_BOARD_CONSTRUCTION_BEAM {
                        None
                    } else {
                        Some(layer)
                    },
                    search_deadline,
                    LAYERED_ROUTE_CANDIDATES,
                    &mut reverse_scratch,
                );
                if routes.is_empty() {
                    continue;
                }
                let shortest = routes.iter().map(|route| route.length).min().unwrap();
                let before = optimistic_reachable_pairs(board, &state.fixed);
                reachability_calls += 1;
                for route in routes.into_iter().filter(|route| route.length == shortest) {
                    let node = tree_board_route_node(
                        &state,
                        candidate.node,
                        id,
                        &route,
                        keep_domains,
                        nodes[candidate.node].depth,
                    );
                    tree_board_apply_node(board, &mut state, &node);
                    let after = optimistic_reachable_pairs(board, &state.fixed);
                    reachability_calls += 1;
                    let keeps_future_open = (0..board.pairs.len()).all(|other| {
                        state.connected[other] || other == id || !before[other] || after[other]
                    });
                    let child_rotated_tile_count = state.rotated_tile_count;
                    let child_rotation_lower_bound = state.rotation_lower_bound;
                    tree_board_revert_node(board, &mut state, &node);
                    if keeps_future_open {
                        let next_node = nodes.len();
                        nodes.push(node);
                        let mut layer_counts = candidate.layer_counts;
                        layer_counts[layer] += 1;
                        next_beam.push(TreeBoardCandidate {
                            node: next_node,
                            connected_count: candidate.connected_count + 1,
                            optimistic_count: after.iter().filter(|&&value| value).count(),
                            route_length: candidate.route_length + route.length,
                            rotated_tile_count: child_rotated_tile_count,
                            rotation_lower_bound: child_rotation_lower_bound,
                            layer_counts,
                        });
                        expanded += 1;
                    }
                }
            }
            next_beam.sort_unstable_by_key(rank);
            let max_connected = next_beam
                .first()
                .expect("empty next tree board beam")
                .connected_count;
            let mut selected = Vec::with_capacity(LAYERED_BOARD_BEAM_WIDTH);
            let mut selected_nodes = HashSet::with_capacity(LAYERED_BOARD_BEAM_WIDTH);
            // Do not let one cheap-looking shortest route monopolize the beam.
            // At the current maximum k, retain states preferred by different
            // resource metrics before reserving the usual lower-k fallbacks.
            for metric in 0..TREE_BOARD_MAX_K_DIVERSE_STATES {
                let candidate = next_beam
                    .iter()
                    .filter(|candidate| {
                        candidate.connected_count == max_connected
                            && !selected_nodes.contains(&candidate.node)
                    })
                    .min_by_key(|candidate| match metric {
                        0 => (
                            candidate.rotation_lower_bound as i64,
                            candidate.route_length,
                            usize::MAX - candidate.optimistic_count,
                            candidate.rotated_tile_count,
                        ),
                        1 => (
                            -(candidate.optimistic_count as i64),
                            candidate.rotation_lower_bound.max(0) as usize,
                            candidate.route_length,
                            candidate.rotated_tile_count,
                        ),
                        2 => (
                            candidate.route_length as i64,
                            usize::MAX - candidate.optimistic_count,
                            candidate.rotation_lower_bound.max(0) as usize,
                            candidate.rotated_tile_count,
                        ),
                        _ => (
                            candidate.rotated_tile_count as i64,
                            usize::MAX - candidate.optimistic_count,
                            candidate.rotation_lower_bound.max(0) as usize,
                            candidate.route_length,
                        ),
                    });
                if let Some(candidate) = candidate {
                    selected_nodes.insert(candidate.node);
                    selected.push(candidate.clone());
                }
            }
            for delta in 1..TREE_BOARD_K_LEVELS {
                let Some(target_connected) = max_connected.checked_sub(delta) else {
                    break;
                };
                if let Some(candidate) = next_beam
                    .iter()
                    .find(|candidate| candidate.connected_count == target_connected)
                {
                    if selected_nodes.insert(candidate.node) {
                        selected.push(candidate.clone());
                    }
                }
            }
            for candidate in next_beam {
                if selected.len() >= LAYERED_BOARD_BEAM_WIDTH {
                    break;
                }
                if selected_nodes.insert(candidate.node) {
                    selected.push(candidate);
                }
            }
            selected.sort_unstable_by_key(rank);
            beam = selected;
        }
    }
    let mut eval_scratch = EvalScratch::new(board.valid.len());
    let mut scored = Vec::with_capacity(beam.len());
    for candidate in &beam {
        tree_board_move_to(board, &mut state, &nodes, &mut current, candidate.node);
        let stats = board.evaluate_with_scratch(&state.orientation, &mut eval_scratch);
        archive_updates += usize::from(store_construction_archive(
            archive,
            stats,
            &state.orientation,
        ));
        let mut used_segments = 0usize;
        let mut shortest_sum = 0usize;
        for id in 0..board.pairs.len() {
            let (value, length) = board.trace_pair(&state.orientation, id, &mut eval_scratch, None);
            if value <= 0 || length <= 0 {
                continue;
            }
            used_segments += length as usize;
            shortest_sum += pair_distance(board, board.pairs[id]) + 1;
        }
        let free_segments = (3 * board.valid_count).saturating_sub(used_segments);
        let projected_extra = if used_segments == 0 {
            free_segments as i64 * PROJECTED_FREE_USE_NUM / PROJECTED_FREE_USE_DEN
        } else {
            free_segments as i64 * stats.total * PROJECTED_FREE_USE_NUM
                / (used_segments as i64 * PROJECTED_FREE_USE_DEN)
        };
        let average_multiplier_milli = if used_segments == 0 {
            1_000
        } else {
            stats.total * 1_000 / used_segments as i64
        };
        let projected_moves =
            (candidate.rotation_lower_bound * PROJECTED_ROTATION_NUM + PROJECTED_ROTATION_DEN - 1)
                / PROJECTED_ROTATION_DEN;
        let projected_total = stats.total + projected_extra;
        let projected_score = (stats.matched as i64
            * (projected_total - board.M as i64 * projected_moves as i64))
            .max(0);
        scored.push((
            candidate.clone(),
            stats,
            projected_score,
            used_segments,
            free_segments,
            average_multiplier_milli,
            projected_moves,
            projected_total,
            shortest_sum,
        ));
    }
    let mut chosen_index = 0usize;
    for index in 1..scored.len() {
        if scored[index].1.quality() > scored[chosen_index].1.quality() {
            chosen_index = index;
        }
    }
    let (
        chosen,
        chosen_stats,
        projected_score,
        used_segments,
        free_segments,
        average_multiplier_milli,
        projected_moves,
        projected_total,
        shortest_sum,
    ) = scored[chosen_index].clone();
    tree_board_move_to(board, &mut state, &nodes, &mut current, chosen.node);
    eprintln!(
        "tree_board_beam nodes={} expanded={} reachability={} archive={}/{} tracked_k={} exact_k={} exact_score={} projected_score={} projected_t={} projected_m={} used={} shortest={} detour={} free={} bonuses={} avg_multiplier_milli={} segments={} rotated={} rotation_lb={} elapsed_ms={}",
        nodes.len(), expanded, reachability_calls, archive_updates, archive.len(),
        chosen.connected_count, chosen_stats.matched, chosen_stats.score, projected_score, projected_total,
        projected_moves, used_segments, shortest_sum,
        used_segments.saturating_sub(shortest_sum), free_segments,
        board.bonus.iter().filter(|&&value| value).count(), average_multiplier_milli,
        chosen.route_length, state.rotated_tile_count, state.rotation_lower_bound,
        started.elapsed().as_millis(),
    );
    (state.orientation, state.fixed, chosen.layer_counts)
}

fn build_layered_with_specials(
    board: &Board,
    archive: &mut Vec<ConstructionArchiveEntry>,
    reserved: &[usize],
    order_variant: usize,
    keep_domains: bool,
    use_two_exit_direct: bool,
    outer_deadline: Instant,
    special_deadline: Instant,
) -> (Vec<u8>, [usize; OUTER_LAYERS], usize, i64) {
    let mut orientation = board.initial.clone();
    let mut fixed = vec![ALL_ORIENTATIONS; orientation.len()];
    let mut connected = vec![false; board.pairs.len()];
    let direct_fixed = if use_two_exit_direct {
        initialize_two_exit_direct_pairs(
            board,
            &mut orientation,
            &mut fixed,
            &mut connected,
            reserved,
        )
    } else {
        0
    };
    let mut layer_counts = [0usize; OUTER_LAYERS];
    let mut selected_detours = 0usize;
    let mut order: Vec<usize> = (0..board.pairs.len())
        .filter(|id| !reserved.contains(id))
        .collect();
    order.sort_unstable_by_key(|&id| {
        let distance = pair_distance(board, board.pairs[id]);
        let priority = ordinary_pair_priority(board, board.pairs[id]);
        let tie = match order_variant % 3 {
            0 => 0,
            // Among equally ranked pairs, try the more contended diagonal
            // displacement first in one construction and last in another.
            1 => distance,
            _ => usize::MAX - distance,
        };
        (priority, tie, id)
    });
    if ENABLE_LAYERED_BOARD_BEAM && ENABLE_TREE_BOARD_BEAM && !ENABLE_DEFERRED_ROUTE_CHOICES {
        let (next_orientation, next_fixed, next_layer_counts) = run_tree_board_beam(
            board,
            orientation,
            fixed,
            connected,
            layer_counts,
            &order,
            keep_domains,
            outer_deadline,
            archive,
        );
        orientation = next_orientation;
        fixed = next_fixed;
        layer_counts = next_layer_counts;
    } else if ENABLE_LAYERED_BOARD_BEAM {
        let cloned_beam_started = Instant::now();
        let mut cloned_beam_reachability_calls = 1usize;
        let mut cloned_beam_expanded = 0usize;
        #[derive(Clone)]
        struct LayeredBeamState {
            orientation: Vec<u8>,
            fixed: Vec<u8>,
            connected: Vec<bool>,
            layer_counts: [usize; OUTER_LAYERS],
            connected_count: usize,
            optimistic_count: usize,
            route_length: usize,
            detour_count: usize,
            rotated_tile_count: usize,
            rotation_lower_bound: i32,
            deferred: Vec<DeferredRouteChoice>,
        }
        let rotation_lower_bound = |domains: &[u8]| -> i32 {
            board
                .valid_cells
                .iter()
                .map(|&cell| board.domain_rotation[cell][domains[cell] as usize])
                .sum()
        };
        let rotated_tile_count = |orientations: &[u8]| -> usize {
            board
                .valid_cells
                .iter()
                .filter(|&&cell| orientations[cell] != board.initial[cell])
                .count()
        };
        let reachable = optimistic_reachable_pairs(board, &fixed);
        let initial_rotation_lower_bound = rotation_lower_bound(&fixed);
        let initial_rotated_tile_count = rotated_tile_count(&orientation);
        let mut beam = vec![LayeredBeamState {
            orientation,
            fixed,
            connected_count: connected.iter().filter(|&&x| x).count(),
            optimistic_count: reachable.iter().filter(|&&x| x).count(),
            connected,
            layer_counts,
            route_length: 0,
            detour_count: 0,
            rotated_tile_count: initial_rotated_tile_count,
            rotation_lower_bound: initial_rotation_lower_bound,
            deferred: Vec::new(),
        }];

        'layers: for layer in 0..OUTER_LAYERS {
            for &id in &order {
                if Instant::now() >= outer_deadline {
                    break 'layers;
                }
                let pair = board.pairs[id];
                let mut next_beam = Vec::with_capacity(beam.len() * (LAYERED_ROUTE_CANDIDATES + 1));
                for state in beam.into_iter() {
                    next_beam.push(state.clone());
                    if state.connected[id] || Instant::now() >= outer_deadline {
                        continue;
                    }
                    let routes = find_routes(
                        board,
                        &state.orientation,
                        &state.fixed,
                        pair[0],
                        pair[1],
                        if ENABLE_FULL_BOARD_CONSTRUCTION_BEAM {
                            board.W
                        } else {
                            layer + 1
                        },
                        false,
                        None,
                        if ENABLE_FULL_BOARD_CONSTRUCTION_BEAM {
                            None
                        } else {
                            Some(layer)
                        },
                        outer_deadline,
                        LAYERED_ROUTE_CANDIDATES,
                    );
                    if routes.is_empty() {
                        continue;
                    }
                    let shortest_length = routes.iter().map(|route| route.length).min().unwrap();
                    let has_detour = routes.iter().any(|route| route.length > shortest_length);
                    if ENABLE_DEFERRED_ROUTE_CHOICES
                        && has_detour
                        && state.deferred.len() < LAYERED_DEFERRED_CHOICES
                    {
                        let mut candidate = state.clone();
                        candidate.connected[id] = true;
                        candidate.route_length += shortest_length;
                        candidate.deferred.push(DeferredRouteChoice {
                            layer,
                            shortest_length,
                            routes: routes.clone(),
                        });
                        if !deferred_route_selections(&candidate.fixed, &candidate.deferred, 1)
                            .is_empty()
                        {
                            next_beam.push(candidate);
                        }
                    }
                    let before = optimistic_reachable_pairs(board, &state.fixed);
                    cloned_beam_reachability_calls += 1;
                    for route in routes
                        .into_iter()
                        .filter(|route| !has_detour || route.length == shortest_length)
                    {
                        let mut candidate = state.clone();
                        apply_route(
                            &mut candidate.orientation,
                            &mut candidate.fixed,
                            &route,
                            keep_domains,
                        );
                        let after = optimistic_reachable_pairs(board, &candidate.fixed);
                        cloned_beam_reachability_calls += 1;
                        let keeps_future_open = (0..board.pairs.len()).all(|other| {
                            state.connected[other] || other == id || !before[other] || after[other]
                        });
                        if !keeps_future_open {
                            continue;
                        }
                        if deferred_route_selections(&candidate.fixed, &candidate.deferred, 1)
                            .is_empty()
                        {
                            continue;
                        }
                        candidate.connected[id] = true;
                        candidate.connected_count += 1;
                        candidate.optimistic_count = after.iter().filter(|&&x| x).count();
                        candidate.layer_counts[layer] += 1;
                        candidate.route_length += route.length;
                        candidate.detour_count += usize::from(route.length > shortest_length);
                        candidate.rotated_tile_count = rotated_tile_count(&candidate.orientation);
                        candidate.rotation_lower_bound = rotation_lower_bound(&candidate.fixed);
                        next_beam.push(candidate);
                        cloned_beam_expanded += 1;
                    }
                }
                let beam_rank = |state: &LayeredBeamState| {
                    Reverse((
                        state.connected_count,
                        Reverse(state.route_length),
                        Reverse(state.rotated_tile_count),
                        state.optimistic_count,
                        Reverse(state.rotation_lower_bound),
                    ))
                };
                next_beam.sort_unstable_by_key(beam_rank);
                let mut regular_states = Vec::new();
                let mut deferred_states = Vec::new();
                for state in next_beam {
                    if state.deferred.is_empty() {
                        regular_states.push(state);
                    } else {
                        deferred_states.push(state);
                    }
                }
                let regular_reserved = (LAYERED_BOARD_BEAM_WIDTH
                    - LAYERED_DEFERRED_RESERVED_STATES)
                    .min(regular_states.len());
                let deferred_reserved = LAYERED_DEFERRED_RESERVED_STATES.min(deferred_states.len());
                let mut selected = Vec::with_capacity(LAYERED_BOARD_BEAM_WIDTH);
                selected.extend(regular_states.drain(..regular_reserved));
                selected.extend(deferred_states.drain(..deferred_reserved));
                regular_states.append(&mut deferred_states);
                regular_states.sort_unstable_by_key(beam_rank);
                selected.extend(
                    regular_states
                        .into_iter()
                        .take(LAYERED_BOARD_BEAM_WIDTH.saturating_sub(selected.len())),
                );
                selected.sort_unstable_by_key(beam_rank);
                beam = selected;
            }
        }
        if !ENABLE_DEFERRED_ROUTE_CHOICES {
            let chosen = beam.into_iter().next().expect("empty layered board beam");
            orientation = chosen.orientation;
            fixed = chosen.fixed;
            layer_counts = chosen.layer_counts;
            selected_detours = chosen.detour_count;
        } else {
            let mut best_materialized: Option<(
                Stats,
                Vec<u8>,
                Vec<u8>,
                [usize; OUTER_LAYERS],
                usize,
                usize,
            )> = None;
            for state in beam {
                let selections = if state.deferred.is_empty() {
                    vec![Vec::new()]
                } else {
                    deferred_route_selections(
                        &state.fixed,
                        &state.deferred,
                        LAYERED_DEFERRED_ASSIGNMENTS,
                    )
                };
                for selection in selections {
                    let mut trial_orientation = state.orientation.clone();
                    let mut trial_fixed = state.fixed.clone();
                    let mut trial_layers = state.layer_counts;
                    let mut touched = vec![false; trial_fixed.len()];
                    let mut detours = state.detour_count;
                    for (choice, &route_id) in state.deferred.iter().zip(&selection) {
                        let route = &choice.routes[route_id];
                        debug_assert!(intersect_route_domains(&mut trial_fixed, route));
                        detours += usize::from(route.length > choice.shortest_length);
                        trial_layers[choice.layer] += 1;
                        for &(cell, _, _) in &route.tiles {
                            touched[cell] = true;
                        }
                    }
                    for &cell in &board.valid_cells {
                        let domain = trial_fixed[cell];
                        if domain >> trial_orientation[cell] & 1 == 0 {
                            let mut best_orientation = 0u8;
                            let mut best_cost = i32::MAX;
                            for candidate_orientation in 0..6u8 {
                                if domain >> candidate_orientation & 1 == 0 {
                                    continue;
                                }
                                let cost =
                                    rotation_cost(board.initial[cell], candidate_orientation);
                                if cost < best_cost {
                                    best_cost = cost;
                                    best_orientation = candidate_orientation;
                                }
                            }
                            trial_orientation[cell] = best_orientation;
                        }
                        if touched[cell] && !keep_domains {
                            trial_fixed[cell] = 1 << trial_orientation[cell];
                        }
                    }
                    let stats = board.evaluate(&trial_orientation);
                    if best_materialized
                        .as_ref()
                        .is_none_or(|entry| stats.quality() > entry.0.quality())
                    {
                        best_materialized = Some((
                            stats,
                            trial_orientation,
                            trial_fixed,
                            trial_layers,
                            detours,
                            state.deferred.len(),
                        ));
                    }
                }
            }
            let (stats, chosen_orientation, chosen_fixed, chosen_layers, detours, deferred_count) =
                best_materialized.expect("empty layered materialization");
            eprintln!(
                "layered_materialized deferred={} detours={} k={} score={}",
                deferred_count, detours, stats.matched, stats.score,
            );
            orientation = chosen_orientation;
            fixed = chosen_fixed;
            layer_counts = chosen_layers;
            selected_detours = detours;
        }
        eprintln!(
            "cloned_board_beam expanded={} reachability={} elapsed_ms={}",
            cloned_beam_expanded,
            cloned_beam_reachability_calls,
            cloned_beam_started.elapsed().as_millis(),
        );
    } else {
        for layer in 0..OUTER_LAYERS {
            for &id in &order {
                if connected[id] || Instant::now() >= outer_deadline {
                    continue;
                }
                let pair = board.pairs[id];
                let Some(route) = find_route(
                    board,
                    &orientation,
                    &fixed,
                    pair[0],
                    pair[1],
                    layer + 1,
                    false,
                    None,
                    Some(layer),
                    outer_deadline,
                ) else {
                    continue;
                };

                let before = optimistic_reachable_pairs(board, &fixed);
                let mut trial_orientation = orientation.clone();
                let mut trial_fixed = fixed.clone();
                apply_route(
                    &mut trial_orientation,
                    &mut trial_fixed,
                    &route,
                    keep_domains,
                );
                let after = optimistic_reachable_pairs(board, &trial_fixed);
                let keeps_future_open = (0..board.pairs.len())
                    .all(|other| connected[other] || other == id || !before[other] || after[other]);
                if keeps_future_open {
                    orientation = trial_orientation;
                    fixed = trial_fixed;
                    connected[id] = true;
                    layer_counts[layer] += 1;
                }
            }
        }
    }

    let before_special_orientation = orientation.clone();
    let before_special_stats = board.evaluate(&before_special_orientation);
    let special_deadline = if ENABLE_TREE_BOARD_BEAM && COMPLETE_TREE_BOARD_BEAM {
        Instant::now() + Duration::from_millis(LAYERED_SPECIAL_LIMIT_MS)
    } else {
        special_deadline
    };
    let mut special_value = 0i64;
    let mut special_done = 0usize;
    for (index, &id) in reserved.iter().enumerate() {
        let now = Instant::now();
        if now >= special_deadline {
            break;
        }
        let searches_left = reserved.len() - index;
        let route_budget = special_deadline.duration_since(now) / searches_left as u32;
        let route_deadline = now + route_budget;
        let pair = board.pairs[id];
        let use_damage_dp = (board.W + 1) / 2 >= 16 && board.M <= 2;
        let damage = use_damage_dp.then(|| board.damage_model(&orientation));
        if let Some(route) = find_route(
            board,
            &orientation,
            &fixed,
            pair[0],
            pair[1],
            OUTER_LAYERS,
            true,
            damage.as_ref(),
            None,
            route_deadline,
        ) {
            special_value += (route.length * (route.bonuses + 1)) as i64;
            special_done += 1;
            apply_route(&mut orientation, &mut fixed, &route, keep_domains);
        }
    }
    if keep_domains {
        resolve_domains(
            board,
            &mut orientation,
            &fixed,
            Instant::now() + Duration::from_millis(60),
        );
    }
    let after_special_stats = board.evaluate(&orientation);
    if before_special_stats.quality() > after_special_stats.quality() {
        eprintln!(
            "special_fallback k={}->{} score={}->{}",
            after_special_stats.matched,
            before_special_stats.matched,
            after_special_stats.score,
            before_special_stats.score,
        );
        orientation = before_special_orientation;
        special_done = 0;
        special_value = 0;
    }
    eprintln!(
        "layered_outer_priority direct_fixed={} reserved={:?} detours={}",
        direct_fixed, reserved, selected_detours
    );
    (orientation, layer_counts, special_done, special_value)
}

fn open_reserved_gates(board: &Board, fixed: &mut [u8], chosen: &[usize], width: usize) {
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
        fixed[cell] = ALL_ORIENTATIONS;
        if dist[cell] == radius {
            continue;
        }
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
    outer_fixed: &[u8],
    width: usize,
    chosen: &[usize],
    deadline: Instant,
) -> (Vec<u8>, i64, usize) {
    let mut orientation = outer.to_vec();
    let mut fixed = outer_fixed.to_vec();
    for cell in 0..fixed.len() {
        if board.valid[cell] && board.boundary_depth[cell] > width {
            fixed[cell] = ALL_ORIENTATIONS;
        }
    }
    open_reserved_gates(board, &mut fixed, chosen, width);
    let mut special_value = 0i64;
    let mut special_done = 0usize;
    for &id in chosen {
        if Instant::now() >= deadline {
            break;
        }
        let p = board.pairs[id];
        let use_damage_dp = (board.W + 1) / 2 >= 16 && board.M <= 2;
        let damage = use_damage_dp.then(|| board.damage_model(&orientation));
        if let Some(route) = find_route(
            board,
            &orientation,
            &fixed,
            p[0],
            p[1],
            width,
            true,
            damage.as_ref(),
            None,
            deadline,
        ) {
            special_value += (route.length * (route.bonuses + 1)) as i64;
            special_done += 1;
            apply_route(&mut orientation, &mut fixed, &route, false);
        }
    }
    let mut best_orientation = orientation.clone();
    let mut best_stats = board.evaluate(&orientation);

    // Rebuild the many ordinary connections around the protected special paths.
    let mut order: Vec<usize> = (0..board.pairs.len())
        .filter(|i| !chosen.contains(i))
        .collect();
    order.sort_unstable_by_key(|&i| ordinary_pair_priority(board, board.pairs[i]));
    for id in order {
        if Instant::now() >= deadline {
            break;
        }
        let p = board.pairs[id];
        if let Some(route) = find_route(
            board,
            &orientation,
            &fixed,
            p[0],
            p[1],
            width,
            false,
            None,
            None,
            deadline,
        ) {
            apply_route(&mut orientation, &mut fixed, &route, false);
            let stats = board.evaluate(&orientation);
            let q = stats.total - board.M as i64 * stats.moves as i64;
            let best_q = best_stats.total - board.M as i64 * best_stats.moves as i64;
            if (
                stats.score,
                q,
                stats.matched,
                stats.total,
                Reverse(stats.moves),
            ) > (
                best_stats.score,
                best_q,
                best_stats.matched,
                best_stats.total,
                Reverse(best_stats.moves),
            ) {
                best_stats = stats;
                best_orientation = orientation.clone();
            }
        }
    }
    (best_orientation, special_value, special_done)
}

fn polish(board: &Board, orientation: &mut Vec<u8>, deadline: Instant) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut best = board.evaluate_with_scratch(orientation, &mut scratch);
    let mut differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut updates = Vec::with_capacity(board.pairs.len());
    let mut best_updates = Vec::with_capacity(board.pairs.len());
    let mut route_cells = Vec::new();
    let mut changed = true;
    while changed && Instant::now() < deadline {
        changed = false;
        for cell in 0..orientation.len() {
            if !board.valid[cell] || Instant::now() >= deadline {
                break;
            }
            let old = orientation[cell];
            let base = best;
            let mut best_o = old;
            best_updates.clear();
            let affected = differential.cell_masks[cell];
            for o in 0..6u8 {
                if o == old {
                    continue;
                }
                orientation[cell] = o;
                let moves = base.moves - rotation_cost(board.initial[cell], old)
                    + rotation_cost(board.initial[cell], o);
                let s = differential.proposal(
                    board,
                    orientation,
                    base,
                    moves,
                    affected,
                    &mut scratch,
                    &mut updates,
                );
                let q = s.total - board.M as i64 * s.moves as i64;
                let best_q = best.total - board.M as i64 * best.moves as i64;
                if (s.score, q, s.matched, s.total, Reverse(s.moves))
                    > (
                        best.score,
                        best_q,
                        best.matched,
                        best.total,
                        Reverse(best.moves),
                    )
                {
                    best = s;
                    best_o = o;
                    best_updates.clone_from(&updates);
                }
            }
            orientation[cell] = best_o;
            if best_o != old {
                differential.commit(
                    board,
                    orientation,
                    &mut scratch,
                    &best_updates,
                    &mut route_cells,
                );
            }
            changed |= best_o != old;
        }
    }
}

fn path_states(
    board: &Board,
    orientation: &[u8],
    start: usize,
    seen: &mut [u32],
    bonus_seen: &mut [u32],
    epoch: u32,
    states: &mut Vec<(usize, usize)>,
) -> (usize, usize, usize) {
    let (cell, enter) = board.exits[start];
    let mut state = cell * 6 + enter;
    let terminal_base = board.valid.len() * 6;
    states.clear();
    let mut bonuses = 0usize;
    for _ in 0..=3 * board.valid_count {
        if seen[state] == epoch {
            return (usize::MAX, states.len(), bonuses);
        }
        seen[state] = epoch;
        let cell = state / 6;
        let enter = state % 6;
        states.push((cell, enter));
        if board.bonus[cell] && bonus_seen[cell] != epoch {
            bonuses += 1;
            bonus_seen[cell] = epoch;
        }
        let next = board.transition[state * 6 + orientation[cell] as usize] as usize;
        if next >= terminal_base {
            return (next - terminal_base, states.len(), bonuses);
        }
        state = next;
    }
    (usize::MAX, states.len(), bonuses)
}

struct LocalExtendWorkspace {
    seen: Vec<u32>,
    bonus_seen: Vec<u32>,
    epoch: u32,
    on_path: Vec<u32>,
    on_path_epoch: u32,
    states: Vec<(usize, usize)>,
    ranked: Vec<(i64, usize, usize)>,
    trial: Vec<u8>,
    trace_scratch: EvalScratch,
    eval_scratch: EvalScratch,
    updates: Vec<(usize, i64)>,
}

impl LocalExtendWorkspace {
    fn new(board: &Board, orientation: &[u8]) -> Self {
        Self {
            seen: vec![0; board.valid.len() * 6],
            bonus_seen: vec![0; board.valid.len()],
            epoch: 0,
            on_path: vec![0; board.valid.len()],
            on_path_epoch: 0,
            states: Vec::with_capacity(3 * board.valid_count),
            ranked: Vec::with_capacity(board.pairs.len()),
            trial: orientation.to_vec(),
            trace_scratch: EvalScratch::new(board.valid.len()),
            eval_scratch: EvalScratch::new(board.valid.len()),
            updates: Vec::with_capacity(board.pairs.len()),
        }
    }

    fn next_epoch(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.seen.fill(0);
            self.bonus_seen.fill(0);
            self.epoch = 1;
        }
        self.epoch
    }

    fn next_path_epoch(&mut self) -> u32 {
        self.on_path_epoch = self.on_path_epoch.wrapping_add(1);
        if self.on_path_epoch == 0 {
            self.on_path.fill(0);
            self.on_path_epoch = 1;
        }
        self.on_path_epoch
    }
}

fn local_extend_candidate(
    board: &Board,
    orientation: &[u8],
    base: Stats,
    differential: &DifferentialEval,
    rng: &mut Rng,
    workspace: &mut LocalExtendWorkspace,
    deadline: Instant,
) -> Option<(Stats, Vec<u8>)> {
    workspace.ranked.clear();
    workspace.ranked.extend(
        (0..board.pairs.len()).filter_map(|id| {
            let value = differential.contribution[id];
            let length = differential.pair_cells[id].len();
            (value > 0 && length >= 2).then_some((value, id, length))
        }),
    );
    if workspace.ranked.is_empty() {
        return None;
    }
    workspace.ranked.sort_unstable_by_key(|x| Reverse(x.0));
    let pick = rng.usize(workspace.ranked.len().min(4));
    let (old_value, id, old_length) = workspace.ranked[pick];
    let pair = board.pairs[id];
    let epoch = workspace.next_epoch();
    let (end, traced_length, _) = path_states(
        board,
        orientation,
        pair[0],
        &mut workspace.seen,
        &mut workspace.bonus_seen,
        epoch,
        &mut workspace.states,
    );
    if end != pair[1] || traced_length != old_length {
        return None;
    }
    let path_epoch = workspace.next_path_epoch();
    for &(cell, _) in &workspace.states {
        workspace.on_path[cell] = path_epoch;
    }

    let mut cluster = None;
    let offset = rng.usize(workspace.states.len());
    'centers: for step in 0..workspace.states.len() {
        let (center, enter) = workspace.states[(offset + step) % workspace.states.len()];
        let current_out = paired_dir(orientation[center], enter);
        let mut neighbors = Vec::new();
        for side in 0..6 {
            if side == enter || side == current_out {
                continue;
            }
            if let Some((next, _)) = board.next(center, side) {
                if workspace.on_path[next] != path_epoch {
                    neighbors.push(next);
                }
            }
        }
        for i in 0..neighbors.len() {
            for j in i + 1..neighbors.len() {
                let a = neighbors[i];
                let b = neighbors[j];
                let adjacent = (0..6).any(|side| board.next(a, side).is_some_and(|x| x.0 == b));
                if !adjacent {
                    continue;
                }
                let mut cells = vec![center, a, b];
                if rng.usize(2) == 0 {
                    let mut fourth = None;
                    for &base in &[a, b] {
                        for side in 0..6 {
                            if let Some((next, _)) = board.next(base, side) {
                                if workspace.on_path[next] != path_epoch && !cells.contains(&next) {
                                    fourth = Some(next);
                                    break;
                                }
                            }
                        }
                        if fourth.is_some() {
                            break;
                        }
                    }
                    if let Some(cell) = fourth {
                        cells.push(cell);
                    }
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
    } else {
        total_patterns
    };
    let pattern_offset = rng.usize(total_patterns);
    let mut candidates: Vec<(i64, usize, i32, usize)> = Vec::with_capacity(16);
    workspace.trial.clone_from_slice(orientation);
    let old_rotations: i32 = cells
        .iter()
        .map(|&cell| rotation_cost(board.initial[cell], orientation[cell]))
        .sum();
    for step in 0..checks {
        if Instant::now() >= deadline {
            break;
        }
        let pattern = (pattern_offset + step) % total_patterns;
        let mut code = pattern;
        let mut changed = false;
        for &cell in &cells {
            let o = (code % 6) as u8;
            code /= 6;
            changed |= o != orientation[cell];
            workspace.trial[cell] = o;
        }
        if !changed {
            continue;
        }
        let (end, length, bonuses) = board.trace_with_scratch(
            &workspace.trial,
            pair[0],
            &mut workspace.trace_scratch,
        );
        if end == pair[1] && length > old_length {
            let rotations: i32 = cells
                .iter()
                .map(|&cell| rotation_cost(board.initial[cell], workspace.trial[cell]))
                .sum();
            let value = length * (bonuses + 1);
            let net_gain = value as i64
                - old_value
                - board.M as i64 * (rotations - old_rotations) as i64;
            candidates.push((net_gain, value, rotations, pattern));
        }
        for &cell in &cells {
            workspace.trial[cell] = orientation[cell];
        }
    }
    candidates.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1), x.2));
    candidates.truncate(8);
    let affected = cells
        .iter()
        .fold(0u128, |mask, &cell| mask | differential.cell_masks[cell]);
    let mut best: Option<(Stats, Vec<u8>)> = None;
    for (_, _, _, mut code) in candidates {
        let mut candidate = orientation.to_vec();
        for &cell in &cells {
            candidate[cell] = (code % 6) as u8;
            code /= 6;
        }
        let moves = base.moves - old_rotations
            + cells
                .iter()
                .map(|&cell| rotation_cost(board.initial[cell], candidate[cell]))
                .sum::<i32>();
        let stats = differential.proposal(
            board,
            &candidate,
            base,
            moves,
            affected,
            &mut workspace.eval_scratch,
            &mut workspace.updates,
        );
        if best
            .as_ref()
            .map_or(true, |x| stats.quality() > x.0.quality())
        {
            best = Some((stats, candidate));
        }
    }
    best
}

fn low_bonus_reallocation(
    board: &Board,
    orientation: &mut Vec<u8>,
    start: Instant,
    deadline: Instant,
) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let initial = board.evaluate_with_scratch(orientation, &mut scratch);
    let initial_differential = DifferentialEval::new(board, orientation, &mut scratch);
    let bonus_limit = board.bonus.iter().filter(|&&x| x).count() / 4;
    let mut targets = Vec::new();
    for id in 0..board.pairs.len() {
        let value = initial_differential.contribution[id];
        let length = initial_differential.pair_cells[id].len();
        if value <= 0 || length == 0 {
            continue;
        }
        let bonuses = value as usize / length - 1;
        if bonuses > bonus_limit {
            continue;
        }
        let pair = board.pairs[id];
        let expected = expected_route_length_between_exits(board, pair[0], pair[1]);
        let excess = length as f64 - expected;
        if excess >= 1.5 {
            targets.push(((excess * 1024.0) as usize, length, bonuses, id));
        }
    }
    targets.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1), x.2, x.3));
    targets.truncate(LOW_BONUS_REALLOCATION_TARGETS);
    let jobs = targets.len();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15 ^ initial.score as u64);
    let mut local_workspace = LocalExtendWorkspace::new(board, orientation);
    let mut positive = 0usize;
    let mut extension_attempts = 0usize;
    let mut extension_accepts = 0usize;
    let mut best = initial;
    let mut best_orientation = orientation.clone();

    let route_phase_deadline =
        (start + Duration::from_millis(10 * jobs as u64)).min(deadline);
    let mut shortened_jobs = Vec::with_capacity(jobs);
    for &(_, old_length, bonuses, target_id) in &targets {
        let now = Instant::now();
        if now >= route_phase_deadline {
            break;
        }
        let mut work = orientation.clone();
        let mut domains = vec![0u8; board.valid.len()];
        for &cell in &board.valid_cells {
            domains[cell] = ALL_ORIENTATIONS;
        }
        for id in 0..board.pairs.len() {
            if id == target_id || initial_differential.contribution[id] <= 0 {
                continue;
            }
            let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
            for _ in 0..=3 * board.valid_count {
                let out = paired_dir(work[cell], enter);
                let mut required = 0u8;
                for o in 0..6u8 {
                    if paired_dir(o, enter) == out {
                        required |= 1 << o;
                    }
                }
                domains[cell] &= required;
                let Some((next, next_enter)) = board.next(cell, out) else {
                    break;
                };
                cell = next;
                enter = next_enter;
            }
        }
        let pair = board.pairs[target_id];
        let route_deadline = (now + Duration::from_millis(10)).min(route_phase_deadline);
        let Some(route) = find_route(
            board,
            &work,
            &domains,
            pair[0],
            pair[1],
            OUTER_LAYERS,
            false,
            None,
            None,
            route_deadline,
        ) else {
            continue;
        };
        if route.length >= old_length {
            continue;
        }
        let new_length = route.length;
        apply_route(&mut work, &mut domains, &route, true);
        shortened_jobs.push((old_length, new_length, bonuses, target_id, work));
    }
    let completed = shortened_jobs.len();
    let completed_jobs = shortened_jobs.len();
    for (index, (old_length, new_length, bonuses, target_id, mut work)) in
        shortened_jobs.into_iter().enumerate()
    {
        let now = Instant::now();
        if now >= deadline {
            break;
        }
        let jobs_left = completed_jobs - index;
        let job_deadline = now + deadline.duration_since(now) / jobs_left as u32;
        let mut work_stats = board.evaluate_with_scratch(&work, &mut scratch);
        let mut work_differential = DifferentialEval::new(board, &work, &mut scratch);
        while Instant::now() < job_deadline {
            extension_attempts += 1;
            let step_deadline =
                (Instant::now() + Duration::from_millis(LOW_BONUS_REALLOCATION_STEP_MS))
                    .min(job_deadline);
            let Some((stats, candidate)) = local_extend_candidate(
                board,
                &work,
                work_stats,
                &work_differential,
                &mut rng,
                &mut local_workspace,
                step_deadline,
            ) else {
                continue;
            };
            if stats.quality() > work_stats.quality() {
                work = candidate;
                work_stats = stats;
                work_differential = DifferentialEval::new(board, &work, &mut scratch);
                extension_accepts += 1;
            }
        }
        let target_connected = board.trace_pair(&work, target_id, &mut scratch, None).0 > 0;
        if target_connected && work_stats.matched >= initial.matched && board.tester_safe(&work) {
            positive += usize::from(work_stats.score > initial.score);
            if work_stats.quality() > best.quality() {
                best = work_stats;
                best_orientation = work;
                eprintln!(
                    "low_bonus_reallocation_improve id={} bonus={} length={}->{} score_delta={}",
                    target_id,
                    bonuses,
                    old_length,
                    new_length,
                    best.score - initial.score
                );
            }
        }
    }
    if best.quality() > initial.quality() {
        orientation.clone_from(&best_orientation);
    }
    eprintln!(
        "low_bonus_reallocation targets={} completed={} positive={} extensions={}/{} score_delta={} elapsed_ms={}",
        jobs,
        completed,
        positive,
        extension_accepts,
        extension_attempts,
        best.score - initial.score,
        start.elapsed().as_millis()
    );
}

fn constrain_path_connection(domains: &mut [u8], cell: usize, enter: usize, out: usize) {
    let mut required = 0u8;
    for o in 0..6u8 {
        if paired_dir(o, enter) == out {
            required |= 1 << o;
        }
    }
    domains[cell] &= required;
}

struct NonbonusShortenCandidate {
    pair_id: Option<usize>,
    source_exit: usize,
    target_exit: usize,
    old_length: usize,
    new_length: usize,
    work: Vec<u8>,
}

fn preserves_other_nonbonus_exit_paths(
    board: &Board,
    before: &[u8],
    after: &[u8],
    excluded: (usize, usize),
    scratch: &mut EvalScratch,
) -> bool {
    for source in 0..board.exits.len() {
        let (target, _, bonuses) = board.trace_with_scratch(before, source, scratch);
        if target == usize::MAX || source >= target || bonuses != 0 {
            continue;
        }
        if (source, target) == excluded {
            continue;
        }
        if board.trace_end(after, source) != target {
            return false;
        }
    }
    true
}

fn nonbonus_shorten_candidate(
    board: &Board,
    orientation: &[u8],
    differential: &DifferentialEval,
    scratch: &mut EvalScratch,
    wrong_selected: &mut usize,
    wrong_rate_denominator: usize,
    rng: &mut Rng,
    deadline: Instant,
) -> Option<NonbonusShortenCandidate> {
    let mut targets = Vec::new();
    for id in 0..board.pairs.len() {
        let length = differential.pair_cells[id].len();
        if length == 0 || differential.contribution[id] != length as i64 {
            continue;
        }
        let shortest = pair_distance(board, board.pairs[id]) + 1;
        if length > shortest {
            let pair = board.pairs[id];
            targets.push((length - shortest, length, Some(id), pair[0], pair[1]));
        }
    }
    // Wrong exit-to-exit connections have no pair contribution, so enumerate
    // the actual paths separately. Keep only one direction of each path.
    for source in 0..board.exits.len() {
        let (target, length, bonuses) = board.trace_with_scratch(orientation, source, scratch);
        if target == usize::MAX
            || source >= target
            || target == board.partner[source]
            || bonuses != 0
        {
            continue;
        }
        let shortest = hex_cell_distance(board.W, board.exits[source].0, board.exits[target].0) + 1;
        if length > shortest {
            targets.push((length - shortest, length, None, source, target));
        }
    }
    if targets.is_empty() {
        return None;
    }
    let has_correct = targets.iter().any(|target| target.2.is_some());
    let has_wrong = targets.iter().any(|target| target.2.is_none());
    let choose_wrong = has_wrong
        && (!has_correct || rng.usize(wrong_rate_denominator.max(1)) == 0);
    *wrong_selected += usize::from(choose_wrong);
    targets.retain(|target| target.2.is_none() == choose_wrong);
    targets.sort_unstable_by_key(|&(excess, length, pair_id, source, target)| {
        (Reverse(excess), Reverse(length), pair_id.is_none(), source, target)
    });
    let pick = rng.usize(targets.len().min(NONBONUS_SHORTEN_TOP_TARGETS));
    let (_, path_length, target_pair_id, source_exit, target_exit) = targets[pick];

    let (mut cell, mut enter) = board.exits[source_exit];
    let mut states = Vec::with_capacity(path_length);
    for step in 0..path_length {
        states.push((cell, enter));
        let out = paired_dir(orientation[cell], enter);
        if step + 1 == path_length {
            if board.next(cell, out).is_some()
                || board.exit_id[cell * 6 + out] as usize != target_exit
            {
                return None;
            }
            break;
        }
        let (next, next_enter) = board.next(cell, out)?;
        cell = next;
        enter = next_enter;
    }

    // Pick two points whose old subpath is longer than the geometric lower
    // bound. Short paths are scanned completely; long paths use random pairs.
    let mut best_segment: Option<(usize, usize, usize, usize)> = None;
    let consider = |i: usize, j: usize, best: &mut Option<(usize, usize, usize, usize)>| {
        let old_segment = j - i + 1;
        let lower = hex_cell_distance(board.W, states[i].0, states[j].0) + 1;
        if old_segment <= lower {
            return;
        }
        let candidate = (old_segment - lower, old_segment, i, j);
        if best
            .as_ref()
            .is_none_or(|&(excess, span, _, _)| (candidate.0, candidate.1) > (excess, span))
        {
            *best = Some(candidate);
        }
    };
    if path_length <= 64 {
        for i in 0..path_length.saturating_sub(2) {
            for j in i + 2..path_length {
                consider(i, j, &mut best_segment);
            }
        }
    } else {
        for _ in 0..128 {
            let i = rng.usize(path_length - 2);
            let j = i + 2 + rng.usize(path_length - i - 2);
            consider(i, j, &mut best_segment);
        }
    }
    let (_, old_segment_length, segment_start, segment_end) = best_segment?;

    let mut work = orientation.to_vec();
    let mut domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        domains[cell] = ALL_ORIENTATIONS;
    }
    let protected_bonus = (0..board.pairs.len())
        .filter(|&id| {
            let length = differential.pair_cells[id].len();
            length > 0 && differential.contribution[id] > length as i64
        })
        .max_by_key(|&id| {
            let length = differential.pair_cells[id].len() as i64;
            (
                differential.contribution[id] / length,
                differential.contribution[id],
            )
        });
    // Preserve every other bonus-free exit path, including wrong connections.
    for source in 0..board.exits.len() {
        let (target, _, bonuses) = board.trace_with_scratch(orientation, source, scratch);
        if target == usize::MAX || source >= target || bonuses != 0 {
            continue;
        }
        if source == source_exit && target == target_exit {
            continue;
        }
        let (mut cell, mut enter) = board.exits[source];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(work[cell], enter);
            constrain_path_connection(&mut domains, cell, enter, out);
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }
    // Keep one high-value bonus trunk stable as a merge destination.
    if let Some(id) = protected_bonus {
        let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(work[cell], enter);
            constrain_path_connection(&mut domains, cell, enter, out);
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }
    // Keep the prefix and suffix of the selected path unchanged. Only the
    // inclusive segment between the two selected ports is released.
    for (index, &(cell, enter)) in states.iter().enumerate() {
        if index < segment_start || index > segment_end {
            let out = paired_dir(work[cell], enter);
            constrain_path_connection(&mut domains, cell, enter, out);
        }
    }
    let start = states[segment_start];
    let target_cell = states[segment_end].0;
    let target_out = paired_dir(work[target_cell], states[segment_end].1);
    let route = find_segment_route(
        board,
        &work,
        &domains,
        start,
        (target_cell, target_out),
        deadline,
    )?;
    if route.length >= old_segment_length || route.bonuses != 0 {
        return None;
    }
    let new_length = route.length;
    apply_route(&mut work, &mut domains, &route, true);
    Some(NonbonusShortenCandidate {
        pair_id: target_pair_id,
        source_exit,
        target_exit,
        old_length: old_segment_length,
        new_length,
        work,
    })
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
    let connected_mask =
        differential
            .contribution
            .iter()
            .enumerate()
            .fold(
                0u128,
                |mask, (id, &x)| {
                    if x > 0 {
                        mask | (1u128 << id)
                    } else {
                        mask
                    }
                },
            );
    let cells: Vec<usize> = (0..board.valid.len())
        .filter(|&cell| {
            if !board.valid[cell] {
                return false;
            }
            let paths = (differential.cell_masks[cell] & connected_mask).count_ones();
            paths == 1 || paths == 2
        })
        .collect();
    if cells.is_empty() {
        return None;
    }
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
        if Instant::now() >= deadline {
            break;
        }
        let center = cells[rng.usize(cells.len())];
        let mut beam: Vec<(Stats, Vec<u8>, Vec<usize>, u128, u128)> = Vec::new();
        for oc in 0u8..6 {
            if oc == orientation[center] {
                continue;
            }
            let mut candidate = orientation.to_vec();
            candidate[center] = oc;
            let moves = base.moves - rotation_cost(board.initial[center], orientation[center])
                + rotation_cost(board.initial[center], oc);
            let affected = differential.cell_masks[center];
            let stats = differential.proposal(
                board,
                &candidate,
                base,
                moves,
                affected,
                scratch,
                &mut updates,
            );
            if stats.matched < base.matched {
                let lost = updates.iter().fold(0u128, |mask, &(id, value)| {
                    if differential.contribution[id] > 0 && value == 0 {
                        mask | (1u128 << id)
                    } else {
                        mask
                    }
                });
                beam.push((stats, candidate, vec![center], affected, lost));
            }
        }
        beam.sort_unstable_by_key(|x| {
            (
                Reverse(x.0.matched),
                Reverse(x.0.score),
                Reverse(x.0.total),
                x.0.moves,
            )
        });
        beam.truncate(beam_width);

        for _depth in 2..=max_depth {
            if beam.is_empty() || Instant::now() >= deadline {
                break;
            }
            let mut next_beam = Vec::new();
            for (_, state, touched, affected, lost) in beam.into_iter() {
                let mut ranked_pool: Vec<(usize, u32, usize)> = Vec::new();
                let mut pool_cells = Vec::new();
                for id in 0..board.pairs.len() {
                    if lost >> id & 1 == 0 {
                        continue;
                    }
                    route.clear();
                    board.trace_pair(&state, id, scratch, Some(&mut route));
                    let touched_positions: Vec<usize> = route
                        .iter()
                        .enumerate()
                        .filter_map(|(pos, cell)| touched.contains(cell).then_some(pos))
                        .collect();
                    for (pos, &cell) in route.iter().enumerate() {
                        if touched.contains(&cell) {
                            continue;
                        }
                        let distance = touched_positions
                            .iter()
                            .map(|&at| pos.abs_diff(at))
                            .min()
                            .unwrap_or(usize::MAX / 2);
                        let damage = (differential.cell_masks[cell] & connected_mask).count_ones();
                        if candidate_rank[cell].0 == usize::MAX {
                            pool_cells.push(cell);
                        }
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
                        if o == state[cell] {
                            continue;
                        }
                        if Instant::now() >= deadline {
                            break;
                        }
                        work[cell] = o;
                        let moves = base.moves
                            + touched
                                .iter()
                                .map(|&changed| {
                                    rotation_cost(board.initial[changed], state[changed])
                                        - rotation_cost(
                                            board.initial[changed],
                                            orientation[changed],
                                        )
                                })
                                .sum::<i32>()
                            + rotation_cost(board.initial[cell], o)
                            - rotation_cost(board.initial[cell], orientation[cell]);
                        let next_affected = affected | differential.cell_masks[cell];
                        let stats = differential.proposal(
                            board,
                            &work,
                            base,
                            moves,
                            next_affected,
                            scratch,
                            &mut updates,
                        );
                        let mut changed = touched.clone();
                        changed.push(cell);
                        if stats.matched >= base.matched {
                            if best
                                .as_ref()
                                .map_or(true, |x| stats.quality() > x.0.quality())
                            {
                                best = Some((stats, work.clone()));
                            }
                        } else {
                            let next_lost = updates.iter().fold(0u128, |mask, &(id, value)| {
                                if differential.contribution[id] > 0 && value == 0 {
                                    mask | (1u128 << id)
                                } else {
                                    mask
                                }
                            });
                            next_beam.push((
                                stats,
                                work.clone(),
                                changed,
                                next_affected,
                                next_lost,
                            ));
                            if next_beam.len() > 2 * beam_width {
                                next_beam.sort_unstable_by_key(|x| {
                                    (
                                        Reverse(x.0.matched),
                                        Reverse(x.0.score),
                                        Reverse(x.0.total),
                                        x.0.moves,
                                    )
                                });
                                next_beam.truncate(beam_width);
                            }
                        }
                        work[cell] = state[cell];
                    }
                }
            }
            next_beam.sort_unstable_by_key(|x| {
                (
                    Reverse(x.0.matched),
                    Reverse(x.0.score),
                    Reverse(x.0.total),
                    x.0.moves,
                )
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

fn preserves_original_matches(differential: &DifferentialEval, updates: &[(usize, i64)]) -> bool {
    updates
        .iter()
        .all(|&(id, value)| differential.contribution[id] == 0 || value > 0)
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
    let mut candidates: Vec<(usize, usize, usize, Vec<usize>)> = Vec::new();
    let cells_count = board.valid.len();
    let mut goal_stamp = vec![false; cells_count];
    let mut seen = vec![false; cells_count];
    let mut parent = vec![usize::MAX; cells_count];
    let mut queue = VecDeque::new();

    for id in 0..board.pairs.len() {
        if differential.contribution[id] > 0 {
            continue;
        }
        board.trace_exit_cells(orientation, board.pairs[id][0], &mut path_a);
        board.trace_exit_cells(orientation, board.pairs[id][1], &mut path_b);
        for &cell in &path_b {
            goal_stamp[cell] = true;
        }
        seen.fill(false);
        parent.fill(usize::MAX);
        queue.clear();
        for &cell in &path_a {
            if !seen[cell] {
                seen[cell] = true;
                queue.push_back(cell);
            }
        }
        let mut goal = usize::MAX;
        while let Some(cell) = queue.pop_front() {
            if goal_stamp[cell] {
                goal = cell;
                break;
            }
            for side in 0..6 {
                let Some((next, _)) = board.next(cell, side) else {
                    continue;
                };
                if !seen[next] {
                    seen[next] = true;
                    parent[next] = cell;
                    queue.push_back(next);
                }
            }
        }
        for &cell in &path_b {
            goal_stamp[cell] = false;
        }
        if goal == usize::MAX {
            continue;
        }
        let mut corridor = Vec::new();
        loop {
            corridor.push(goal);
            if parent[goal] == usize::MAX {
                break;
            }
            goal = parent[goal];
        }
        if corridor.len() <= 5 {
            candidates.push((
                pair_distance(board, board.pairs[id]),
                corridor.len(),
                id,
                corridor,
            ));
        }
    }
    candidates.sort_unstable_by_key(|x| (x.0, x.1));

    let mut best: Option<(Stats, Vec<u8>, usize, usize, usize, usize)> = None;
    let mut trials = 0usize;
    let mut completed = 0usize;
    let mut updates = Vec::with_capacity(board.pairs.len());
    for (_, _, target, corridor) in candidates.into_iter().take(CONNECT_REPAIR_TARGETS) {
        if Instant::now() >= deadline {
            break;
        }
        let mut in_region = vec![false; cells_count];
        let mut region = Vec::new();
        for &cell in &corridor {
            if !in_region[cell] {
                in_region[cell] = true;
                region.push(cell);
            }
            for side in 0..6 {
                if let Some((next, _)) = board.next(cell, side) {
                    if !in_region[next] {
                        in_region[next] = true;
                        region.push(next);
                    }
                }
            }
        }
        if region.len() > 25 {
            continue;
        }
        trials += 1;
        region.sort_unstable();
        // Monotone region indices avoid generating the same changed subset in
        // different orders. Intermediate states may lose matches; only a complete
        // transaction that adds a match and improves the exact score is returned.
        // Store only the sparse changes of each branch.  A single reusable board
        // is materialized with apply/revert, and only paths touching cells that
        // this branch actually changed are retraced.
        let mut beam: Vec<(Stats, i64, i32, usize, usize, u128, Vec<(usize, u8)>)> =
            vec![(base, 0, base.moves, 0, 0, 1u128 << target, Vec::new())];
        let mut work = orientation.to_vec();
        for _depth in 1..=region.len() {
            if Instant::now() >= deadline {
                break;
            }
            let mut next_beam = Vec::new();
            for (_, _, moves, next_at, broken_peak, affected, changes) in beam.into_iter() {
                for &(cell, o) in &changes {
                    work[cell] = o;
                }
                for ri in next_at..region.len() {
                    let cell = region[ri];
                    for o in 0u8..6 {
                        if o == orientation[cell] {
                            continue;
                        }
                        let old = work[cell];
                        work[cell] = o;
                        let next_moves = moves - rotation_cost(board.initial[cell], old)
                            + rotation_cost(board.initial[cell], o);
                        let next_affected = affected | differential.cell_masks[cell];
                        let stats = differential.proposal(
                            board,
                            &work,
                            base,
                            next_moves,
                            next_affected,
                            scratch,
                            &mut updates,
                        );
                        let target_value = updates
                            .iter()
                            .find_map(|&(id, value)| (id == target).then_some(value))
                            .unwrap_or(0);
                        let preserves_all =
                            target_value > 0 && preserves_original_matches(differential, &updates);
                        if preserves_all {
                            completed += 1;
                        }
                        let next_broken_peak =
                            broken_peak.max(base.matched.saturating_sub(stats.matched));
                        if preserves_all
                            && stats.matched >= base.matched + 1
                            && stats.score > base.score
                        {
                            if best.as_ref().map_or(true, |x| stats.score > x.0.score) {
                                let changed = changes.len() + 1;
                                let mut candidate = orientation.to_vec();
                                for &(changed_cell, changed_o) in &changes {
                                    candidate[changed_cell] = changed_o;
                                }
                                candidate[cell] = o;
                                best = Some((
                                    stats,
                                    candidate,
                                    target,
                                    region.len(),
                                    changed,
                                    next_broken_peak,
                                ));
                            }
                        }
                        let mut next_changes = changes.clone();
                        next_changes.push((cell, o));
                        next_beam.push((
                            stats,
                            target_value,
                            next_moves,
                            ri + 1,
                            next_broken_peak,
                            next_affected,
                            next_changes,
                        ));
                        work[cell] = old;
                    }
                }
                for &(cell, _) in &changes {
                    work[cell] = orientation[cell];
                }
            }
            next_beam.sort_unstable_by_key(|x| {
                (
                    Reverse(x.1 > 0),
                    Reverse(x.0.matched),
                    Reverse(x.0.score),
                    Reverse(x.0.total),
                    x.0.moves,
                )
            });
            next_beam.truncate(CONNECT_REPAIR_BEAM);
            beam = next_beam;
            if beam.is_empty() {
                break;
            }
        }
    }
    if let Some((_, candidate, target, area, changed, broken_peak)) = best {
        ConnectRepairResult {
            candidate: Some(candidate),
            trials,
            completed,
            target,
            area,
            changed,
            broken_peak,
        }
    } else {
        ConnectRepairResult {
            candidate: None,
            trials,
            completed,
            target: usize::MAX,
            area: 0,
            changed: 0,
            broken_peak: 0,
        }
    }
}

fn compact_metrics(
    board: &Board,
    orientation: &[u8],
    representative_mask: u128,
    scratch: &mut EvalScratch,
) -> CompactMetrics {
    let mut moves = 0i32;
    for &cell in &board.valid_cells {
        moves += rotation_cost(board.initial[cell], orientation[cell]);
    }
    let mut matched = 0usize;
    let mut total_value = 0i64;
    let mut representative_value = 0i64;
    let mut compressible_length = 0usize;
    let exit_epoch = scratch.next_exit_epoch(board.exits.len());
    let mut unmatched_length = 0usize;
    for start in 0..board.exits.len() {
        if scratch.exit_stamp[start] == exit_epoch {
            continue;
        }
        let (end, length, bonuses) = board.trace_with_scratch(orientation, start, scratch);
        scratch.exit_stamp[start] = exit_epoch;
        if end >= board.exits.len() {
            continue;
        }
        scratch.exit_stamp[end] = exit_epoch;
        if board.partner[start] == end {
            let id = board.pair_id_by_exit[start];
            matched += 1;
            let value = (length * (bonuses + 1)) as i64;
            total_value += value;
            if representative_mask >> id & 1 != 0 {
                representative_value += value;
            } else {
                compressible_length += length;
            }
        } else {
            unmatched_length += length;
        }
    }
    let energy = matched as i64 * 1_000_000_000 + representative_value * 10_000
        - compressible_length as i64 * 200
        - unmatched_length as i64 * 300
        - board.M as i64 * moves as i64 * 200;
    CompactMetrics {
        energy,
        matched,
        total_value,
        representative_value,
        compressible_length,
        unmatched_length,
        moves,
    }
}

fn representative_paths(board: &Board, orientation: &[u8]) -> u128 {
    let mut candidates = Vec::new();
    let mut scratch = EvalScratch::new(board.valid.len());
    for (id, pair) in board.pairs.iter().enumerate() {
        let (end, length, bonuses) = board.trace_with_scratch(orientation, pair[0], &mut scratch);
        if end == pair[1] && bonuses > 0 {
            candidates.push((length * (bonuses + 1), id));
        }
    }
    candidates.sort_unstable_by_key(|x| Reverse(x.0));
    candidates
        .into_iter()
        .take(COMPACT_REPRESENTATIVES)
        .fold(0u128, |mask, (_, id)| mask | (1u128 << id))
}

fn compact_paths_sa(board: &Board, orientation: &mut Vec<u8>, start: Instant, deadline: Instant) {
    if start >= deadline {
        return;
    }
    let cells = &board.valid_cells;
    let mut rng = Rng(0x6a09e667f3bcc909 ^ board.W as u64 ^ ((board.M as u64) << 24));
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut current = orientation.clone();
    let representative_mask = representative_paths(board, &current);
    let initial_metrics = compact_metrics(board, &current, representative_mask, &mut scratch);
    let mut current_metrics = initial_metrics;
    let true_score = |m: CompactMetrics| {
        (m.matched as i64 * (m.total_value - board.M as i64 * m.moves as i64)).max(0)
    };
    let mut output = current.clone();
    let mut output_metrics = current_metrics;
    let mut output_score = true_score(current_metrics);
    let span = deadline
        .saturating_duration_since(start)
        .as_secs_f64()
        .max(0.001);
    let mut iterations = 0usize;
    let mut now = start;
    let mut temperature = COMPACT_SA_START_TEMP;
    let mut next_segment = start + Duration::from_millis(COMPACT_SEGMENT_INTERVAL_MS);
    let mut segment_attempts = 0usize;
    let mut segment_completed = 0usize;
    let mut segment_accepted = 0usize;
    let mut segment_wrong_selected = 0usize;
    let mut segment_wrong_accepted = 0usize;
    while now < deadline {
        if iterations & 31 == 0 {
            now = Instant::now();
            if now >= deadline {
                break;
            }
            let frac = (now.duration_since(start).as_secs_f64() / span).min(1.0);
            temperature = COMPACT_SA_START_TEMP.powf(1.0 - frac) * COMPACT_SA_END_TEMP.powf(frac);
        }
        if now >= next_segment {
            next_segment += Duration::from_millis(COMPACT_SEGMENT_INTERVAL_MS);
            segment_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(NONBONUS_SHORTEN_BUDGET_MS)).min(deadline);
            let differential = DifferentialEval::new(board, &current, &mut scratch);
            if let Some(shorten) = nonbonus_shorten_candidate(
                board,
                &current,
                &differential,
                &mut scratch,
                &mut segment_wrong_selected,
                1,
                &mut rng,
                local_deadline,
            ) {
                segment_completed += 1;
                let target_preserved =
                    board.trace_end(&shorten.work, shorten.source_exit) == shorten.target_exit;
                let paths_preserved = preserves_other_nonbonus_exit_paths(
                    board,
                    &current,
                    &shorten.work,
                    (shorten.source_exit, shorten.target_exit),
                    &mut scratch,
                );
                if target_preserved && paths_preserved {
                    let next_metrics =
                        compact_metrics(board, &shorten.work, representative_mask, &mut scratch);
                    let delta = next_metrics.energy - current_metrics.energy;
                    if metropolis_accept(&mut rng, delta as f64, temperature) {
                        let wrong = shorten.pair_id.is_none();
                        current = shorten.work;
                        current_metrics = next_metrics;
                        segment_accepted += 1;
                        segment_wrong_accepted += usize::from(wrong);
                        let score = true_score(next_metrics);
                        if next_metrics.matched >= initial_metrics.matched
                            && score > output_score
                            && board.tester_safe(&current)
                        {
                            output_score = score;
                            output_metrics = next_metrics;
                            output.clone_from(&current);
                        }
                    }
                }
            }
            now = Instant::now();
            iterations += 1;
            continue;
        }
        let changes = 1 + rng.usize(if cells.len() < 100 { 3 } else { 2 });
        let mut undo: Vec<(usize, u8)> = Vec::with_capacity(changes);
        for _ in 0..changes {
            let cell = cells[rng.usize(cells.len())];
            if undo.iter().any(|&(x, _)| x == cell) {
                continue;
            }
            let old = current[cell];
            let mut next = rng.usize(5) as u8;
            if next >= old {
                next += 1;
            }
            undo.push((cell, old));
            current[cell] = next;
        }
        let next_metrics = compact_metrics(board, &current, representative_mask, &mut scratch);
        let delta = next_metrics.energy - current_metrics.energy;
        if metropolis_accept(&mut rng, delta as f64, temperature) {
            current_metrics = next_metrics;
            let score = true_score(next_metrics);
            if next_metrics.matched >= initial_metrics.matched
                && score > output_score
                && board.tester_safe(&current)
            {
                output_score = score;
                output_metrics = next_metrics;
                output.clone_from(&current);
            }
        } else {
            for &(cell, old) in &undo {
                current[cell] = old;
            }
        }
        iterations += 1;
    }
    orientation.clone_from(&output);
    eprintln!("compact_sa iterations={} temp={}->{} representatives={} segments={}/{}/{} wrong_selected={} wrong_accepted={} k={}->{} representative_value={}->{} compressible_length={}->{} unmatched_length={}->{} moves={}->{}",
        iterations, COMPACT_SA_START_TEMP, COMPACT_SA_END_TEMP,
        representative_mask.count_ones(),
        segment_accepted, segment_completed, segment_attempts,
        segment_wrong_selected, segment_wrong_accepted,
        initial_metrics.matched, output_metrics.matched,
        initial_metrics.representative_value, output_metrics.representative_value,
        initial_metrics.compressible_length, output_metrics.compressible_length,
        initial_metrics.unmatched_length, output_metrics.unmatched_length,
        initial_metrics.moves, output_metrics.moves);
}

fn multi_trunk_lns(board: &Board, orientation: &mut Vec<u8>, start: Instant, deadline: Instant) {
    if start >= deadline {
        return;
    }
    let mut scratch = EvalScratch::new(board.valid.len());
    let initial = board.evaluate_with_scratch(orientation, &mut scratch);
    let differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut matched = Vec::new();
    for id in 0..board.pairs.len() {
        let value = differential.contribution[id];
        if value <= 0 {
            continue;
        }
        let (_, length) = board.trace_pair(orientation, id, &mut scratch, None);
        let bonuses = if length > 0 { value / length - 1 } else { -1 };
        matched.push((bonuses, value, length, id));
    }
    matched.sort_unstable_by_key(|&(bonuses, value, length, id)| {
        (Reverse(bonuses), Reverse(value), Reverse(length), id)
    });
    let heroes: Vec<usize> = matched
        .iter()
        .take(MULTI_TRUNK_LNS_HEROES)
        .map(|&(_, _, _, id)| id)
        .collect();
    if heroes.len() < 2 {
        eprintln!(
            "multi_trunk_lns heroes={} victims=0 hero_done=0 restored=0 k={}->{} score_delta=0 accepted=false elapsed_ms={}",
            heroes.len(), initial.matched, initial.matched, start.elapsed().as_millis()
        );
        return;
    }

    let mut hero_cells = vec![false; board.valid.len()];
    for &id in &heroes {
        for &cell in &differential.pair_cells[id] {
            hero_cells[cell] = true;
        }
    }
    let mut near_hero = hero_cells.clone();
    for &cell in &board.valid_cells {
        if !hero_cells[cell] {
            continue;
        }
        for side in 0..6 {
            if let Some((next, _)) = board.next(cell, side) {
                near_hero[next] = true;
            }
        }
    }
    let mut victim_candidates = Vec::new();
    for &(bonuses, value, length, id) in &matched {
        if heroes.contains(&id) {
            continue;
        }
        let mut overlap = 0usize;
        let mut proximity = 0usize;
        for &cell in &differential.pair_cells[id] {
            overlap += usize::from(hero_cells[cell]);
            proximity += usize::from(near_hero[cell]);
        }
        victim_candidates.push((overlap, proximity, bonuses, value, length, id));
    }
    victim_candidates.sort_unstable_by_key(|&(overlap, proximity, bonuses, value, length, id)| {
        (
            Reverse(overlap),
            Reverse(proximity),
            bonuses,
            value,
            length,
            id,
        )
    });
    let mut victims: Vec<usize> = victim_candidates
        .iter()
        .take(MULTI_TRUNK_LNS_VICTIMS)
        .map(|&(_, _, _, _, _, id)| id)
        .collect();
    victims.sort_unstable_by_key(|&id| pair_distance(board, board.pairs[id]));

    let mut work = orientation.clone();
    let mut domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        domains[cell] = ALL_ORIENTATIONS;
    }
    let selected = heroes
        .iter()
        .chain(victims.iter())
        .fold(0u128, |mask, &id| mask | (1u128 << id));
    // Preserve every non-ruined matched path as local (enter,out) constraints.
    // Their unused strands remain free, so the hero group can still share tiles.
    for id in 0..board.pairs.len() {
        if differential.contribution[id] <= 0 || selected >> id & 1 != 0 {
            continue;
        }
        let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(work[cell], enter);
            let mut required = 0u8;
            for o in 0..6u8 {
                if paired_dir(o, enter) == out {
                    required |= 1 << o;
                }
            }
            domains[cell] &= required;
            debug_assert!(domains[cell] != 0 && domains[cell] >> work[cell] & 1 != 0);
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }

    let total_span = deadline.saturating_duration_since(start);
    let hero_phase_deadline =
        (start + total_span * MULTI_TRUNK_LNS_HERO_PERCENT / 100).min(deadline);
    let mut hero_done = 0usize;
    for (index, &id) in heroes.iter().enumerate() {
        let now = Instant::now();
        if now >= hero_phase_deadline {
            break;
        }
        let left = heroes.len() - index;
        let route_deadline = now + hero_phase_deadline.duration_since(now) / left as u32;
        let pair = board.pairs[id];
        let damage = board.damage_model(&work);
        if let Some(route) = find_route(
            board,
            &work,
            &domains,
            pair[0],
            pair[1],
            OUTER_LAYERS,
            true,
            Some(&damage),
            None,
            route_deadline,
        ) {
            apply_route(&mut work, &mut domains, &route, true);
            hero_done += 1;
        }
    }

    let mut restored = 0usize;
    for (index, &id) in victims.iter().enumerate() {
        let now = Instant::now();
        if now >= deadline {
            break;
        }
        let left = victims.len() - index;
        let route_deadline = now + deadline.duration_since(now) / left as u32;
        let pair = board.pairs[id];
        if let Some(route) = find_route(
            board,
            &work,
            &domains,
            pair[0],
            pair[1],
            OUTER_LAYERS,
            false,
            None,
            None,
            route_deadline,
        ) {
            apply_route(&mut work, &mut domains, &route, true);
            restored += 1;
        }
    }
    if Instant::now() < deadline {
        resolve_domains(board, &mut work, &domains, deadline);
    }
    let candidate = board.evaluate_with_scratch(&work, &mut scratch);
    let accepted = candidate.score > initial.score && board.tester_safe(&work);
    if accepted {
        orientation.clone_from(&work);
    }
    eprintln!(
        "multi_trunk_lns heroes={} victims={} hero_done={} restored={} k={}->{} score_delta={} accepted={} elapsed_ms={}",
        heroes.len(),
        victims.len(),
        hero_done,
        restored,
        initial.matched,
        candidate.matched,
        candidate.score - initial.score,
        accepted,
        start.elapsed().as_millis()
    );
}

struct TwoPathLnsResult {
    candidate: Option<Vec<u8>>,
    trials: usize,
    completed: usize,
    improving: usize,
}

// Treat the temporary k-2/k-1 states as an implementation detail: every
// returned candidate has both selected paths rebuilt and is evaluated exactly.
fn two_path_lns_candidate(
    board: &Board,
    orientation: &[u8],
    deadline: Instant,
) -> TwoPathLnsResult {
    let mut result = TwoPathLnsResult {
        candidate: None,
        trials: 0,
        completed: 0,
        improving: 0,
    };
    if Instant::now() >= deadline {
        return result;
    }

    let mut scratch = EvalScratch::new(board.valid.len());
    let base = board.evaluate_with_scratch(orientation, &mut scratch);
    let differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut matched = Vec::new();
    for id in 0..board.pairs.len() {
        let value = differential.contribution[id];
        if value <= 0 {
            continue;
        }
        let length = differential.pair_cells[id].len();
        let bonuses = if length > 0 { value / length as i64 - 1 } else { -1 };
        matched.push((id, value, length, bonuses));
    }
    if matched.len() < 2 {
        return result;
    }

    // Favor paths which can exchange nearby tile resources.  Bonus/value
    // asymmetry also exposes the useful low-value-path + hero-path transaction.
    let mut ranked_pairs = Vec::new();
    let mut marked = vec![false; board.valid.len()];
    let mut near = vec![false; board.valid.len()];
    for a in 0..matched.len() {
        let (id_a, value_a, length_a, bonuses_a) = matched[a];
        for &cell in &differential.pair_cells[id_a] {
            marked[cell] = true;
            near[cell] = true;
            for side in 0..6 {
                if let Some((next, _)) = board.next(cell, side) {
                    near[next] = true;
                }
            }
        }
        for &(id_b, value_b, length_b, bonuses_b) in &matched[a + 1..] {
            let overlap = differential.pair_cells[id_b]
                .iter()
                .filter(|&&cell| marked[cell])
                .count();
            let proximity = differential.pair_cells[id_b]
                .iter()
                .filter(|&&cell| near[cell])
                .count();
            let bonus_gap = bonuses_a.abs_diff(bonuses_b);
            let length_sum = length_a + length_b;
            let combined_value = value_a + value_b;
            ranked_pairs.push((
                overlap,
                proximity,
                bonus_gap,
                length_sum,
                Reverse(combined_value),
                id_a,
                id_b,
            ));
        }
        for &cell in &differential.pair_cells[id_a] {
            marked[cell] = false;
            near[cell] = false;
            for side in 0..6 {
                if let Some((next, _)) = board.next(cell, side) {
                    near[next] = false;
                }
            }
        }
    }
    ranked_pairs.sort_unstable_by_key(|x| {
        (Reverse(x.0), Reverse(x.1), Reverse(x.2), Reverse(x.3), x.4, x.5, x.6)
    });
    ranked_pairs.truncate(TWO_PATH_LNS_PAIR_CANDIDATES);

    let jobs = ranked_pairs.len() * 2;
    let mut job = 0usize;
    let mut best: Option<(Stats, Vec<u8>)> = None;
    for &(_, _, _, _, _, id_a, id_b) in &ranked_pairs {
        for reverse_order in [false, true] {
            let now = Instant::now();
            if now >= deadline {
                break;
            }
            result.trials += 1;
            let jobs_left = (jobs - job).max(1);
            job += 1;
            let transaction_deadline =
                (now + deadline.duration_since(now) / jobs_left as u32).min(deadline);
            let selected = (1u128 << id_a) | (1u128 << id_b);
            let mut work = orientation.to_vec();
            let mut domains = vec![0u8; board.valid.len()];
            for &cell in &board.valid_cells {
                domains[cell] = ALL_ORIENTATIONS;
            }

            // Preserve all other matched paths as local enter->out constraints.
            for id in 0..board.pairs.len() {
                if differential.contribution[id] <= 0 || selected >> id & 1 != 0 {
                    continue;
                }
                let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
                for _ in 0..=3 * board.valid_count {
                    let out = paired_dir(work[cell], enter);
                    let mut required = 0u8;
                    for o in 0..6u8 {
                        if paired_dir(o, enter) == out {
                            required |= 1 << o;
                        }
                    }
                    domains[cell] &= required;
                    let Some((next, next_enter)) = board.next(cell, out) else {
                        break;
                    };
                    cell = next;
                    enter = next_enter;
                }
            }

            let order = if reverse_order { [id_b, id_a] } else { [id_a, id_b] };
            let mut rebuilt = 0usize;
            for (index, &id) in order.iter().enumerate() {
                let route_now = Instant::now();
                if route_now >= transaction_deadline {
                    break;
                }
                let routes_left = 2 - index;
                let route_deadline = route_now
                    + transaction_deadline.duration_since(route_now) / routes_left as u32;
                let pair = board.pairs[id];
                let Some(route) = find_route(
                    board,
                    &work,
                    &domains,
                    pair[0],
                    pair[1],
                    OUTER_LAYERS,
                    false,
                    None,
                    None,
                    route_deadline,
                ) else {
                    break;
                };
                apply_route(&mut work, &mut domains, &route, true);
                rebuilt += 1;
            }
            if rebuilt != 2 {
                continue;
            }
            if Instant::now() < transaction_deadline {
                resolve_domains(board, &mut work, &domains, transaction_deadline);
            }
            let stats = board.evaluate_with_scratch(&work, &mut scratch);
            let both_connected = [id_a, id_b].iter().all(|&id| {
                board.trace_pair(&work, id, &mut scratch, None).0 > 0
            });
            if !both_connected || stats.matched < base.matched || !board.tester_safe(&work) {
                continue;
            }
            result.completed += 1;
            result.improving += usize::from(stats.score > base.score);
            if best.as_ref().map_or(true, |x| stats.quality() > x.0.quality()) {
                best = Some((stats, work));
            }
        }
    }
    result.candidate = best.map(|x| x.1);
    result
}

fn build_multitile_choices(board: &Board, orientation: &[u8]) -> Vec<MultiTileChoice> {
    let started = Instant::now();
    let mut scratch = EvalScratch::new(board.valid.len());
    let differential = DifferentialEval::new(board, orientation, &mut scratch);
    let base = board.evaluate_with_scratch(orientation, &mut scratch);
    let triangles = collect_triangles(board);
    let mut work = orientation.to_vec();
    let mut updates = Vec::new();
    let mut direct_cells = Vec::new();
    let mut direct_pair_stats = Vec::new();
    let mut horizontal_pairs = 0usize;
    let mut candidates: Vec<(i64, i64, MultiTileChoice)> = Vec::new();
    for id in 0..board.pairs.len() {
        direct_cells.clear();
        let pair = board.pairs[id];
        let (start_cell, start_side) = board.exits[pair[0]];
        let (end_cell, end_side) = board.exits[pair[1]];
        if start_cell != end_cell
            || !(0..6u8).any(|o| paired_dir(o, start_side) == end_side)
            || differential.contribution[id] <= 0
        {
            continue;
        }
        direct_cells.push(start_cell);
        let direct_length = 1i64;
        horizontal_pairs += 1;
        let (_, current_length) = board.trace_pair(orientation, id, &mut scratch, None);
        if current_length > direct_length {
            direct_pair_stats.push((pair[0], pair[1], current_length));
        }
        for &cells in &triangles {
            if !cells.iter().any(|cell| direct_cells.contains(cell)) {
                continue;
            }
            let current = [
                orientation[cells[0]],
                orientation[cells[1]],
                orientation[cells[2]],
            ];
            let mut affected = 1u128 << id;
            let mut current_local_moves = 0i32;
            for &cell in &cells {
                affected |= differential.cell_masks[cell];
                current_local_moves += rotation_cost(board.initial[cell], orientation[cell]);
            }
            for code in 0..216usize {
                let local = [(code % 6) as u8, (code / 6 % 6) as u8, (code / 36) as u8];
                if local == current {
                    continue;
                }
                let mut local_moves = 0i32;
                for (i, &cell) in cells.iter().enumerate() {
                    work[cell] = local[i];
                    local_moves += rotation_cost(board.initial[cell], local[i]);
                }
                let (target_value, target_length) = board.trace_pair(&work, id, &mut scratch, None);
                if target_value <= 0 || target_length > direct_length {
                    continue;
                }
                let next = differential.proposal(
                    board,
                    &work,
                    base,
                    base.moves - current_local_moves + local_moves,
                    affected,
                    &mut scratch,
                    &mut updates,
                );
                let other_gain: i64 = updates
                    .iter()
                    .filter(|&&(other, value)| {
                        other != id && value > differential.contribution[other]
                    })
                    .map(|&(other, value)| value - differential.contribution[other])
                    .sum();
                if next.matched >= base.matched && next.score > base.score && other_gain > 0 {
                    candidates.push((
                        next.score - base.score,
                        other_gain,
                        MultiTileChoice {
                            cells,
                            variants: [current, local],
                            target_pair: pair,
                        },
                    ));
                }
            }
            for (i, &cell) in cells.iter().enumerate() {
                work[cell] = current[i];
            }
        }
    }
    candidates.sort_unstable_by_key(|x| (Reverse(x.0), Reverse(x.1)));
    let raw = candidates.len();
    let mut used = vec![false; board.valid.len()];
    let mut choices = Vec::new();
    for (_, _, choice) in candidates {
        if choice.cells.iter().any(|&cell| used[cell]) {
            continue;
        }
        for &cell in &choice.cells {
            used[cell] = true;
        }
        choices.push(choice);
        if choices.len() >= MULTITILE_CHOICE_LIMIT {
            break;
        }
    }
    eprintln!(
        "multitile_choices horizontal_pairs={} long_direct_pairs={:?} raw={} disjoint={} elapsed_ms={}",
        horizontal_pairs,
        direct_pair_stats,
        raw,
        choices.len(),
        started.elapsed().as_millis()
    );
    choices
}

fn resolve_multitile_choices(
    board: &Board,
    orientation: &mut Vec<u8>,
    choices: &[MultiTileChoice],
) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
    let initial = stats;
    let mut tested = 0usize;
    let mut accepted = 0usize;
    let mut accepted_pairs = Vec::new();
    for choice in choices {
        let current = [
            orientation[choice.cells[0]],
            orientation[choice.cells[1]],
            orientation[choice.cells[2]],
        ];
        let mut best: Option<(Stats, [u8; 3])> = None;
        for variant in choice.variants {
            if variant == current {
                continue;
            }
            tested += 1;
            for (i, &cell) in choice.cells.iter().enumerate() {
                orientation[cell] = variant[i];
            }
            let next = board.evaluate_with_scratch(orientation, &mut scratch);
            if next.score > stats.score
                && next.matched >= stats.matched
                && board.tester_safe(orientation)
                && best
                    .as_ref()
                    .map_or(true, |x| next.quality() > x.0.quality())
            {
                best = Some((next, variant));
            }
            for (i, &cell) in choice.cells.iter().enumerate() {
                orientation[cell] = current[i];
            }
        }
        if let Some((next, variant)) = best {
            for (i, &cell) in choice.cells.iter().enumerate() {
                orientation[cell] = variant[i];
            }
            stats = next;
            accepted += 1;
            accepted_pairs.push(choice.target_pair);
        }
    }
    eprintln!(
        "multitile_resolve choices={} tested={} accepted={} accepted_pairs={:?} k={}->{} score_delta={}",
        choices.len(),
        tested,
        accepted,
        accepted_pairs,
        initial.matched,
        stats.matched,
        stats.score - initial.score
    );
}

struct DetachedLoopMerge {
    stats: Stats,
    cell: usize,
    orientation: u8,
    loop_length: usize,
    source_pair_id: usize,
    source_multiplier: i64,
    pair_id: usize,
    target_multiplier: i64,
    predicted_score: i64,
    predicted_candidates: usize,
}

struct DetachedLoopScratch {
    seen_stamp: Vec<u32>,
    seen_pos: Vec<usize>,
    stamp: u32,
    states: Vec<usize>,
}

impl DetachedLoopScratch {
    fn new(ports: usize) -> Self {
        Self {
            seen_stamp: vec![0; ports],
            seen_pos: vec![0; ports],
            stamp: 0,
            states: Vec::with_capacity(401),
        }
    }
}

fn try_merge_detached_loop(
    board: &Board,
    orientation: &mut [u8],
    changed: &[(usize, u8)],
    updates: &[(usize, i64)],
    extra_source: Option<(usize, usize, i64)>,
    proposed: Stats,
    best_score: i64,
    save_min_k: usize,
    save_max_k: usize,
    differential: &DifferentialEval,
    scratch: &mut EvalScratch,
    safety_scratch: &mut SafetyScratch,
    loop_scratch: &mut DetachedLoopScratch,
    cycles_found: &mut usize,
    predicted_total: &mut usize,
) -> Option<DetachedLoopMerge> {
    let ports = board.valid.len() * 6;
    let terminal_base = ports;
    let mut signatures: HashSet<Vec<(usize, usize, usize)>> = HashSet::new();
    let mut cycles: Vec<Vec<(usize, usize, usize)>> = Vec::new();
    for &(changed_cell, _) in changed {
        for enter in 0..6 {
            loop_scratch.stamp = loop_scratch.stamp.wrapping_add(1);
            if loop_scratch.stamp == 0 {
                loop_scratch.seen_stamp.fill(0);
                loop_scratch.stamp = 1;
            }
            let stamp = loop_scratch.stamp;
            loop_scratch.states.clear();
            let start_state = changed_cell * 6 + enter;
            let mut state = start_state;
            let mut terminal = false;
            for _ in 0..=3 * board.valid_count {
                if loop_scratch.seen_stamp[state] == stamp {
                    break;
                }
                loop_scratch.seen_stamp[state] = stamp;
                loop_scratch.seen_pos[state] = loop_scratch.states.len();
                loop_scratch.states.push(state);
                let cell = state / 6;
                let next = board.transition[state * 6 + orientation[cell] as usize] as usize;
                if next >= terminal_base {
                    terminal = true;
                    break;
                }
                state = next;
            }
            let closed = !terminal
                && state == start_state
                && loop_scratch.seen_stamp[start_state] == stamp
                && loop_scratch.seen_pos[start_state] == 0;
            if closed {
                let mut visits = Vec::with_capacity(loop_scratch.states.len());
                for &cycle_state in &loop_scratch.states {
                    let cell = cycle_state / 6;
                    let cycle_enter = cycle_state % 6;
                    let out = paired_dir(orientation[cell], cycle_enter);
                    visits.push((cell, cycle_enter, out));
                }
                let mut signature: Vec<(usize, usize, usize)> = visits
                    .iter()
                    .map(|&(cell, a, b)| (cell, a.min(b), a.max(b)))
                    .collect();
                signature.sort_unstable();
                if signatures.insert(signature) {
                    cycles.push(visits);
                }
            }
        }
    }
    if cycles.is_empty() {
        return None;
    }
    let mut eligible_sources = HashMap::new();
    for &(id, new_value) in updates {
        let old_value = differential.contribution[id];
        let old_length = differential.pair_cells[id].len() as i64;
        if new_value <= 0 || old_length <= 0 {
            continue;
        }
        let multiplier = old_value / old_length;
        let loss = old_value - new_value;
        if multiplier > 1 && loss > 0 && loss % multiplier == 0 {
            eligible_sources
                .entry((loss / multiplier) as usize)
                .or_insert((id, multiplier));
        } else if multiplier == 1 && loss > 0 {
            eligible_sources.entry(loss as usize).or_insert((id, 1));
        }
    }
    if let Some((length, source_id, multiplier)) = extra_source {
        eligible_sources.entry(length).or_insert((source_id, multiplier));
    }
    cycles.retain(|cycle| eligible_sources.contains_key(&cycle.len()));
    if cycles.is_empty() {
        return None;
    }
    *cycles_found += cycles.len();

    let mut loop_cell = vec![false; board.valid.len()];
    for cycle in &cycles {
        for &(cell, _, _) in cycle {
            loop_cell[cell] = true;
        }
    }
    let mut path_visits: Vec<Vec<(usize, usize, usize, i64)>> =
        vec![Vec::new(); board.valid.len()];
    let mut target_mask = 0u128;
    for &cell in &board.valid_cells {
        if loop_cell[cell] {
            target_mask |= differential.cell_masks[cell];
        }
    }
    for &(id, _) in updates {
        let old_value = differential.contribution[id];
        let old_length = differential.pair_cells[id].len() as i64;
        if old_length > 0 && old_value / old_length > 1 {
            target_mask |= 1u128 << id;
        }
    }
    while target_mask != 0 {
        let id = target_mask.trailing_zeros() as usize;
        target_mask &= target_mask - 1;
        let (value, length) = board.trace_pair(orientation, id, scratch, None);
        if value <= 0 || length <= 0 || value / length <= 1 {
            continue;
        }
        let bonuses = value / length - 1;
        let pair = board.pairs[id];
        let (cell, enter) = board.exits[pair[0]];
        let mut state = cell * 6 + enter;
        for _ in 0..=3 * board.valid_count {
            let cell = state / 6;
            let enter = state % 6;
            let out = paired_dir(orientation[cell], enter);
            if loop_cell[cell] {
                path_visits[cell].push((id, enter, out, bonuses));
            }
            let next = board.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                break;
            }
            state = next;
        }
    }

    let mut best: Option<DetachedLoopMerge> = None;
    let mut predicted_candidates = 0usize;
    for cycle in &cycles {
        let loop_length = cycle.len();
        let mut cycle_count = HashMap::new();
        for &(cell, _, _) in cycle {
            *cycle_count.entry(cell).or_insert(0usize) += 1;
        }
        for &(cell, loop_enter, loop_out) in cycle {
            if cycle_count[&cell] != 1 {
                continue;
            }
            for &(pair_id, path_enter, path_out, bonuses) in &path_visits[cell] {
                if path_visits[cell]
                    .iter()
                    .filter(|&&(id, _, _, _)| id == pair_id)
                    .count()
                    != 1
                {
                    continue;
                }
                let used = (1u8 << loop_enter)
                    | (1u8 << loop_out)
                    | (1u8 << path_enter)
                    | (1u8 << path_out);
                if used.count_ones() != 4 {
                    continue;
                }
                let old_o = orientation[cell];
                for new_o in 0..6u8 {
                    if new_o == old_o {
                        continue;
                    }
                    let cross = (paired_dir(new_o, loop_enter) == path_enter
                        && paired_dir(new_o, loop_out) == path_out)
                        || (paired_dir(new_o, loop_enter) == path_out
                            && paired_dir(new_o, loop_out) == path_enter);
                    if !cross {
                        continue;
                    }
                    let predicted_moves = proposed.moves
                        + rotation_cost(board.initial[cell], new_o)
                        - rotation_cost(board.initial[cell], old_o);
                    let predicted_total =
                        proposed.total + loop_length as i64 * (bonuses + 1);
                    let predicted_score = (proposed.matched as i64
                        * (predicted_total - board.M as i64 * predicted_moves as i64))
                        .max(0);
                    if predicted_score <= best_score {
                        continue;
                    }
                    predicted_candidates += 1;
                    orientation[cell] = new_o;
                    let stats = board.evaluate_with_scratch(orientation, scratch);
                    let valid = stats.score > best_score
                        && stats.matched >= save_min_k
                        && stats.matched <= save_max_k
                        && board.tester_safe_with_scratch(orientation, safety_scratch);
                    orientation[cell] = old_o;
                    if valid
                        && best
                            .as_ref()
                            .map_or(true, |candidate| stats.quality() > candidate.stats.quality())
                    {
                        let (source_pair_id, source_multiplier) =
                            eligible_sources[&loop_length];
                        best = Some(DetachedLoopMerge {
                            stats,
                            cell,
                            orientation: new_o,
                            loop_length,
                            source_pair_id,
                            source_multiplier,
                            pair_id,
                            target_multiplier: bonuses + 1,
                            predicted_score,
                            predicted_candidates: 0,
                        });
                    }
                }
            }
        }
    }
    if let Some(candidate) = best.as_mut() {
        candidate.predicted_candidates = predicted_candidates;
        orientation[candidate.cell] = candidate.orientation;
    }
    *predicted_total += predicted_candidates;
    best
}

fn search_rotations(
    board: &Board,
    orientation: &mut Vec<u8>,
    target_fallback: &[u8],
    target_matched: usize,
    construction_archive: &[ConstructionArchiveEntry],
    start: Instant,
    deadline: Instant,
) {
    let cells = &board.valid_cells;
    let mut rng = Rng(0x9e3779b97f4a7c15 ^ board.W as u64 ^ ((board.M as u64) << 32));
    let mut eval_scratch = EvalScratch::new(board.valid.len());
    let mut safety_scratch = SafetyScratch::new(board.valid.len() * 6);
    let mut loop_scratch = DetachedLoopScratch::new(board.valid.len() * 6);
    let mut current = orientation.clone();
    let mut current_stats = board.evaluate_with_scratch(&current, &mut eval_scratch);
    let n = (board.W + 1) / 2;
    let input_bonus_count = board.bonus.iter().filter(|&&value| value).count();
    let estimated_final_score = SA_SCORE_ESTIMATE_SCALE
        * (n as f64).powf(SA_SCORE_ESTIMATE_N_EXP)
        * ((input_bonus_count + 1) as f64).powf(SA_SCORE_ESTIMATE_B_EXP);
    let start_temperature = if USE_SCORE_SCALED_SA_TEMPERATURE {
        estimated_final_score / SA_START_SCORE_DIVISOR
    } else {
        FIXED_SA_START_TEMP
    };
    let end_temperature = if USE_SCORE_SCALED_SA_TEMPERATURE {
        estimated_final_score / SA_END_SCORE_DIVISOR
    } else {
        FIXED_SA_END_TEMP
    };
    let use_differential = board.W >= DIFFERENTIAL_MIN_W;
    let mut differential = DifferentialEval::new(board, &current, &mut eval_scratch);
    // A target is an upper cap only when construction is already within the
    // beam's retained top-k window.  A low-k construction is merely incomplete
    // and must remain free to add connections during rotation search.
    let lock_target = target_matched + TREE_BOARD_K_LEVELS - 1 >= board.pairs.len();
    let candidate_floor = target_matched.saturating_sub((board.pairs.len() + 2) / 3);
    let mut lower_entries: Vec<&ConstructionArchiveEntry> = construction_archive
        .iter()
        .filter(|entry| {
            lock_target
                && entry.stats.matched >= candidate_floor
                && entry.stats.matched < target_matched
                && board.tester_safe(&entry.orientation)
        })
        .collect();
    lower_entries.sort_unstable_by_key(|entry| entry.stats.matched);
    let allowed_floor = if lock_target {
        lower_entries
            .iter()
            .map(|entry| entry.stats.matched)
            .min()
            .unwrap_or(target_matched)
            .saturating_sub(1)
    } else {
        target_matched
    };
    // A connection consumes at least its short route and competes with bonus
    // trunks for the remaining segments.  Use one full-board, all-bonus pass as
    // the marginal resource price of moving away from the construction target.
    let bonus_count = board.bonus.iter().filter(|&&value| value).count() as i64;
    let target_step = (3 * board.valid_count) as i64 * (bonus_count + 1);
    let aux_value_scale = (3
        * board.valid_count
        * (board.bonus.iter().filter(|&&x| x).count() + 1)) as f64;
    let energy = |s: Stats, sq_sum: i64| {
        let q = s.total - board.M as i64 * s.moves as i64;
        let target_gap = if lock_target {
            (if s.matched < allowed_floor {
                allowed_floor - s.matched
            } else if s.matched > target_matched {
                s.matched - target_matched
            } else {
                0
            }) as i64
        } else {
            target_matched.saturating_sub(s.matched) as i64
        };
        let sq_aux = sq_sum as f64 / aux_value_scale;
        (s.score - target_step * target_gap) as f64
            + 0.15 * q as f64
            + SA_CONTRIBUTION_SQ_BONUS * sq_aux
    };
    let mut best = if lock_target {
        target_fallback.to_vec()
    } else {
        current.clone()
    };
    let mut best_stats = board.evaluate_with_scratch(&best, &mut eval_scratch);
    if lock_target {
        for entry in &lower_entries {
            if entry.stats.matched >= allowed_floor && entry.stats.quality() > best_stats.quality()
            {
                best_stats = entry.stats;
                best.clone_from(&entry.orientation);
            }
        }
    }
    let can_save = |matched: usize| {
        if lock_target {
            matched >= allowed_floor && matched <= target_matched
        } else {
            matched >= target_matched
        }
    };
    let span = deadline
        .saturating_duration_since(start)
        .as_secs_f64()
        .max(0.001);
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
    let mut nonbonus_shorten_attempts = 0usize;
    let mut nonbonus_shorten_wrong_selected = 0usize;
    let mut nonbonus_shorten_completed = 0usize;
    let mut nonbonus_shorten_wrong_completed = 0usize;
    let mut nonbonus_shorten_direct_accepts = 0usize;
    let mut nonbonus_shorten_merge_accepts = 0usize;
    let mut nonbonus_shorten_merge_attempts = 0usize;
    let mut nonbonus_shorten_wrong_merge_attempts = 0usize;
    let mut nonbonus_shorten_wrong_accepts = 0usize;
    let mut nonbonus_shorten_protected_rejects = 0usize;
    let mut two_path_trials = 0usize;
    let mut two_path_completed = 0usize;
    let mut two_path_improving = 0usize;
    let mut two_path_accepts = 0usize;
    let mut differential_pairs = 0usize;
    let mut random_attempts = 0usize;
    let mut random_accepts = 0usize;
    let mut random_k_change_accepts = 0usize;
    let mut loop_merge_attempts = 0usize;
    let mut loop_merge_cycles = 0usize;
    let mut loop_merge_predicted = 0usize;
    let mut loop_merge_accepts = 0usize;
    let mut loop_merge_added_length = 0usize;
    let mut next_extend = start + Duration::from_millis(LOCAL_EXTEND_INTERVAL_MS);
    let mut next_repair = start + Duration::from_secs_f64(0.65 * span);
    let mut next_connect = start + Duration::from_secs_f64(0.55 * span);
    let mut next_nonbonus_shorten = start + Duration::from_secs_f64(0.35 * span);
    let two_path_lns_time = start + Duration::from_secs_f64(0.45 * span);
    let mut two_path_lns_done = !ENABLE_TWO_PATH_LNS;
    let triangles = if ENABLE_SA_TRIANGLE && board.valid_count <= 80 {
        collect_triangles(board)
    } else {
        Vec::new()
    };
    let mut next_triangle = start + Duration::from_millis(SMALL_TRIANGLE_INTERVAL_MS);
    let mut triangle_sweeps = 0usize;
    let mut triangle_accepts = 0usize;
    let mut triangle_combined_accepts = 0usize;
    let mut now = Instant::now();
    let mut temperature = start_temperature;
    let temperature_cycles = if board.valid_count >= SINGLE_CYCLE_MIN_CELLS {
        1
    } else {
        SA_CYCLES
    };
    let mut active_cycle = 0usize;
    let mut undo = Vec::with_capacity(4);
    let mut proposed = Vec::with_capacity(4);
    let mut updates = Vec::with_capacity(board.pairs.len());
    let mut route_cells = Vec::with_capacity(3 * board.valid_count);
    let mut local_workspace = LocalExtendWorkspace::new(board, &current);
    loop {
        // Time queries and powf are visible overhead on small boards, where an
        // evaluation itself is very cheap.  A slightly stale temperature is
        // harmless, so update the schedule once per batch instead of per move.
        if iterations & SA_TIME_CHECK_MASK == 0 {
            now = Instant::now();
            if now >= deadline {
                break;
            }
            let frac = (now.duration_since(start).as_secs_f64() / span).min(1.0);
            let scaled = frac * temperature_cycles as f64;
            let cycle = (scaled.floor() as usize).min(temperature_cycles - 1);
            if cycle > active_cycle {
                active_cycle = cycle;
                if cycle == 1 {
                    current.clone_from_slice(target_fallback);
                } else {
                    current.clone_from(&best);
                }
                current_stats = board.evaluate_with_scratch(&current, &mut eval_scratch);
                differential = DifferentialEval::new(board, &current, &mut eval_scratch);
            }
            let cycle_frac = (scaled - cycle as f64).min(1.0);
            temperature =
                start_temperature.powf(1.0 - cycle_frac) * end_temperature.powf(cycle_frac);
        }
        if !two_path_lns_done && now >= two_path_lns_time {
            two_path_lns_done = true;
            let local_deadline =
                (now + Duration::from_millis(TWO_PATH_LNS_BUDGET_MS)).min(deadline);
            let outcome = two_path_lns_candidate(board, &current, local_deadline);
            two_path_trials += outcome.trials;
            two_path_completed += outcome.completed;
            two_path_improving += outcome.improving;
            if let Some(candidate) = outcome.candidate {
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                let diff = (next.score - current_stats.score) as f64;
                if metropolis_accept(&mut rng, diff, temperature) {
                    current = candidate;
                    current_stats = next;
                    differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                    two_path_accepts += 1;
                    if can_save(next.matched)
                        && next.quality() > best_stats.quality()
                        && board.tester_safe_with_scratch(&current, &mut safety_scratch)
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
        if now >= next_nonbonus_shorten {
            next_nonbonus_shorten += Duration::from_millis(NONBONUS_SHORTEN_INTERVAL_MS);
            nonbonus_shorten_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(NONBONUS_SHORTEN_BUDGET_MS)).min(deadline);
            if let Some(shorten) = nonbonus_shorten_candidate(
                    board,
                    &current,
                    &differential,
                    &mut eval_scratch,
                    &mut nonbonus_shorten_wrong_selected,
                    4,
                    &mut rng,
                    local_deadline,
                ) {
                let NonbonusShortenCandidate {
                    pair_id: target_pair_id,
                    source_exit,
                    target_exit,
                    old_length,
                    new_length,
                    work: mut candidate,
                } = shorten;
                nonbonus_shorten_completed += 1;
                nonbonus_shorten_wrong_completed += usize::from(target_pair_id.is_none());
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                let next_differential =
                    DifferentialEval::new(board, &candidate, &mut eval_scratch);
                let preserves_nonbonus = preserves_other_nonbonus_exit_paths(
                    board,
                    &current,
                    &candidate,
                    (source_exit, target_exit),
                    &mut eval_scratch,
                );
                let target_preserved = board.trace_end(&candidate, source_exit) == target_exit;
                if !preserves_nonbonus || !target_preserved {
                    nonbonus_shorten_protected_rejects += 1;
                } else if next.score > best_stats.score
                    && can_save(next.matched)
                    && board.tester_safe_with_scratch(&candidate, &mut safety_scratch)
                {
                    current = candidate;
                    current_stats = next;
                    differential = next_differential;
                    best_stats = next;
                    best.clone_from(&current);
                    nonbonus_shorten_direct_accepts += 1;
                    nonbonus_shorten_wrong_accepts += usize::from(target_pair_id.is_none());
                    eprintln!(
                        "nonbonus_shorten_accept pair={:?} exits={}->{} length={}->{} score={} merged=false",
                        target_pair_id, source_exit, target_exit, old_length, new_length, next.score
                    );
                } else {
                    updates.clear();
                    for id in 0..board.pairs.len() {
                        let value = next_differential.contribution[id];
                        if value != differential.contribution[id] {
                            updates.push((id, value));
                        }
                    }
                    let released_length = (old_length - new_length) as i64;
                    let max_bonus_multiplier = next_differential
                        .contribution
                        .iter()
                        .zip(&next_differential.pair_cells)
                        .filter_map(|(&value, cells)| {
                            (!cells.is_empty() && value > cells.len() as i64)
                                .then_some(value / cells.len() as i64)
                        })
                        .max()
                        .unwrap_or(0);
                    let merge_upper_score = (next.matched as i64
                        * (next.total + released_length * max_bonus_multiplier
                            - board.M as i64 * (next.moves - 3).max(0) as i64))
                        .max(0);
                    if released_length > 0
                        && max_bonus_multiplier > 1
                        && merge_upper_score > best_stats.score
                    {
                        nonbonus_shorten_merge_attempts += 1;
                        nonbonus_shorten_wrong_merge_attempts +=
                            usize::from(target_pair_id.is_none());
                        let changed: Vec<(usize, u8)> = board
                            .valid_cells
                            .iter()
                            .filter_map(|&cell| {
                                (candidate[cell] != current[cell])
                                    .then_some((cell, current[cell]))
                            })
                            .collect();
                        loop_merge_attempts += 1;
                        let save_max_k = if lock_target {
                            target_matched
                        } else {
                            usize::MAX
                        };
                        if let Some(merged) = try_merge_detached_loop(
                            board,
                            &mut candidate,
                            &changed,
                            &updates,
                            target_pair_id
                                .is_none()
                                .then_some((released_length as usize, usize::MAX, 0)),
                            next,
                            best_stats.score,
                            if lock_target { allowed_floor } else { target_matched },
                            save_max_k,
                            &differential,
                            &mut eval_scratch,
                            &mut safety_scratch,
                            &mut loop_scratch,
                            &mut loop_merge_cycles,
                            &mut loop_merge_predicted,
                        ) {
                            let merged_differential =
                                DifferentialEval::new(board, &candidate, &mut eval_scratch);
                            let still_preserves_nonbonus = preserves_other_nonbonus_exit_paths(
                                board,
                                &current,
                                &candidate,
                                (source_exit, target_exit),
                                &mut eval_scratch,
                            );
                            let target_still_preserved =
                                board.trace_end(&candidate, source_exit) == target_exit;
                            if still_preserves_nonbonus && target_still_preserved {
                                current = candidate;
                                current_stats = merged.stats;
                                differential = merged_differential;
                                best_stats = merged.stats;
                                best.clone_from(&current);
                                nonbonus_shorten_merge_accepts += 1;
                                nonbonus_shorten_wrong_accepts +=
                                    usize::from(target_pair_id.is_none());
                                loop_merge_accepts += 1;
                                loop_merge_added_length += merged.loop_length;
                                eprintln!(
                                    "nonbonus_shorten_accept pair={:?} exits={}->{} length={}->{} score={} merged=true loop_length={} target_pair={}",
                                    target_pair_id,
                                    source_exit,
                                    target_exit,
                                    old_length,
                                    new_length,
                                    merged.stats.score,
                                    merged.loop_length,
                                    merged.pair_id,
                                );
                            } else {
                                nonbonus_shorten_protected_rejects += 1;
                            }
                        }
                    }
                }
            }
            now = Instant::now();
            iterations += 1;
            continue;
        }
        if (board.W + 1) / 2 >= 17 && now >= next_extend {
            next_extend += Duration::from_millis(LOCAL_EXTEND_INTERVAL_MS);
            extend_attempts += 1;
            let local_deadline =
                (now + Duration::from_millis(LOCAL_EXTEND_BUDGET_MS)).min(deadline);
            if let Some((next, candidate)) = local_extend_candidate(
                board,
                &current,
                current_stats,
                &differential,
                &mut rng,
                &mut local_workspace,
                local_deadline,
            )
            {
                let next_differential = DifferentialEval::new(board, &candidate, &mut eval_scratch);
                let diff = energy(next, next_differential.contribution_sq_sum)
                    - energy(current_stats, differential.contribution_sq_sum);
                if metropolis_accept(&mut rng, diff, temperature) {
                    current = candidate;
                    current_stats = next;
                    differential = next_differential;
                    extend_accepts += 1;
                    if can_save(next.matched)
                        && next.quality() > best_stats.quality()
                        && board.tester_safe_with_scratch(&current, &mut safety_scratch)
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
        if !triangles.is_empty() && now >= next_triangle {
            next_triangle += Duration::from_millis(SMALL_TRIANGLE_INTERVAL_MS);
            triangle_sweeps += 1;
            let local_deadline =
                (now + Duration::from_millis(SMALL_TRIANGLE_BUDGET_MS)).min(deadline);
            let (accepted, combined) = reduce_rotations_by_triangles_with(
                board,
                &mut current,
                &triangles,
                local_deadline,
                false,
            );
            if accepted > 0 {
                triangle_accepts += accepted;
                triangle_combined_accepts += combined;
                current_stats = board.evaluate_with_scratch(&current, &mut eval_scratch);
                differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                if can_save(current_stats.matched)
                    && current_stats.quality() > best_stats.quality()
                    && board.tester_safe_with_scratch(&current, &mut safety_scratch)
                {
                    best_stats = current_stats;
                    best.clone_from(&current);
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
                board,
                &current,
                current_stats,
                &differential,
                &mut eval_scratch,
                &mut rng,
                local_deadline,
            ) {
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                if (next.score, next.matched, next.total, Reverse(next.moves))
                    > (
                        current_stats.score,
                        current_stats.matched,
                        current_stats.total,
                        Reverse(current_stats.moves),
                    )
                {
                    current = candidate;
                    current_stats = next;
                    differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                    repair_accepts += 1;
                    if can_save(next.matched)
                        && next.quality() > best_stats.quality()
                        && board.tester_safe_with_scratch(&current, &mut safety_scratch)
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
                board,
                &current,
                current_stats,
                &differential,
                &mut eval_scratch,
                local_deadline,
            );
            connect_trials += outcome.trials;
            connect_completed += outcome.completed;
            let event_meta = (
                outcome.target,
                outcome.area,
                outcome.changed,
                outcome.broken_peak,
            );
            if let Some(candidate) = outcome.candidate {
                let previous = current_stats;
                let next = board.evaluate_with_scratch(&candidate, &mut eval_scratch);
                if next.matched > current_stats.matched && next.score > current_stats.score {
                    current = candidate;
                    current_stats = next;
                    differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                    connect_accepts += 1;
                    connect_events.push((
                        event_meta.0,
                        next.matched as i64 - previous.matched as i64,
                        next.total - previous.total,
                        next.moves - previous.moves,
                        next.score - previous.score,
                        event_meta.1,
                        event_meta.2,
                        event_meta.3,
                    ));
                    if can_save(next.matched)
                        && next.quality() > best_stats.quality()
                        && board.tester_safe_with_scratch(&current, &mut safety_scratch)
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
        if RANDOM_ROTATION_MODE == 1 {
            iterations += 1;
            continue;
        }
        random_attempts += 1;
        let changes = 1 + rng.usize(if cells.len() < 80 { 4 } else { 3 });
        undo.clear();
        proposed.clear();
        let mut affected = 0u128;
        for _ in 0..changes {
            let cell = cells[rng.usize(cells.len())];
            if undo.iter().any(|&(x, _)| x == cell) {
                continue;
            }
            let old = current[cell];
            // On normal/large boards a +/-1 rotation preserves one of the tile's
            // three connections. Tiny boards can exhaust the wider neighborhood,
            // and restricting them caused a large reachability loss.
            let new_o = if board.valid_count <= 80 {
                let mut o = rng.usize(6) as u8;
                if o == old {
                    o = (o + 1) % 6;
                }
                o
            } else if rng.usize(2) == 0 {
                (old + 1) % 6
            } else {
                (old + 5) % 6
            };
            undo.push((cell, old));
            proposed.push(new_o);
            if use_differential {
                affected |= differential.cell_masks[cell];
            }
        }
        for (&(cell, _), &new_o) in undo.iter().zip(proposed.iter()) {
            current[cell] = new_o;
        }
        let next_moves = current_stats.moves
            + undo
                .iter()
                .map(|&(cell, old)| {
                    rotation_cost(board.initial[cell], current[cell])
                        - rotation_cost(board.initial[cell], old)
                })
                .sum::<i32>();
        let (next, next_sq_sum) = if use_differential {
            differential_pairs += affected.count_ones() as usize;
            differential.proposal_with_sq_sum(
                board,
                &current,
                current_stats,
                next_moves,
                affected,
                &mut eval_scratch,
                &mut updates,
            )
        } else {
            (
                board.evaluate_with_moves(&current, next_moves, &mut eval_scratch),
                differential.contribution_sq_sum,
            )
        };
        let diff = energy(next, next_sq_sum)
            - energy(current_stats, differential.contribution_sq_sum);
        let mut recoverable_merge_gain = 0i64;
        if ENABLE_DETACHED_LOOP_MERGE && use_differential && next.score < current_stats.score {
            let mut max_loop_length = 0i64;
            for &(id, new_value) in &updates {
                let old_value = differential.contribution[id];
                let old_length = differential.pair_cells[id].len() as i64;
                if new_value > 0 && old_length > 0 && old_value > new_value {
                    let multiplier = old_value / old_length;
                    let loss = old_value - new_value;
                    if multiplier > 0 && loss % multiplier == 0 {
                        max_loop_length = max_loop_length.max(loss / multiplier);
                    }
                }
            }
            if max_loop_length > 0 {
                let max_bonus_multiplier = differential
                    .contribution
                    .iter()
                    .zip(&differential.pair_cells)
                    .filter_map(|(&value, cells)| {
                        (!cells.is_empty() && value > cells.len() as i64)
                            .then_some(value / cells.len() as i64)
                    })
                    .max()
                    .unwrap_or(0);
                recoverable_merge_gain = max_loop_length * max_bonus_multiplier;
            }
        }
        let merge_upper_score = (next.matched as i64
            * (next.total + recoverable_merge_gain
                - board.M as i64 * (next.moves - 3).max(0) as i64))
            .max(0);
        if recoverable_merge_gain > 0 && merge_upper_score > best_stats.score {
            loop_merge_attempts += 1;
            let save_max_k = if lock_target {
                target_matched
            } else {
                usize::MAX
            };
            if let Some(merged) = try_merge_detached_loop(
                board,
                &mut current,
                &undo,
                &updates,
                None,
                next,
                best_stats.score,
                if lock_target { allowed_floor } else { target_matched },
                save_max_k,
                &differential,
                &mut eval_scratch,
                &mut safety_scratch,
                &mut loop_scratch,
                &mut loop_merge_cycles,
                &mut loop_merge_predicted,
            ) {
                current_stats = merged.stats;
                differential = DifferentialEval::new(board, &current, &mut eval_scratch);
                best_stats = merged.stats;
                best.clone_from(&current);
                loop_merge_accepts += 1;
                loop_merge_added_length += merged.loop_length;
                eprintln!(
                    "loop_merge_accept source_pair={} source_multiplier={} target_pair={} target_multiplier={} cell={} loop_length={} predicted_score={} score={}",
                    merged.source_pair_id,
                    merged.source_multiplier,
                    merged.pair_id,
                    merged.target_multiplier,
                    merged.cell,
                    merged.loop_length,
                    merged.predicted_score,
                    merged.stats.score
                );
                iterations += 1;
                continue;
            }
        }
        let metropolis_accepted = metropolis_accept(&mut rng, diff, temperature);
        let same_k_allowed = RANDOM_ROTATION_MODE != 2 || next.matched == current_stats.matched;
        if same_k_allowed && metropolis_accepted {
            random_accepts += 1;
            random_k_change_accepts += (next.matched != current_stats.matched) as usize;
            current_stats = next;
            if use_differential {
                differential.commit(
                    board,
                    &current,
                    &mut eval_scratch,
                    &updates,
                    &mut route_cells,
                );
                debug_assert_eq!(differential.contribution_sq_sum, next_sq_sum);
            }
            if can_save(next.matched)
                && next.quality() > best_stats.quality()
                && board.tester_safe_with_scratch(&current, &mut safety_scratch)
            {
                best_stats = next;
                best.clone_from(&current);
            }
        } else {
            for &(cell, old) in &undo {
                current[cell] = old;
            }
        }
        iterations += 1;
        if use_differential && iterations & 65535 == 0 {
            let exact = board.evaluate_with_scratch(&current, &mut eval_scratch);
            assert_eq!(
                (
                    current_stats.matched,
                    current_stats.total,
                    current_stats.moves,
                    current_stats.score
                ),
                (exact.matched, exact.total, exact.moves, exact.score)
            );
        }
    }
    orientation.clone_from(&best);
    let mut final_scratch = EvalScratch::new(board.valid.len());
    let mut actual: Vec<(i64, i64, usize)> = (0..board.pairs.len())
        .map(|id| {
            let (value, length) = board.trace_pair(orientation, id, &mut final_scratch, None);
            (length, if length > 0 { value / length - 1 } else { -1 }, id)
        })
        .collect();
    actual.sort_unstable_by_key(|x| Reverse(x.0));
    let bonus_count = board.bonus.iter().filter(|&&x| x).count() as i64;
    let full_bonus_paths = actual
        .iter()
        .filter(|&&(length, bonuses, _)| length > 0 && bonuses == bonus_count)
        .count();
    let total_bonus_uses: i64 = actual
        .iter()
        .filter(|&&(length, _, _)| length > 0)
        .map(|&(_, bonuses, _)| bonuses)
        .sum();
    let mut weighted: Vec<(i64, i64, i64, usize)> = actual
        .iter()
        .filter(|&&(length, _, _)| length > 0)
        .map(|&(length, bonuses, id)| (length * (bonuses + 1), length, bonuses, id))
        .collect();
    weighted.sort_unstable_by_key(|x| Reverse(x.0));
    let bonus_multiplier = (board.bonus.iter().filter(|&&x| x).count() + 1) as i64;
    let hero_rotation_budget = if board.M > 0 {
        actual[0].0.max(0) * bonus_multiplier / board.M as i64
    } else {
        i64::MAX
    };
    let final_cycles = board.alternating_cycles(orientation);
    eprintln!("rotation_search iterations={} random_mode={} random_accepts={}/{} random_k_change_accepts={} loop_merges={}/{}/{} cycles={} added_length={} temp={}->{} reheats={} target_k={} extends={}/{} repairs={}/{} connects={}/{} triangles={}/{} triangle_combined={} final_cycles={}/{} diff_avg={:.2} bonuses={} full_bonus_paths={} total_bonus_uses={} rotation_budget={}/{} longest3={:?} weighted3={:?} best_score={}",
        iterations,
        RANDOM_ROTATION_MODE,
        random_accepts,
        random_attempts,
        random_k_change_accepts,
        loop_merge_accepts,
        loop_merge_predicted,
        loop_merge_attempts,
        loop_merge_cycles,
        loop_merge_added_length,
        start_temperature,
        end_temperature,
        temperature_cycles - 1,
        target_matched,
        extend_accepts, extend_attempts, repair_accepts, repair_attempts,
        connect_accepts, connect_attempts,
        triangle_accepts, triangle_sweeps,
        triangle_combined_accepts,
        final_cycles, board.pairs.len(),
        differential_pairs as f64 / iterations.max(1) as f64,
        board.bonus.iter().filter(|&&x| x).count(),
        full_bonus_paths, total_bonus_uses, best_stats.moves, hero_rotation_budget,
        &actual[..3],
        &weighted[..weighted.len().min(3)],
        best_stats.score);
    eprintln!(
        "connect_repair trials={} completed={} accepted={} events={:?}",
        connect_trials, connect_completed, connect_accepts, connect_events
    );
    eprintln!(
        "nonbonus_shorten attempts={} wrong_selected={} completed={} wrong_completed={} direct={} merged={}/{} wrong_accepts={} wrong_merge_attempts={} protected_rejects={}",
        nonbonus_shorten_attempts,
        nonbonus_shorten_wrong_selected,
        nonbonus_shorten_completed,
        nonbonus_shorten_wrong_completed,
        nonbonus_shorten_direct_accepts,
        nonbonus_shorten_merge_accepts,
        nonbonus_shorten_merge_attempts,
        nonbonus_shorten_wrong_accepts,
        nonbonus_shorten_wrong_merge_attempts,
        nonbonus_shorten_protected_rejects,
    );
    eprintln!(
        "two_path_lns trials={} completed={} improving={} accepted={}",
        two_path_trials, two_path_completed, two_path_improving, two_path_accepts
    );
}

fn region_signature(board: &Board, cells: &[usize], local: &[u8]) -> Vec<u8> {
    let mut boundary = Vec::with_capacity(12);
    for i in 0..cells.len() {
        for side in 0..6 {
            let inside = board
                .next(cells[i], side)
                .is_some_and(|(next, _)| cells.contains(&next));
            if !inside {
                boundary.push((i, side));
            }
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
            result = boundary
                .iter()
                .position(|&(i, side)| i == cell && side == out)
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
        .filter(|&cell| board.valid[cell])
        .map(|cell| vec![cell])
        .collect();
    for size in 1..=max_size {
        if size >= 2 {
            all.extend(level.iter().cloned());
        }
        if size == max_size {
            break;
        }
        let mut next_level = Vec::new();
        for cells in &level {
            for &cell in cells {
                for side in 0..6 {
                    let Some((next, _)) = board.next(cell, side) else {
                        continue;
                    };
                    if cells.contains(&next) {
                        continue;
                    }
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
        for o in &mut local {
            *o = (x % 6) as u8;
            x /= 6;
        }
        groups
            .entry(region_signature(board, cells, &local))
            .or_default()
            .push(code as u16);
    }
    let mut table = vec![Vec::new(); count];
    for group in groups.into_values() {
        for &code in &group {
            table[code as usize] = group.clone();
        }
    }
    table
}

fn transition_descriptor(
    board: &Board,
    cells: &[usize],
    local: &[u8],
) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let mut boundary = Vec::new();
    for i in 0..cells.len() {
        for side in 0..6 {
            if !board
                .next(cells[i], side)
                .is_some_and(|(next, _)| cells.contains(&next))
            {
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
            if board.bonus[cells[cell]] {
                bonus_mask |= 1 << cell;
            }
            let out = paired_dir(local[cell], enter);
            if let Some((next, next_enter)) = board.next(cells[cell], out) {
                if let Some(next_local) = cells.iter().position(|&x| x == next) {
                    cell = next_local;
                    enter = next_enter;
                    continue;
                }
            }
            pairing.push(
                boundary
                    .iter()
                    .position(|&(i, side)| i == cell && side == out)
                    .unwrap() as u8,
            );
            lengths.push(length);
            bonuses.push(bonus_mask);
            break;
        }
    }
    (pairing, lengths, bonuses)
}

fn improve_by_transition_tables(
    board: &Board,
    orientation: &mut Vec<u8>,
    deadline: Instant,
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
        if Instant::now() >= deadline {
            break;
        }
        visited += 1;
        // Exhaustive enumeration shows that an adjacent two-cell region has no
        // non-trivial orientation with the same boundary transition.
        if cells.len() == 2 {
            continue;
        }
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
        if group.len() <= 1 {
            continue;
        }
        nontrivial_hits += 1;
        raw_alternatives += group.len() - 1;
        let mut options = Vec::new();
        for &raw in group {
            let mut code = raw as usize;
            let mut local = vec![0u8; cells.len()];
            for o in &mut local {
                *o = (code % 6) as u8;
                code /= 6;
            }
            let moves: i32 = cells
                .iter()
                .enumerate()
                .map(|(i, &cell)| rotation_cost(board.initial[cell], local[i]))
                .sum();
            let (_, lengths, bonuses) = transition_descriptor(board, cells, &local);
            options.push((raw, moves, lengths, bonuses, local));
        }
        let mut pareto = Vec::new();
        let mut current_is_dominated = false;
        for i in 0..options.len() {
            let dominated = (0..options.len()).any(|j| {
                i != j
                    && options[j].1 <= options[i].1
                    && options[j].2.iter().zip(&options[i].2).all(|(a, b)| a >= b)
                    && options[j]
                        .3
                        .iter()
                        .zip(&options[i].3)
                        .all(|(a, b)| a | b == *a)
                    && (options[j].1 < options[i].1
                        || options[j].2 != options[i].2
                        || options[j].3 != options[i].3)
            });
            if options[i].0 as usize == current_code && dominated {
                current_is_dominated = true;
            }
            if !dominated {
                pareto.push(i);
            }
        }
        if current_is_dominated {
            current_dominated += 1;
        }
        pareto_alternatives += pareto
            .iter()
            .filter(|&&i| options[i].0 as usize != current_code)
            .count();
        let mut affected = 0u128;
        let mut old_local_moves = 0i32;
        for &cell in cells {
            affected |= differential.cell_masks[cell];
            old_local_moves += rotation_cost(board.initial[cell], orientation[cell]);
        }
        let mut best: Option<(Stats, Vec<u8>, Vec<(usize, i64)>)> = None;
        for i in pareto {
            if options[i].0 as usize == current_code {
                continue;
            }
            tested += 1;
            tested_by_size[cells.len()] += 1;
            for (at, &cell) in cells.iter().enumerate() {
                orientation[cell] = options[i].4[at];
            }
            let moves = stats.moves - old_local_moves + options[i].1;
            let candidate = differential.proposal(
                board,
                orientation,
                stats,
                moves,
                affected,
                &mut scratch,
                &mut updates,
            );
            if candidate.matched == stats.matched && candidate.score > stats.score {
                positive_candidates += 1;
            }
            if candidate.matched == stats.matched
                && candidate.score > stats.score
                && best.as_ref().map_or(true, |x| candidate.score > x.0.score)
            {
                best = Some((candidate, options[i].4.clone(), updates.clone()));
            }
            for (at, &cell) in cells.iter().enumerate() {
                orientation[cell] = current[at];
            }
            if Instant::now() >= deadline {
                break;
            }
        }
        if let Some((next, local, best_updates)) = best {
            improving_regions += 1;
            let dm = next.moves as i64 - stats.moves as i64;
            let dt = next.total - stats.total;
            let ds = next.score - stats.score;
            delta_moves_by_size[cells.len()] += dm;
            delta_total_by_size[cells.len()] += dt;
            delta_score_by_size[cells.len()] += ds;
            if dt == 0 && dm < 0 {
                accepted_kind[0] += 1;
            } else if dt > 0 {
                accepted_kind[1] += 1;
            } else {
                accepted_kind[2] += 1;
            }
            for (at, &cell) in cells.iter().enumerate() {
                orientation[cell] = local[at];
            }
            differential.commit(
                board,
                orientation,
                &mut scratch,
                &best_updates,
                &mut route_cells,
            );
            stats = next;
            accepted += 1;
            accepted_by_size[cells.len()] += 1;
        }
    }
    let verified = board.evaluate_with_scratch(orientation, &mut scratch);
    assert!(
        verified.matched == stats.matched
            && verified.total == stats.total
            && verified.moves == stats.moves
            && verified.score == stats.score
    );
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

fn collect_matched_tile_visits(
    board: &Board,
    orientation: &[u8],
    differential: &DifferentialEval,
) -> (Vec<usize>, Vec<Vec<(usize, usize)>>) {
    const NO_OWNER: usize = usize::MAX;
    const MULTIPLE_OWNERS: usize = usize::MAX - 1;
    let mut owner = vec![NO_OWNER; board.valid.len()];
    let mut visits = vec![Vec::new(); board.valid.len()];
    let terminal_base = board.valid.len() * 6;
    for id in 0..board.pairs.len() {
        if differential.contribution[id] <= 0 {
            continue;
        }
        let pair = board.pairs[id];
        let (cell, enter) = board.exits[pair[0]];
        let mut state = cell * 6 + enter;
        for _ in 0..=3 * board.valid_count {
            let cell = state / 6;
            let enter = state % 6;
            let out = paired_dir(orientation[cell], enter);
            if owner[cell] == NO_OWNER {
                owner[cell] = id;
            } else if owner[cell] != id {
                owner[cell] = MULTIPLE_OWNERS;
            }
            visits[cell].push((enter, out));
            let next = board.transition[state * 6 + orientation[cell] as usize] as usize;
            if next >= terminal_base {
                break;
            }
            state = next;
        }
    }
    (owner, visits)
}

fn preserves_ordered_tile_path(visits: &[(usize, usize)], orientation: u8) -> bool {
    if visits.len() < 2 || visits.len() > 3 {
        return false;
    }
    let mut used = 0u8;
    for &(enter, out) in visits {
        let bits = (1u8 << enter) | (1u8 << out);
        if enter == out || used & bits != 0 {
            return false;
        }
        used |= bits;
    }
    // A candidate may reorder the path's visits, but it may not leak into an
    // unused segment of this tile.
    for side in 0..6 {
        if used >> side & 1 != 0 && used >> paired_dir(orientation, side) & 1 == 0 {
            return false;
        }
    }
    // With ordered visits (a,b), (c,d), (e,f), the outside links are b--c
    // and d--e, while a and f are the terminals.  Since an orientation is
    // already a perfect matching, the union is one path iff it contains none
    // of the shortcut edges a--f, b--c, d--e.  Any such edge would close the
    // complementary ports into a detached loop.
    if paired_dir(orientation, visits[0].0) == visits[visits.len() - 1].1 {
        return false;
    }
    for i in 0..visits.len() - 1 {
        if paired_dir(orientation, visits[i].1) == visits[i + 1].0 {
            return false;
        }
    }
    true
}

fn reduce_rotations_by_single_pair_cells(
    board: &Board,
    orientation: &mut Vec<u8>,
    deadline: Instant,
    log: bool,
) -> usize {
    let started = Instant::now();
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut safety_scratch = SafetyScratch::new(board.valid.len() * 6);
    let mut differential = DifferentialEval::new(board, orientation, &mut scratch);
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
    let initial_moves = stats.moves;
    let initial_total = stats.total;
    let initial_score = stats.score;
    let mut accepted = 0usize;
    let mut accepted_180 = 0usize;
    let mut tested = 0usize;
    let mut local_2opt_tested = 0usize;
    let mut local_2opt_accepted = 0usize;
    let mut updates = Vec::new();
    let mut route_cells = Vec::new();
    loop {
        let (tile_owner, tile_visits) =
            collect_matched_tile_visits(board, orientation, &differential);
        let mut changed = false;
        for &cell in &board.valid_cells {
            if Instant::now() >= deadline {
                if log {
                    eprintln!(
                        "single_pair_post tested={} local_2opt_tested={} accepted={} local_2opt_accepted={} accepted_180={} rotations_saved={} total_delta={} score_delta={} elapsed_ms={}",
                        tested,
                        local_2opt_tested,
                        accepted,
                        local_2opt_accepted,
                        accepted_180,
                        initial_moves - stats.moves,
                        stats.total - initial_total,
                        stats.score - initial_score,
                        started.elapsed().as_millis()
                    );
                }
                return accepted;
            }
            let affected = differential.cell_masks[cell];
            if affected.count_ones() != 1 {
                continue;
            }
            let id = affected.trailing_zeros() as usize;
            if differential.contribution[id] <= 0 {
                continue;
            }
            let old = orientation[cell];
            let old_cost = rotation_cost(board.initial[cell], old);
            if old_cost == 0 {
                continue;
            }
            let mut best: Option<(Stats, u8, Vec<(usize, i64)>, bool)> = None;
            for candidate_orientation in 0..6u8 {
                let candidate_cost = rotation_cost(board.initial[cell], candidate_orientation);
                if candidate_orientation == old || candidate_cost >= old_cost {
                    continue;
                }
                tested += 1;
                orientation[cell] = candidate_orientation;
                let local_2opt = tile_owner[cell] == id
                    && preserves_ordered_tile_path(&tile_visits[cell], candidate_orientation);
                let candidate = if local_2opt {
                    local_2opt_tested += 1;
                    Stats {
                        matched: stats.matched,
                        total: stats.total,
                        moves: stats.moves - old_cost + candidate_cost,
                        score: (stats.matched as i64
                            * (stats.total
                                - board.M as i64
                                    * (stats.moves - old_cost + candidate_cost) as i64))
                            .max(0),
                    }
                } else if tile_visits[cell].len() < 2 {
                    differential.proposal(
                        board,
                        orientation,
                        stats,
                        stats.moves - old_cost + candidate_cost,
                        affected,
                        &mut scratch,
                        &mut updates,
                    )
                } else {
                    orientation[cell] = old;
                    continue;
                };
                if candidate.matched == stats.matched
                    && candidate.total == stats.total
                    && best.as_ref().map_or(true, |current| {
                        (Reverse(candidate.moves), candidate.score)
                            > (Reverse(current.0.moves), current.0.score)
                    })
                    && board.tester_safe_after_cell_change(
                        orientation,
                        cell,
                        &mut safety_scratch,
                    )
                {
                    best = Some((
                        candidate,
                        candidate_orientation,
                        if local_2opt { Vec::new() } else { updates.clone() },
                        local_2opt,
                    ));
                }
                orientation[cell] = old;
            }
            if let Some((next, next_orientation, best_updates, local_2opt)) = best {
                orientation[cell] = next_orientation;
                if local_2opt {
                    local_2opt_accepted += 1;
                } else {
                    differential.commit(
                        board,
                        orientation,
                        &mut scratch,
                        &best_updates,
                        &mut route_cells,
                    );
                }
                stats = next;
                accepted += 1;
                accepted_180 += ((next_orientation as i32 - old as i32).rem_euclid(6) == 3) as usize;
                changed = true;
                // A 2-opt changes the visit order of this pair at other cells.
                // Rebuild all ordered tile memos before considering another move.
                break;
            }
        }
        if !changed {
            break;
        }
    }
    let verified = board.evaluate_with_scratch(orientation, &mut scratch);
    assert_eq!(
        (verified.matched, verified.total, verified.moves, verified.score),
        (stats.matched, stats.total, stats.moves, stats.score)
    );
    if log {
        eprintln!(
            "single_pair_post tested={} local_2opt_tested={} accepted={} local_2opt_accepted={} accepted_180={} rotations_saved={} total_delta={} score_delta={} elapsed_ms={}",
            tested,
            local_2opt_tested,
            accepted,
            local_2opt_accepted,
            accepted_180,
            initial_moves - stats.moves,
            stats.total - initial_total,
            stats.score - initial_score,
            started.elapsed().as_millis()
        );
    }
    accepted
}

fn collect_triangles(board: &Board) -> Vec<[usize; 3]> {
    let mut triangles = Vec::new();
    for a in 0..board.valid.len() {
        if !board.valid[a] {
            continue;
        }
        for side in 0..6 {
            let Some((b, _)) = board.next(a, side) else {
                continue;
            };
            let Some((c, _)) = board.next(a, (side + 1) % 6) else {
                continue;
            };
            if !(0..6).any(|d| board.next(b, d).is_some_and(|x| x.0 == c)) {
                continue;
            }
            let mut triangle = [a, b, c];
            triangle.sort_unstable();
            triangles.push(triangle);
        }
    }
    triangles.sort_unstable();
    triangles.dedup();
    triangles
}

fn reduce_rotations_by_triangles_with(
    board: &Board,
    orientation: &mut Vec<u8>,
    triangles: &[[usize; 3]],
    deadline: Instant,
    log: bool,
) -> (usize, usize) {
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
    let initial_moves = stats.moves;
    let initial_total = stats.total;
    let initial_score = stats.score;
    let mut accepted = 0usize;
    let mut combined_accepted = 0usize;
    loop {
        let mut changed = false;
        for cells in triangles {
            if Instant::now() >= deadline {
                if log {
                    eprintln!(
                        "triangle_post accepted={} combined_accepted={} rotations_saved={} total_delta={} score_delta={}",
                        accepted,
                        combined_accepted,
                        initial_moves - stats.moves,
                        stats.total - initial_total,
                        stats.score - initial_score
                    );
                }
                return (accepted, combined_accepted);
            }
            let current = [
                orientation[cells[0]],
                orientation[cells[1]],
                orientation[cells[2]],
            ];
            let signature = region_signature(board, cells, &current);
            let old_local_moves: i32 = cells
                .iter()
                .map(|&cell| rotation_cost(board.initial[cell], orientation[cell]))
                .sum();
            let mut best: Option<(Stats, Vec<u8>, bool)> = None;
            for code in 0..216usize {
                let local = [(code % 6) as u8, (code / 6 % 6) as u8, (code / 36) as u8];
                if local == current {
                    continue;
                }
                let local_moves: i32 = (0..3)
                    .map(|i| rotation_cost(board.initial[cells[i]], local[i]))
                    .sum();
                if (log && local_moves >= old_local_moves)
                    || region_signature(board, cells, &local) != signature
                {
                    continue;
                }
                for i in 0..3 {
                    orientation[cells[i]] = local[i];
                }
                let mut candidate_board = orientation.clone();
                let mut candidate = board.evaluate_with_scratch(&candidate_board, &mut scratch);
                let mut combined = false;
                if !log && local_moves >= old_local_moves && Instant::now() < deadline {
                    let followup = reduce_rotations_by_single_pair_cells(
                        board,
                        &mut candidate_board,
                        deadline,
                        false,
                    );
                    if followup > 0 {
                        // At least one triangle cell must remain changed; do not
                        // credit an unrelated single-tile cleanup to a triangle
                        // transformation that was completely undone.
                        combined = cells
                            .iter()
                            .enumerate()
                            .any(|(i, &cell)| candidate_board[cell] != current[i]);
                        candidate =
                            board.evaluate_with_scratch(&candidate_board, &mut scratch);
                    }
                }
                if candidate.matched == stats.matched
                    && candidate.score > stats.score
                    && candidate.moves < stats.moves
                    && (local_moves < old_local_moves || combined)
                    && best.as_ref().map_or(true, |x| {
                        (candidate.score, candidate.total, Reverse(candidate.moves))
                            > (x.0.score, x.0.total, Reverse(x.0.moves))
                    })
                {
                    best = Some((candidate, candidate_board, combined));
                }
                for i in 0..3 {
                    orientation[cells[i]] = current[i];
                }
            }
            if let Some((next, candidate_board, combined)) = best {
                orientation.clone_from(&candidate_board);
                stats = next;
                accepted += 1;
                combined_accepted += combined as usize;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    if log {
        eprintln!(
            "triangle_post accepted={} combined_accepted={} rotations_saved={} total_delta={} score_delta={}",
            accepted,
            combined_accepted,
            initial_moves - stats.moves,
            stats.total - initial_total,
            stats.score - initial_score
        );
    }
    (accepted, combined_accepted)
}

fn reduce_rotations_by_triangles(
    board: &Board,
    orientation: &mut Vec<u8>,
    deadline: Instant,
) -> usize {
    let triangles = collect_triangles(board);
    reduce_rotations_by_triangles_with(board, orientation, &triangles, deadline, true).0
}

fn collect_rhombi(board: &Board) -> Vec<[usize; 4]> {
    let mut rhombi = Vec::new();
    for a in 0..board.valid.len() {
        if !board.valid[a] {
            continue;
        }
        for side in 0..6 {
            let Some((b, _)) = board.next(a, side) else {
                continue;
            };
            let Some((c, _)) = board.next(a, (side + 1) % 6) else {
                continue;
            };
            let Some((d, _)) = board.next(b, (side + 1) % 6) else {
                continue;
            };
            if !board.next(c, side).is_some_and(|x| x.0 == d) {
                continue;
            }
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
        groups
            .entry(region_signature(board, cells, &local))
            .or_default()
            .push(code as u16);
    }
    let mut table = vec![Vec::new(); 1296];
    for group in groups.into_values() {
        for &code in &group {
            table[code as usize] = group.clone();
        }
    }
    table
}

fn reduce_rotations_by_rhombi(
    board: &Board,
    orientation: &mut Vec<u8>,
    deadline: Instant,
) -> usize {
    let rhombi = collect_rhombi(board);

    let mut tables: HashMap<Vec<i8>, Vec<Vec<u16>>> = HashMap::new();
    let mut scratch = EvalScratch::new(board.valid.len());
    let mut stats = board.evaluate_with_scratch(orientation, &mut scratch);
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
            let current = [
                orientation[cells[0]],
                orientation[cells[1]],
                orientation[cells[2]],
                orientation[cells[3]],
            ];
            let current_code = current[0] as usize
                + 6 * current[1] as usize
                + 36 * current[2] as usize
                + 216 * current[3] as usize;
            let old_local_moves: i32 = cells
                .iter()
                .map(|&cell| rotation_cost(board.initial[cell], orientation[cell]))
                .sum();
            let mut best: Option<(Stats, [u8; 4])> = None;
            for &code in &tables[&geometry][current_code] {
                let code = code as usize;
                let local = [
                    (code % 6) as u8,
                    (code / 6 % 6) as u8,
                    (code / 36 % 6) as u8,
                    (code / 216) as u8,
                ];
                let local_moves: i32 = (0..4)
                    .map(|i| rotation_cost(board.initial[cells[i]], local[i]))
                    .sum();
                if local_moves >= old_local_moves {
                    continue;
                }
                for i in 0..4 {
                    orientation[cells[i]] = local[i];
                }
                let candidate = board.evaluate_with_scratch(orientation, &mut scratch);
                if candidate.matched == stats.matched
                    && candidate.score > stats.score
                    && best.as_ref().map_or(true, |x| {
                        (candidate.score, candidate.total, Reverse(candidate.moves))
                            > (x.0.score, x.0.total, Reverse(x.0.moves))
                    })
                {
                    best = Some((candidate, local));
                }
                for i in 0..4 {
                    orientation[cells[i]] = current[i];
                }
            }
            if let Some((next, local)) = best {
                for i in 0..4 {
                    orientation[cells[i]] = local[i];
                }
                stats = next;
                accepted += 1;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    eprintln!(
        "rhombus_post accepted={} rotations_saved={} total_delta={} score_delta={} tables={}",
        accepted,
        initial_moves - stats.moves,
        stats.total - initial_total,
        stats.score - initial_score,
        tables.len()
    );
    accepted
}

fn improve_by_boundary_signatures(board: &Board, orientation: &mut Vec<u8>, deadline: Instant) {
    let table_deadline = (Instant::now() + Duration::from_millis(100)).min(deadline);
    let table_accepted = improve_by_transition_tables(board, orientation, table_deadline);
    let single_pair_accepted =
        reduce_rotations_by_single_pair_cells(board, orientation, deadline, true);
    let mut rounds = 0usize;
    let mut triangle_accepted = 0usize;
    let mut rhombus_accepted = 0usize;
    while Instant::now() < deadline {
        rounds += 1;
        let triangles = if ENABLE_FINAL_TRIANGLE {
            reduce_rotations_by_triangles(board, orientation, deadline)
        } else {
            0
        };
        triangle_accepted += triangles;
        if Instant::now() >= deadline {
            break;
        }
        let rhombi = if ENABLE_FINAL_RHOMBUS {
            reduce_rotations_by_rhombi(board, orientation, deadline)
        } else {
            0
        };
        rhombus_accepted += rhombi;
        if triangles == 0 && rhombi == 0 {
            break;
        }
    }
    eprintln!(
        "signature_post rounds={} table_accepted={} single_pair_accepted={} triangle_accepted={} rhombus_accepted={}",
        rounds,
        table_accepted,
        single_pair_accepted,
        triangle_accepted,
        rhombus_accepted
    );
}

fn build_exits(N: usize, valid: &[bool]) -> (Vec<(usize, usize)>, Vec<i32>) {
    let W = 2 * N - 1;
    let inside = |r: isize, c: isize| {
        r >= 0 && c >= 0 && r < W as isize && c < W as isize && valid[r as usize * W + c as usize]
    };
    let mut exits = Vec::new();
    let mut push = |r: usize, c: usize, d: usize| {
        debug_assert!(!inside(r as isize + DR[d], c as isize + DC[d]));
        exits.push((r * W + c, d));
    };
    for c in N - 1..W {
        if c == N - 1 {
            push(0, c, 5);
        }
        push(0, c, 0);
        push(0, c, 1);
        if c == W - 1 {
            push(0, c, 2);
        }
    }
    for r in 1..N - 1 {
        push(r, W - 1, 1);
        push(r, W - 1, 2);
    }
    push(N - 1, W - 1, 1);
    push(N - 1, W - 1, 2);
    push(N - 1, W - 1, 3);
    for r in N..W - 1 {
        let c = W + N - 2 - r;
        push(r, c, 2);
        push(r, c, 3);
    }
    for c in (0..N).rev() {
        if c == N - 1 {
            push(W - 1, c, 2);
        }
        push(W - 1, c, 3);
        push(W - 1, c, 4);
        if c == 0 {
            push(W - 1, c, 5);
        }
    }
    for r in (N..W - 1).rev() {
        push(r, 0, 4);
        push(r, 0, 5);
    }
    push(N - 1, 0, 4);
    push(N - 1, 0, 5);
    push(N - 1, 0, 0);
    for r in (1..N - 1).rev() {
        let c = N - 1 - r;
        push(r, c, 5);
        push(r, c, 0);
    }
    let mut id = vec![-1; valid.len() * 6];
    for (i, &(cell, d)) in exits.iter().enumerate() {
        id[cell * 6 + d] = i as i32;
    }
    (exits, id)
}

fn second_construction_beam(board: &Board, base_orientation: &[u8], deadline: Instant) -> Vec<u8> {
    let started = Instant::now();
    let mut scratch = EvalScratch::new(board.valid.len());
    let differential = DifferentialEval::new(board, base_orientation, &mut scratch);
    let initial = board.evaluate_with_scratch(base_orientation, &mut scratch);

    let mut unmatched: Vec<usize> = (0..board.pairs.len())
        .filter(|&id| differential.contribution[id] == 0)
        .collect();
    unmatched.sort_unstable_by_key(|&id| ordinary_pair_priority(board, board.pairs[id]));
    unmatched.truncate(SECOND_CONSTRUCTION_UNMATCHED);

    let mut long_pairs: Vec<(usize, usize, usize)> = Vec::new();
    for id in 0..board.pairs.len() {
        if differential.contribution[id] == 0 {
            continue;
        }
        let (_, length) = board.trace_pair(base_orientation, id, &mut scratch, None);
        long_pairs.push((length as usize, pair_distance(board, board.pairs[id]), id));
    }
    long_pairs.sort_unstable_by_key(|&(length, distance, id)| {
        (
            Reverse(length.saturating_sub(distance)),
            Reverse(length),
            id,
        )
    });
    long_pairs.truncate(SECOND_CONSTRUCTION_LONG_PAIRS);

    let assign_count = unmatched.len().min(long_pairs.len());
    unmatched.truncate(assign_count);
    if assign_count == 0 || Instant::now() >= deadline {
        eprintln!(
            "second_construct virtual_pairs=0 unmatched={} long={} accepted=false elapsed_ms={}",
            unmatched.len(),
            long_pairs.len(),
            started.elapsed().as_millis()
        );
        return base_orientation.to_vec();
    }

    // Assign each unmatched pair to a long pair by the shortest virtual wrong
    // connection: min((u0-l0)+(u1-l1), (u0-l1)+(u1-l0)).
    let long_count = long_pairs.len();
    let mut dp: Vec<Option<(usize, Vec<(usize, usize, bool, usize)>)>> =
        vec![None; 1usize << long_count];
    dp[0] = Some((0, Vec::new()));
    for &unmatched_id in &unmatched {
        let mut next: Vec<Option<(usize, Vec<(usize, usize, bool, usize)>)>> =
            vec![None; 1usize << long_count];
        for mask in 0..(1usize << long_count) {
            let Some((base_cost, assignment)) = dp[mask].as_ref() else {
                continue;
            };
            for long_index in 0..long_count {
                if mask >> long_index & 1 != 0 {
                    continue;
                }
                let long_id = long_pairs[long_index].2;
                let u = board.pairs[unmatched_id];
                let l = board.pairs[long_id];
                let straight =
                    pair_distance(board, [u[0], l[0]]) + pair_distance(board, [u[1], l[1]]);
                let crossed =
                    pair_distance(board, [u[0], l[1]]) + pair_distance(board, [u[1], l[0]]);
                let (wrong_cost, flip) = if crossed < straight {
                    (crossed, true)
                } else {
                    (straight, false)
                };
                let new_mask = mask | (1usize << long_index);
                let new_cost = base_cost + wrong_cost;
                if next[new_mask]
                    .as_ref()
                    .is_none_or(|entry| new_cost < entry.0)
                {
                    let mut new_assignment = assignment.clone();
                    new_assignment.push((unmatched_id, long_id, flip, wrong_cost));
                    next[new_mask] = Some((new_cost, new_assignment));
                }
            }
        }
        dp = next;
    }
    let Some((virtual_cost, assignment)) = dp.into_iter().flatten().min_by_key(|x| x.0) else {
        return base_orientation.to_vec();
    };

    let mut selected_mask = 0u128;
    let mut order = Vec::with_capacity(assignment.len() * 2);
    for &(unmatched_id, _, _, _) in &assignment {
        selected_mask |= 1u128 << unmatched_id;
        order.push(unmatched_id);
    }
    for &(_, long_id, _, _) in &assignment {
        selected_mask |= 1u128 << long_id;
        order.push(long_id);
    }

    let mut protected_domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        protected_domains[cell] = ALL_ORIENTATIONS;
    }
    // Keep all non-selected matched paths as strand domains. Their other two
    // strands remain available to the second construction.
    for id in 0..board.pairs.len() {
        if differential.contribution[id] <= 0 || selected_mask >> id & 1 != 0 {
            continue;
        }
        let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(base_orientation[cell], enter);
            let mut required = 0u8;
            for o in 0..6u8 {
                if paired_dir(o, enter) == out {
                    required |= 1 << o;
                }
            }
            protected_domains[cell] &= required;
            if protected_domains[cell] == 0 {
                return base_orientation.to_vec();
            }
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }

    #[derive(Clone)]
    struct SecondBeamState {
        orientation: Vec<u8>,
        domains: Vec<u8>,
        routed: usize,
        route_length: usize,
        stats: Stats,
    }
    let mut beam = vec![SecondBeamState {
        orientation: base_orientation.to_vec(),
        domains: protected_domains,
        routed: 0,
        route_length: 0,
        stats: initial,
    }];
    let mut reverse_scratch = ReverseBfsScratch::new(board.valid.len() * 6);
    for &id in &order {
        if Instant::now() >= deadline {
            break;
        }
        let mut next_beam =
            Vec::with_capacity(beam.len() * (SECOND_CONSTRUCTION_ROUTE_CANDIDATES + 1));
        for state in beam.into_iter() {
            next_beam.push(state.clone());
            if Instant::now() >= deadline {
                continue;
            }
            let pair = board.pairs[id];
            let routes = find_routes_with_reverse_scratch(
                board,
                &state.orientation,
                &state.domains,
                pair[0],
                pair[1],
                OUTER_LAYERS,
                false,
                None,
                None,
                deadline,
                SECOND_CONSTRUCTION_ROUTE_CANDIDATES,
                &mut reverse_scratch,
            );
            if routes.is_empty() {
                continue;
            }
            let shortest = routes.iter().map(|route| route.length).min().unwrap();
            for route in routes.into_iter().filter(|route| route.length == shortest) {
                let mut candidate = state.clone();
                apply_route(
                    &mut candidate.orientation,
                    &mut candidate.domains,
                    &route,
                    true,
                );
                candidate.routed += 1;
                candidate.route_length += route.length;
                candidate.stats = board.evaluate_with_scratch(&candidate.orientation, &mut scratch);
                next_beam.push(candidate);
            }
        }
        next_beam.sort_unstable_by_key(|state| {
            Reverse((
                state.stats.score,
                state.stats.matched,
                state.routed,
                Reverse(state.route_length),
                Reverse(state.stats.moves),
            ))
        });
        next_beam.truncate(SECOND_CONSTRUCTION_BEAM_WIDTH);
        beam = next_beam;
    }

    let best = beam
        .into_iter()
        .max_by_key(|state| state.stats.quality())
        .expect("empty second construction beam");
    let accepted = best.stats.matched > initial.matched
        && best.stats.score > initial.score
        && board.tester_safe(&best.orientation);
    eprintln!(
        "second_construct virtual_pairs={} virtual_cost={} assignment={:?} routed={} k={}->{} score_delta={} accepted={} elapsed_ms={}",
        assignment.len(), virtual_cost, assignment, best.routed,
        initial.matched, best.stats.matched, best.stats.score - initial.score,
        accepted, started.elapsed().as_millis()
    );
    if accepted {
        best.orientation
    } else {
        base_orientation.to_vec()
    }
}

#[allow(dead_code)]
fn targeted_second_construction_beam(
    board: &Board,
    base_orientation: &[u8],
    plan: &ConnectionTargetPlan,
    deadline: Instant,
) -> Vec<u8> {
    let started = Instant::now();
    if plan.wrong_pairs.is_empty() || Instant::now() >= deadline {
        eprintln!(
            "target_second_beam target_k={} drop={} wrong=0 accepted=false elapsed_ms={}",
            plan.matched,
            plan.dropped_ids.len(),
            started.elapsed().as_millis()
        );
        return base_orientation.to_vec();
    }
    let mut scratch = EvalScratch::new(board.valid.len());
    let differential = DifferentialEval::new(board, base_orientation, &mut scratch);
    let initial = board.evaluate_with_scratch(base_orientation, &mut scratch);
    let selected_mask = plan
        .dropped_ids
        .iter()
        .fold(0u128, |mask, &id| mask | (1u128 << id));
    let mut protected_domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        protected_domains[cell] = ALL_ORIENTATIONS;
    }
    for id in 0..board.pairs.len() {
        if differential.contribution[id] <= 0 || selected_mask >> id & 1 != 0 {
            continue;
        }
        let (mut cell, mut enter) = board.exits[board.pairs[id][0]];
        for _ in 0..=3 * board.valid_count {
            let out = paired_dir(base_orientation[cell], enter);
            let mut required = 0u8;
            for o in 0..6u8 {
                if paired_dir(o, enter) == out {
                    required |= 1 << o;
                }
            }
            protected_domains[cell] &= required;
            if protected_domains[cell] == 0 {
                return base_orientation.to_vec();
            }
            let Some((next, next_enter)) = board.next(cell, out) else {
                break;
            };
            cell = next;
            enter = next_enter;
        }
    }

    #[derive(Clone)]
    struct TargetSecondState {
        orientation: Vec<u8>,
        domains: Vec<u8>,
        routed: usize,
        route_length: usize,
        stats: Stats,
    }
    let mut virtual_pairs = plan.wrong_pairs.clone();
    virtual_pairs.sort_unstable_by(|a, b| {
        expected_route_length_between_exits(board, a[0], a[1])
            .total_cmp(&expected_route_length_between_exits(board, b[0], b[1]))
    });
    let mut beam = vec![TargetSecondState {
        orientation: base_orientation.to_vec(),
        domains: protected_domains,
        routed: 0,
        route_length: 0,
        stats: initial,
    }];
    let mut reverse_scratch = ReverseBfsScratch::new(board.valid.len() * 6);
    for pair in &virtual_pairs {
        if Instant::now() >= deadline {
            break;
        }
        let mut next_beam =
            Vec::with_capacity(beam.len() * (SECOND_CONSTRUCTION_ROUTE_CANDIDATES + 1));
        for state in beam.into_iter() {
            next_beam.push(state.clone());
            if Instant::now() >= deadline {
                continue;
            }
            let routes = find_routes_with_reverse_scratch(
                board,
                &state.orientation,
                &state.domains,
                pair[0],
                pair[1],
                board.W,
                false,
                None,
                None,
                deadline,
                SECOND_CONSTRUCTION_ROUTE_CANDIDATES,
                &mut reverse_scratch,
            );
            if routes.is_empty() {
                continue;
            }
            let shortest = routes.iter().map(|route| route.length).min().unwrap();
            for route in routes.into_iter().filter(|route| route.length == shortest) {
                let mut candidate = state.clone();
                apply_route(
                    &mut candidate.orientation,
                    &mut candidate.domains,
                    &route,
                    true,
                );
                candidate.routed += 1;
                candidate.route_length += route.length;
                candidate.stats =
                    board.evaluate_with_scratch(&candidate.orientation, &mut scratch);
                next_beam.push(candidate);
            }
        }
        next_beam.sort_unstable_by(|a, b| {
            b.routed
                .cmp(&a.routed)
                .then_with(|| {
                    a.stats
                        .matched
                        .abs_diff(plan.matched)
                        .cmp(&b.stats.matched.abs_diff(plan.matched))
                })
                .then_with(|| b.stats.quality().cmp(&a.stats.quality()))
                .then_with(|| a.route_length.cmp(&b.route_length))
        });
        next_beam.truncate(SECOND_CONSTRUCTION_BEAM_WIDTH);
        beam = next_beam;
    }
    let required = virtual_pairs.len();
    let best = beam
        .into_iter()
        .filter(|state| state.routed == required)
        .min_by_key(|state| {
            (
                state.stats.matched.abs_diff(plan.matched),
                Reverse(state.stats.quality()),
                state.route_length,
            )
        });
    let Some(best) = best else {
        eprintln!(
            "target_second_beam target_k={} drop={} wrong={} offset={} completed=false accepted=false elapsed_ms={}",
            plan.matched,
            plan.dropped_ids.len(),
            required,
            plan.offset,
            started.elapsed().as_millis()
        );
        return base_orientation.to_vec();
    };
    let routed_stats = best.stats;
    let mut rebuilt = best.orientation;
    if Instant::now() < deadline {
        let rebuild_start = Instant::now();
        multi_trunk_lns(board, &mut rebuilt, rebuild_start, deadline);
    }
    let rebuilt_stats = board.evaluate_with_scratch(&rebuilt, &mut scratch);
    let accepted = rebuilt_stats.score > initial.score && board.tester_safe(&rebuilt);
    eprintln!(
        "target_second_beam target_k={} drop={} wrong={} offset={} routed={} length={} k={}->{}->{} t={}->{}->{} m={}->{}->{} score_delta={} accepted={} elapsed_ms={}",
        plan.matched,
        plan.dropped_ids.len(),
        required,
        plan.offset,
        best.routed,
        best.route_length,
        initial.matched,
        routed_stats.matched,
        rebuilt_stats.matched,
        initial.total,
        routed_stats.total,
        rebuilt_stats.total,
        initial.moves,
        routed_stats.moves,
        rebuilt_stats.moves,
        rebuilt_stats.score - initial.score,
        accepted,
        started.elapsed().as_millis()
    );
    if board.tester_safe(&rebuilt) {
        rebuilt
    } else {
        base_orientation.to_vec()
    }
}

fn fresh_targeted_second_construction_beam(
    board: &Board,
    base_orientation: &[u8],
    plan: &ConnectionTargetPlan,
    deadline: Instant,
) -> Option<Vec<u8>> {
    let started = Instant::now();
    let initial = board.evaluate(base_orientation);
    let dropped_mask = plan
        .dropped_ids
        .iter()
        .fold(0u128, |mask, &id| mask | (1u128 << id));
    let mut connections: Vec<[usize; 2]> = (0..board.pairs.len())
        .filter(|&id| dropped_mask >> id & 1 == 0)
        .map(|id| board.pairs[id])
        .collect();
    connections.extend_from_slice(&plan.rewired_pairs);
    connections.sort_unstable_by(|a, b| {
        expected_route_length_between_exits(board, a[0], a[1])
            .total_cmp(&expected_route_length_between_exits(board, b[0], b[1]))
            .then_with(|| a.cmp(b))
    });

    #[derive(Clone)]
    struct FreshSecondState {
        orientation: Vec<u8>,
        domains: Vec<u8>,
        routed: usize,
        route_length: usize,
        rotation_lower_bound: i32,
        stats: Stats,
    }
    let mut domains = vec![0u8; board.valid.len()];
    for &cell in &board.valid_cells {
        domains[cell] = ALL_ORIENTATIONS;
    }
    let mut scratch = EvalScratch::new(board.valid.len());
    let initial_board_stats = board.evaluate_with_scratch(&board.initial, &mut scratch);
    let mut beam = vec![FreshSecondState {
        orientation: board.initial.clone(),
        domains,
        routed: 0,
        route_length: 0,
        rotation_lower_bound: 0,
        stats: initial_board_stats,
    }];
    let mut reverse_scratch = ReverseBfsScratch::new(board.valid.len() * 6);
    let mut processed = 0usize;
    let routing_deadline = deadline
        .checked_sub(Duration::from_millis(SECOND_FRESH_DOMAIN_RESOLVE_MS))
        .unwrap_or(deadline);
    for pair in &connections {
        if Instant::now() >= routing_deadline {
            break;
        }
        processed += 1;
        struct FreshSecondExpansion {
            parent: usize,
            route: Option<Route>,
            routed: usize,
            route_length: usize,
            rotation_lower_bound: i32,
        }
        let parents = beam;
        let mut expansions =
            Vec::with_capacity(parents.len() * (SECOND_CONSTRUCTION_ROUTE_CANDIDATES + 1));
        for (parent, state) in parents.iter().enumerate() {
            expansions.push(FreshSecondExpansion {
                parent,
                route: None,
                routed: state.routed,
                route_length: state.route_length,
                rotation_lower_bound: state.rotation_lower_bound,
            });
            if Instant::now() >= routing_deadline {
                continue;
            }
            let routes = find_routes_with_reverse_scratch(
                board,
                &state.orientation,
                &state.domains,
                pair[0],
                pair[1],
                board.W,
                false,
                None,
                None,
                routing_deadline,
                SECOND_CONSTRUCTION_ROUTE_CANDIDATES,
                &mut reverse_scratch,
            );
            if routes.is_empty() {
                continue;
            }
            let shortest = routes.iter().map(|route| route.length).min().unwrap();
            for route in routes.into_iter().filter(|route| route.length == shortest) {
                let mut rotation_delta = 0i32;
                for &(cell, _, required_domain) in &route.tiles {
                    let old_domain = state.domains[cell];
                    let new_domain = old_domain & required_domain;
                    debug_assert_ne!(new_domain, 0);
                    rotation_delta += board.domain_rotation[cell][new_domain as usize]
                        - board.domain_rotation[cell][old_domain as usize];
                }
                expansions.push(FreshSecondExpansion {
                    parent,
                    routed: state.routed + 1,
                    route_length: state.route_length + route.length,
                    rotation_lower_bound: state.rotation_lower_bound + rotation_delta,
                    route: Some(route),
                });
            }
        }
        // Rank cheap metadata first.  Only the states that survive the beam cut
        // clone/materialize a board and receive an exact all-pair evaluation.
        expansions.sort_unstable_by(|a, b| {
            b.routed
                .cmp(&a.routed)
                .then_with(|| a.rotation_lower_bound.cmp(&b.rotation_lower_bound))
                .then_with(|| a.route_length.cmp(&b.route_length))
                .then_with(|| a.parent.cmp(&b.parent))
        });
        expansions.truncate(SECOND_CONSTRUCTION_BEAM_WIDTH);
        let mut next_beam = Vec::with_capacity(expansions.len());
        for expansion in expansions {
            let mut candidate = parents[expansion.parent].clone();
            if let Some(route) = expansion.route {
                apply_route(
                    &mut candidate.orientation,
                    &mut candidate.domains,
                    &route,
                    true,
                );
                candidate.routed = expansion.routed;
                candidate.route_length = expansion.route_length;
                candidate.rotation_lower_bound = expansion.rotation_lower_bound;
                candidate.stats =
                    board.evaluate_with_scratch(&candidate.orientation, &mut scratch);
            }
            next_beam.push(candidate);
        }
        next_beam.sort_unstable_by(|a, b| {
            b.routed
                .cmp(&a.routed)
                .then_with(|| a.rotation_lower_bound.cmp(&b.rotation_lower_bound))
                .then_with(|| a.route_length.cmp(&b.route_length))
                .then_with(|| b.stats.matched.cmp(&a.stats.matched))
                .then_with(|| b.stats.score.cmp(&a.stats.score))
        });
        beam = next_beam;
    }
    let Some(best) = beam.into_iter().min_by_key(|state| {
        (
            Reverse(state.routed),
            state.stats.matched.abs_diff(plan.matched),
            state.rotation_lower_bound,
            state.route_length,
            Reverse(state.stats.score),
        )
    }) else {
        return None;
    };
    let routed_stats = best.stats;
    let mut rebuilt = best.orientation;
    let domains_safe = processed == connections.len()
        && materialize_domains_safely(board, &mut rebuilt, &best.domains);
    let routed_near_incomplete = routed_stats.matched < plan.matched
        && routed_stats.matched >= plan.matched.saturating_sub(2);
    if !domains_safe && routed_near_incomplete && Instant::now() < deadline {
        multi_trunk_lns(board, &mut rebuilt, Instant::now(), deadline);
    }
    let rebuilt_stats = board.evaluate_with_scratch(&rebuilt, &mut scratch);
    let safe = board.tester_safe(&rebuilt);
    eprintln!(
        "fresh_target_second target_k={} drop={} rewired={} wrong={} processed={}/{} routed={} length={} rotation_lb={} k={}->{}->{} t={}->{}->{} m={}->{}->{} score_delta={} safe={} elapsed_ms={}",
        plan.matched,
        plan.dropped_ids.len(),
        plan.rewired_pairs.len(),
        plan.wrong_pairs.len(),
        processed,
        connections.len(),
        best.routed,
        best.route_length,
        best.rotation_lower_bound,
        initial.matched,
        routed_stats.matched,
        rebuilt_stats.matched,
        initial.total,
        routed_stats.total,
        rebuilt_stats.total,
        initial.moves,
        routed_stats.moves,
        rebuilt_stats.moves,
        rebuilt_stats.score - initial.score,
        safe,
        started.elapsed().as_millis()
    );
    if safe
        && processed == connections.len()
        && rebuilt_stats.matched >= plan.matched.saturating_sub(2)
    {
        Some(rebuilt)
    } else {
        None
    }
}

fn construct_initial(
    board: &Board,
    phase_start: Instant,
    construction_deadline: Instant,
    label: &str,
) -> (
    Vec<u8>,
    Vec<ConstructionArchiveEntry>,
    ConnectionTargetPlan,
    Option<Vec<u8>>,
) {
    let initial_stats = board.evaluate(&board.initial);
    let first_deadline = construction_deadline;
    let mut best_orientation = board.initial.clone();
    let mut best_stats = initial_stats;
    let mut archive = Vec::new();
    let mut second_sa_start = None;
    store_construction_archive(&mut archive, initial_stats, &board.initial);
    let specials = special_order(board);
    for count in 1..=LAYERED_MAX_SPECIAL.min(specials.len()) {
        if Instant::now() >= first_deadline {
            break;
        }
        let reserved = &specials[..count];
        let outer_deadline = (Instant::now() + Duration::from_millis(LAYERED_OUTER_LIMIT_MS))
            .min(first_deadline);
        let special_deadline = (outer_deadline + Duration::from_millis(LAYERED_SPECIAL_LIMIT_MS))
            .min(first_deadline);
        let (mut candidate, layers, done, special_t) = build_layered_with_specials(
            board,
            &mut archive,
            reserved,
            count - 1,
            count > 1,
            DIRECT_TWO_EXIT_IN_LAYERED,
            outer_deadline,
            special_deadline,
        );
        polish(
            board,
            &mut candidate,
            (Instant::now() + Duration::from_millis(80)).min(first_deadline),
        );
        let stats = board.evaluate(&candidate);
        store_construction_archive(&mut archive, stats, &candidate);
        eprintln!("construct label={} layered reserved={:?} domains={} layers={:?} special_done={} special_t={} k={} t={} m={} score={}",
            label, reserved, count > 1, layers, done, special_t,
            stats.matched, stats.total, stats.moves, stats.score);
        if stats.score > best_stats.score && board.tester_safe(&candidate) {
            best_stats = stats;
            best_orientation = candidate;
        }
    }
    if ENABLE_EXACT_CSP_CONSTRUCTION
        && best_stats.matched < board.pairs.len()
        && Instant::now() < first_deadline
    {
        let csp_deadline =
            (Instant::now() + Duration::from_millis(EXACT_CSP_CONSTRUCTION_MS)).min(first_deadline);
        if let Some(candidate) =
            exact_csp_repair_matched_paths(board, &best_orientation, csp_deadline)
        {
            let stats = board.evaluate(&candidate);
            store_construction_archive(&mut archive, stats, &candidate);
            if stats.score > best_stats.score && board.tester_safe(&candidate) {
                best_stats = stats;
                best_orientation = candidate;
            }
        }
    }
    if ENABLE_LEGACY_CONSTRUCTION {
        for &width in &WIDTHS {
            if Instant::now() >= first_deadline {
                break;
            }
            let outer_deadline =
                (Instant::now() + Duration::from_millis(450)).min(first_deadline);
            let use_two_exit_direct = DIRECT_TWO_EXIT_IN_LEGACY;
            let (outer, _) = build_outer(board, width, &[], use_two_exit_direct, outer_deadline);
            let outer_stats = board.evaluate(&outer);
            if outer_stats.score > best_stats.score && board.tester_safe(&outer) {
                best_stats = outer_stats;
                best_orientation = outer;
            }
            for count in 1..=MAX_SPECIAL {
                if Instant::now() >= first_deadline {
                    break;
                }
                let chosen = &specials[..count.min(specials.len())];
                let gate_deadline =
                    (Instant::now() + Duration::from_millis(180)).min(first_deadline);
                let (gated_outer, gated_fixed) =
                    build_outer(board, width, chosen, use_two_exit_direct, gate_deadline);
                let special_deadline =
                    (Instant::now() + Duration::from_millis(260)).min(first_deadline);
                let (mut candidate, special_t, done) = build_with_specials(
                    board,
                    &gated_outer,
                    &gated_fixed,
                    width,
                    chosen,
                    special_deadline,
                );
                polish(
                    board,
                    &mut candidate,
                    (Instant::now() + Duration::from_millis(30)).min(first_deadline),
                );
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
    }
    let connection_plan =
        estimate_connection_target(board, &best_orientation, best_stats.moves, &archive);
    if ENABLE_SECOND_CONSTRUCTION_BEAM
        && board.valid_count >= SECOND_CONSTRUCTION_MIN_CELLS
        && Instant::now() < construction_deadline
    {
        let second = if connection_plan.wrong_pairs.is_empty() {
            Some(second_construction_beam(
                board,
                &best_orientation,
                construction_deadline,
            ))
        } else {
            let second_deadline = (Instant::now()
                + Duration::from_millis(SECOND_FRESH_LIMIT_MS))
            .min(phase_start + Duration::from_millis(5300));
            fresh_targeted_second_construction_beam(
                board,
                &best_orientation,
                &connection_plan,
                second_deadline,
            )
        };
        if let Some(second) = second {
            let stats = board.evaluate(&second);
            store_construction_archive(&mut archive, stats, &second);
            let usable_target_start = !connection_plan.wrong_pairs.is_empty()
                && stats.matched >= connection_plan.matched.saturating_sub(2)
                && board.tester_safe(&second);
            if usable_target_start {
                second_sa_start = Some(second.clone());
            }
            if !usable_target_start
                && stats.score > best_stats.score
                && board.tester_safe(&second)
            {
                best_stats = stats;
                best_orientation = second;
            }
        }
    }
    eprintln!(
        "construct_done label={} k={} t={} m={} score={} elapsed_ms={}",
        label,
        best_stats.matched,
        best_stats.total,
        best_stats.moves,
        best_stats.score,
        phase_start.elapsed().as_millis()
    );
    archive.sort_unstable_by_key(|entry| entry.stats.matched);
    eprintln!(
        "construction_archive entries={} levels={:?}",
        archive.len(),
        archive
            .iter()
            .map(|entry| {
                (
                    entry.stats.matched,
                    entry.stats.total,
                    entry.stats.moves,
                    entry.stats.score,
                )
            })
            .collect::<Vec<_>>()
    );
    (
        best_orientation,
        archive,
        connection_plan,
        second_sa_start,
    )
}

fn search_path_reallocation(board: &Board, orientation: &mut Vec<u8>, deadline: Instant) {
    polish(
        board,
        orientation,
        (Instant::now() + Duration::from_millis(POST_CONSTRUCTION_POLISH_MS)).min(deadline),
    );
    emit_phase_snapshot(board, "02_polish", orientation);

    let portfolio_start = Instant::now();
    let portfolio_deadline =
        (portfolio_start + Duration::from_millis(PATH_REALLOCATION_MS)).min(deadline);
    let before_reallocation = board.evaluate(orientation);
    let use_compact_only = board.valid_count <= 80
        && 5 * board.M as i64 * before_reallocation.moves as i64 > before_reallocation.total;
    eprintln!(
        "reallocation_branch kind={} cells={} penalty_ratio={:.4}",
        if use_compact_only {
            "compact"
        } else {
            "portfolio"
        },
        board.valid_count,
        board.M as f64 * before_reallocation.moves as f64
            / before_reallocation.total.max(1) as f64
    );
    if use_compact_only {
        compact_paths_sa(board, orientation, portfolio_start, portfolio_deadline);
    } else {
        let reallocation_base = orientation.clone();
        let mut lns_candidate = reallocation_base.clone();
        let lns_deadline =
            (portfolio_start + Duration::from_millis(MULTI_TRUNK_LNS_LIMIT_MS))
                .min(portfolio_deadline);
        multi_trunk_lns(board, &mut lns_candidate, portfolio_start, lns_deadline);
        let fallback_start = Instant::now();
        let mut compact_candidate = reallocation_base;
        if fallback_start < portfolio_deadline {
            compact_paths_sa(
                board,
                &mut compact_candidate,
                fallback_start,
                portfolio_deadline,
            );
        }
        let lns_stats = board.evaluate(&lns_candidate);
        let compact_stats = board.evaluate(&compact_candidate);
        let choose_lns =
            lns_stats.quality() > compact_stats.quality() && board.tester_safe(&lns_candidate);
        *orientation = if choose_lns {
            lns_candidate
        } else {
            compact_candidate
        };
        eprintln!(
            "reallocation_select kind={} lns_k={} lns_score={} compact_k={} compact_score={}",
            if choose_lns {
                "multi_trunk_lns"
            } else {
                "compact"
            },
            lns_stats.matched,
            lns_stats.score,
            compact_stats.matched,
            compact_stats.score
        );
    }
    emit_phase_snapshot(board, "03_reallocation", orientation);

    let low_bonus_start = Instant::now();
    let low_bonus_ms = if board.bonus.iter().filter(|&&x| x).count()
        >= LOW_BONUS_REALLOCATION_HIGH_BONUS_THRESHOLD
    {
        LOW_BONUS_REALLOCATION_HIGH_BONUS_MS
    } else {
        LOW_BONUS_REALLOCATION_MS
    };
    let low_bonus_deadline =
        (low_bonus_start + Duration::from_millis(low_bonus_ms)).min(deadline);
    low_bonus_reallocation(
        board,
        orientation,
        low_bonus_start,
        low_bonus_deadline,
    );
    emit_phase_snapshot(board, "04_low_bonus_reallocation", orientation);
}

fn output_orientation(board: &Board, orientation: &[u8]) {
    let mut moves = Vec::new();
    for cell in 0..orientation.len() {
        if !board.valid[cell] {
            continue;
        }
        let from = board.initial[cell] as i32;
        let to = orientation[cell] as i32;
        let cw = (to - from + 6) % 6;
        let ccw = (from - to + 6) % 6;
        let (count, dir) = if cw <= ccw { (cw, 1) } else { (ccw, -1) };
        for _ in 0..count {
            moves.push((cell / board.W, cell % board.W, dir));
        }
    }
    let mut out = io::BufWriter::new(io::stdout().lock());
    writeln!(out, "{}", moves.len()).unwrap();
    for (r, c, d) in moves {
        writeln!(out, "{} {} {}", r, c, d).unwrap();
    }
}

fn emit_phase_snapshot(board: &Board, phase: &str, orientation: &[u8]) {
    if std::env::var_os("MM166_PHASE_SNAPSHOTS").is_none() {
        return;
    }
    let mut moves = Vec::new();
    for cell in 0..orientation.len() {
        if !board.valid[cell] {
            continue;
        }
        let from = board.initial[cell] as i32;
        let to = orientation[cell] as i32;
        let cw = (to - from + 6) % 6;
        let ccw = (from - to + 6) % 6;
        let (count, dir) = if cw <= ccw { (cw, 1) } else { (ccw, -1) };
        for _ in 0..count {
            moves.push((cell / board.W, cell % board.W, dir));
        }
    }
    let stats = board.evaluate(orientation);
    eprintln!("@@PHASE_BEGIN {} {}", phase, stats.score);
    eprintln!("{}", moves.len());
    for (r, c, d) in moves {
        eprintln!("{} {} {}", r, c, d);
    }
    eprintln!("@@PHASE_END {}", phase);
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
        if x >= 0 {
            valid[cell] = true;
            initial[cell] = x as u8;
        }
    }
    let mut bonus = vec![false; W * W];
    for _ in 0..B {
        let r: usize = sc.next();
        let c: usize = sc.next();
        bonus[r * W + c] = true;
    }
    let (exits, exit_id) = build_exits(N, &valid);
    assert_eq!(exits.len(), 6 * W);
    let mut neighbors = vec![[usize::MAX; 6]; W * W];
    for cell in 0..W * W {
        if !valid[cell] {
            continue;
        }
        let r = cell / W;
        let c = cell % W;
        for side in 0..6 {
            let nr = r as isize + DR[side];
            let nc = c as isize + DC[side];
            if nr >= 0 && nc >= 0 && nr < W as isize && nc < W as isize {
                let next = nr as usize * W + nc as usize;
                if valid[next] {
                    neighbors[cell][side] = next;
                }
            }
        }
    }
    let mut boundary_depth = vec![usize::MAX; W * W];
    let mut q = VecDeque::new();
    for &(cell, _) in &exits {
        if boundary_depth[cell] != 0 {
            boundary_depth[cell] = 0;
            q.push_back(cell);
        }
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
    let mut transition = vec![0u16; valid.len() * 36];
    for cell in 0..valid.len() {
        if !valid[cell] {
            continue;
        }
        for enter in 0..6 {
            let state = cell * 6 + enter;
            for o in 0u8..6 {
                let out = paired_dir(o, enter);
                transition[state * 6 + o as usize] = (if neighbors[cell][out] != usize::MAX {
                    neighbors[cell][out] * 6 + (out + 3) % 6
                } else {
                    terminal_base + exit_id[cell * 6 + out] as usize
                }) as u16;
            }
        }
    }
    let valid_cells: Vec<usize> = (0..valid.len()).filter(|&cell| valid[cell]).collect();
    let mut domain_rotation = vec![[i32::MAX; 64]; valid.len()];
    for &cell in &valid_cells {
        for domain in 1usize..64 {
            domain_rotation[cell][domain] = (0..6u8)
                .filter(|&o| domain >> o & 1 != 0)
                .map(|o| rotation_cost(initial[cell], o))
                .min()
                .unwrap();
        }
    }
    let mut partner = vec![usize::MAX; exits.len()];
    let mut pair_id_by_exit = vec![usize::MAX; exits.len()];
    for (id, pair) in pairs.iter().enumerate() {
        partner[pair[0]] = pair[1];
        partner[pair[1]] = pair[0];
        pair_id_by_exit[pair[0]] = id;
        pair_id_by_exit[pair[1]] = id;
    }
    let board = Board {
        W,
        M,
        initial: initial.clone(),
        valid,
        bonus,
        exits,
        exit_id,
        pairs,
        partner,
        pair_id_by_exit,
        transition,
        neighbors,
        domain_rotation,
        boundary_depth,
        valid_cells,
        valid_count,
    };
    let solve_start = Instant::now();
    let deadline = solve_start + Duration::from_millis(TIME_LIMIT_MS);
    let construction_deadline =
        (solve_start + Duration::from_millis(CONSTRUCTION_LIMIT_MS)).min(deadline);
    let (
        mut best_orientation,
        construction_archive,
        connection_plan,
        second_sa_start,
    ) =
        construct_initial(&board, solve_start, construction_deadline, "main");
    let mut best_stats = board.evaluate(&best_orientation);
    let construction_target_orientation = best_orientation.clone();
    let fallback_target_matched = best_stats.matched;
    let mut construction_target_matched = best_stats.matched;
    let mut has_second_sa_start = false;
    if let Some(second) = second_sa_start {
        has_second_sa_start = second != construction_target_orientation;
        best_orientation = second;
        best_stats = board.evaluate(&best_orientation);
        construction_target_matched = connection_plan.matched;
        eprintln!(
            "target_second_start selected=true target_k={} start_k={} start_t={} start_m={} start_score={} fallback_k={} fallback_score={}",
            construction_target_matched,
            best_stats.matched,
            best_stats.total,
            best_stats.moves,
            best_stats.score,
            board.evaluate(&construction_target_orientation).matched,
            board.evaluate(&construction_target_orientation).score
        );
    }
    emit_phase_snapshot(&board, "01_construction", &best_orientation);
    if !OUTPUT_CONSTRUCTION_ONLY && Instant::now() < deadline {
        search_path_reallocation(&board, &mut best_orientation, deadline);
        let rotation_start = Instant::now();
        if has_second_sa_start {
            let remaining = deadline.saturating_duration_since(rotation_start);
            let second_deadline =
                rotation_start + remaining.mul_f64(SECOND_CONSTRUCTION_SA_FRACTION);
            search_rotations(
                &board,
                &mut best_orientation,
                &construction_target_orientation,
                construction_target_matched,
                &construction_archive,
                rotation_start,
                second_deadline,
            );
            let second_result = best_orientation.clone();
            let second_stats = board.evaluate(&second_result);
            let mut fallback_result = construction_target_orientation.clone();
            search_rotations(
                &board,
                &mut fallback_result,
                &construction_target_orientation,
                fallback_target_matched,
                &construction_archive,
                Instant::now(),
                deadline,
            );
            let fallback_stats = board.evaluate(&fallback_result);
            let choose_second = second_stats.score > fallback_stats.score
                && board.tester_safe(&second_result);
            best_orientation = if choose_second {
                second_result
            } else {
                fallback_result
            };
            eprintln!(
                "target_second_ab choose={} second_k={} second_score={} fallback_k={} fallback_score={}",
                if choose_second { "second" } else { "fallback" },
                second_stats.matched,
                second_stats.score,
                fallback_stats.matched,
                fallback_stats.score
            );
        } else {
            search_rotations(
                &board,
                &mut best_orientation,
                &construction_target_orientation,
                construction_target_matched,
                &construction_archive,
                rotation_start,
                deadline,
            );
        }
        emit_phase_snapshot(&board, "05_rotation_sa", &best_orientation);
        let postprocess_deadline = Instant::now() + Duration::from_millis(POSTPROCESS_LIMIT_MS);
        improve_by_boundary_signatures(&board, &mut best_orientation, postprocess_deadline);
        let choices = build_multitile_choices(&board, &best_orientation);
        resolve_multitile_choices(&board, &mut best_orientation, &choices);
        best_stats = board.evaluate(&best_orientation);
        emit_phase_snapshot(&board, "06_final_postprocess", &best_orientation);
    }
    eprintln!(
        "final k={} t={} m={} score={} elapsed_ms={}",
        best_stats.matched,
        best_stats.total,
        best_stats.moves,
        best_stats.score,
        start.elapsed().as_millis()
    );

    output_orientation(&board, &best_orientation);
}
