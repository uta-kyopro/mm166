import argparse
import json
import time
from collections import deque
from pathlib import Path

import z3

DR = (-1, -1, 0, 1, 1, 0)
DC = (0, 1, 1, 0, -1, -1)
BASE = (1, 0, 4, 5, 2, 3)


def paired(o, enter):
    x = (enter + 6 - o) % 6
    return (BASE[x] + o) % 6


def rot_cost(a, b):
    d = (b - a) % 6
    return min(d, 6 - d)


class Instance:
    def __init__(self, path):
        data = list(map(int, Path(path).read_text().split()))
        at = 0
        self.n, self.m, self.b, self.p = data[:4]
        at = 4
        self.pairs = []
        for _ in range(self.p):
            self.pairs.append((data[at], data[at + 1]))
            at += 2
        self.w = 2 * self.n - 1
        self.initial = data[at:at + self.w * self.w]
        at += self.w * self.w
        self.valid = [x >= 0 for x in self.initial]
        self.bonus = set()
        for _ in range(self.b):
            r, c = data[at], data[at + 1]
            at += 2
            self.bonus.add(r * self.w + c)
        self.exits, self.exit_id = self.build_exits()
        assert len(self.exits) == 6 * self.w

    def inside(self, r, c):
        return 0 <= r < self.w and 0 <= c < self.w and self.valid[r * self.w + c]

    def next(self, cell, side):
        r, c = divmod(cell, self.w)
        nr, nc = r + DR[side], c + DC[side]
        if self.inside(nr, nc):
            return nr * self.w + nc, (side + 3) % 6
        return None

    def build_exits(self):
        e = []
        def push(r, c, d): e.append((r * self.w + c, d))
        n, w = self.n, self.w
        for c in range(n - 1, w):
            if c == n - 1: push(0, c, 5)
            push(0, c, 0); push(0, c, 1)
            if c == w - 1: push(0, c, 2)
        for r in range(1, n - 1): push(r, w - 1, 1); push(r, w - 1, 2)
        push(n - 1, w - 1, 1); push(n - 1, w - 1, 2); push(n - 1, w - 1, 3)
        for r in range(n, w - 1):
            c = w + n - 2 - r; push(r, c, 2); push(r, c, 3)
        for c in range(n - 1, -1, -1):
            if c == n - 1: push(w - 1, c, 2)
            push(w - 1, c, 3); push(w - 1, c, 4)
            if c == 0: push(w - 1, c, 5)
        for r in range(w - 2, n - 1, -1): push(r, 0, 4); push(r, 0, 5)
        push(n - 1, 0, 4); push(n - 1, 0, 5); push(n - 1, 0, 0)
        for r in range(n - 2, 0, -1):
            c = n - 1 - r; push(r, c, 5); push(r, c, 0)
        ids = [-1] * (self.w * self.w * 6)
        for i, (cell, side) in enumerate(e): ids[cell * 6 + side] = i
        return e, ids

    def trace(self, orient, start, cells=False):
        cell, enter = self.exits[start]
        path, seen_bonus = [], set()
        for _ in range(3 * sum(self.valid) + 1):
            path.append(cell)
            if cell in self.bonus: seen_bonus.add(cell)
            out = paired(orient[cell], enter)
            nxt = self.next(cell, out)
            if nxt is None:
                return self.exit_id[cell * 6 + out], len(path), len(seen_bonus), path
            cell, enter = nxt
        return -1, len(path), len(seen_bonus), path

    def evaluate(self, orient):
        k = t = 0
        details = []
        for i, (a, b) in enumerate(self.pairs):
            end, length, bonuses, path = self.trace(orient, a, True)
            if end == b:
                k += 1
                value = length * (bonuses + 1)
                t += value
                details.append((i, length, bonuses, value, path))
        moves = sum(rot_cost(a, b) for a, b, ok in zip(self.initial, orient, self.valid) if ok)
        return k, t, moves, max(0, k * (t - self.m * moves)), details


def load_orientation(inst, path):
    vals = list(map(int, Path(path).read_text().split()))
    moves, at = vals[0], 1
    orient = [max(0, x) for x in inst.initial]
    for _ in range(moves):
        r, c, d = vals[at:at + 3]
        at += 3
        cell = r * inst.w + c
        orient[cell] = (orient[cell] + d) % 6
    return orient


def shortest_corridor(inst, start, goals):
    parent = {start: None}
    q = deque([start])
    goal = None
    while q:
        cell = q.popleft()
        if cell in goals:
            goal = cell
            break
        for side in range(6):
            nxt = inst.next(cell, side)
            if nxt and nxt[0] not in parent:
                parent[nxt[0]] = cell
                q.append(nxt[0])
    path = []
    while goal is not None:
        path.append(goal)
        goal = parent[goal]
    return path


def shortest_between(inst, starts, goals):
    goals = set(goals)
    parent = {cell: None for cell in starts}
    q = deque(starts)
    goal = None
    while q:
        cell = q.popleft()
        if cell in goals:
            goal = cell
            break
        for side in range(6):
            nxt = inst.next(cell, side)
            if nxt and nxt[0] not in parent:
                parent[nxt[0]] = cell
                q.append(nxt[0])
    path = []
    while goal is not None:
        path.append(goal)
        goal = parent[goal]
    return path


def expand(inst, seeds, width):
    dist = {cell: 0 for cell in seeds}
    q = deque(seeds)
    while q:
        cell = q.popleft()
        if dist[cell] == width: continue
        for side in range(6):
            nxt = inst.next(cell, side)
            if nxt and nxt[0] not in dist:
                dist[nxt[0]] = dist[cell] + 1
                q.append(nxt[0])
    return sorted(dist)


def solve_width(inst, base_orient, width, timeout_ms, max_models, max_changes,
                random_seed, mode, max_targets):
    base = inst.evaluate(base_orient)
    matched = {x[0]: x for x in base[4]}
    if mode == 'bonus':
        targets = [x for x in base[4] if inst.b - x[2] == 1]
        targets.sort(key=lambda x: -x[1])
    else:
        matched_ids = set(matched)
        targets = []
        for pid, (a, b) in enumerate(inst.pairs):
            if pid in matched_ids:
                continue
            pa = inst.trace(base_orient, a, True)[3]
            pb = inst.trace(base_orient, b, True)[3]
            corridor = shortest_between(inst, pa, set(pb))
            targets.append((pid, len(corridor), corridor))
        targets.sort(key=lambda x: x[1])
    results = []
    for target in targets[:max_targets]:
        pid = target[0]
        if mode == 'bonus':
            target_path = target[4]
            visited = set(target_path) & inst.bonus
            missing = next(iter(inst.bonus - visited))
            corridor = shortest_corridor(inst, missing, set(target_path))
        else:
            missing = None
            corridor = target[2]
        region = expand(inst, corridor, width)
        rid = {cell: i for i, cell in enumerate(region)}
        port_count = 6 * len(region)
        term_base = port_count

        def collapse(cell, enter):
            cost = 0
            bonus_mask = 0
            seen = set()
            while cell not in rid:
                key = (cell, enter)
                if key in seen: return term_base + len(inst.exits), cost, bonus_mask
                seen.add(key)
                cost += 1
                if cell in inst.bonus:
                    bonus_mask |= 1 << sorted(inst.bonus).index(cell)
                out = paired(base_orient[cell], enter)
                nxt = inst.next(cell, out)
                if nxt is None:
                    return term_base + inst.exit_id[cell * 6 + out], cost, bonus_mask
                cell, enter = nxt
            return 6 * rid[cell] + enter, cost, bonus_mask

        opt = z3.Solver()
        opt.set(timeout=timeout_ms)
        opt.set(random_seed=random_seed)
        ori = [z3.Int(f'o_{pid}_{width}_{i}') for i in range(len(region))]
        for x in ori: opt.add(0 <= x, x < 6)
        changes = [ori[i] != base_orient[cell] for i, cell in enumerate(region)]
        opt.add(z3.Sum([z3.If(x, 1, 0) for x in changes]) <= max_changes)

        # Each region port is a graph vertex. Outside fixed paths collapse to one
        # fixed edge; tile-internal edges are enabled by the orientation variable.
        edges = []
        fixed_seen = set()
        for i, cell in enumerate(region):
            for side in range(6):
                u = 6 * i + side
                nxt = inst.next(cell, side)
                if nxt is None:
                    v = term_base + inst.exit_id[cell * 6 + side]
                    edge_cost, edge_bonus = 0, 0
                elif nxt[0] in rid:
                    v = 6 * rid[nxt[0]] + nxt[1]
                    edge_cost, edge_bonus = 0, 0
                else:
                    v, edge_cost, edge_bonus = collapse(*nxt)
                key = tuple(sorted((u, v)))
                if u != v and key not in fixed_seen:
                    fixed_seen.add(key)
                    edges.append((key[0], key[1], z3.BoolVal(True), None,
                                  edge_cost, edge_bonus))
        for i, cell in enumerate(region):
            possible = {}
            for o in range(6):
                for side in range(6):
                    other = paired(o, side)
                    key = tuple(sorted((side, other)))
                    possible.setdefault(key, []).append(o)
            for (a, b), rotations in possible.items():
                enabled = z3.Or(*[ori[i] == o for o in sorted(set(rotations))])
                mask = 1 << sorted(inst.bonus).index(cell) if cell in inst.bonus else 0
                edges.append((6 * i + a, 6 * i + b, enabled, cell, 1, mask))

        impacted = [mid for mid, detail in matched.items()
                    if set(detail[4]) & set(region)]
        row_base = {'target': pid, 'missing': missing, 'width': width,
                    'mode': mode, 'region_cells': len(region),
                    'corridor_cells': len(corridor),
                    'impacted_pairs': len(impacted)}
        node_count = term_base + len(inst.exits) + 1

        # A path worth more than the receiver is too expensive to shorten merely
        # to gain its last bonus. Preserve every local pairing used by such paths;
        # equivalent orientations may still rearrange their other two segments.
        protected = []
        for mid in impacted:
            if mode != 'bonus' or mid == pid or matched[mid][3] <= matched[pid][3]:
                continue
            protected.append(mid)
            a, b = inst.pairs[mid]
            cell, enter = inst.exits[a]
            for _ in range(3 * sum(inst.valid) + 1):
                leave = paired(base_orient[cell], enter)
                if cell in rid:
                    allowed = [o for o in range(6) if paired(o, enter) == leave]
                    opt.add(z3.Or(*[ori[rid[cell]] == o for o in allowed]))
                nxt = inst.next(cell, leave)
                if nxt is None:
                    break
                cell, enter = nxt
        row_base['protected_pairs'] = protected

        def add_flow(mid):
            a, b = inst.pairs[mid]
            source, sink = term_base + a, term_base + b
            out = [[] for _ in range(node_count)]
            incoming = [[] for _ in range(node_count)]
            for ei, (u, v, enabled, _, _, _) in enumerate(edges):
                uv = z3.Bool(f'f_{pid}_{width}_{mid}_{ei}_0')
                vu = z3.Bool(f'f_{pid}_{width}_{mid}_{ei}_1')
                opt.add(z3.Implies(uv, enabled), z3.Implies(vu, enabled),
                        z3.Not(z3.And(uv, vu)))
                out[u].append(uv); incoming[v].append(uv)
                out[v].append(vu); incoming[u].append(vu)
            for node in range(node_count):
                balance = z3.Sum([z3.If(x, 1, 0) for x in out[node]]) \
                    - z3.Sum([z3.If(x, 1, 0) for x in incoming[node]])
                opt.add(balance == (1 if node == source else -1 if node == sink else 0))

        if mode == 'bonus':
            # Split the receiver flow at one selected segment of the missing bonus.
            # This forbids satisfying the condition with an independent cycle.
            a, b = inst.pairs[pid]
            source, sink = term_base + a, term_base + b
            selectors = []
            for ei, (u, v, enabled, tag, _, _) in enumerate(edges):
                if tag == missing:
                    uv = z3.Bool(f'sel_{pid}_{width}_{ei}_0')
                    vu = z3.Bool(f'sel_{pid}_{width}_{ei}_1')
                    opt.add(z3.Implies(uv, enabled), z3.Implies(vu, enabled),
                            z3.Not(z3.And(uv, vu)))
                    selectors.extend(((uv, u, v), (vu, v, u)))
            opt.add(z3.Sum([z3.If(sel, 1, 0) for sel, _, _ in selectors]) == 1)

            def add_target_half(name, first_half):
                out = [[] for _ in range(node_count)]
                incoming = [[] for _ in range(node_count)]
                for ei, (u, v, enabled, tag, _, _) in enumerate(edges):
                    if tag == missing:
                        continue
                    uv = z3.Bool(f'{name}_{pid}_{width}_{ei}_0')
                    vu = z3.Bool(f'{name}_{pid}_{width}_{ei}_1')
                    opt.add(z3.Implies(uv, enabled), z3.Implies(vu, enabled),
                            z3.Not(z3.And(uv, vu)))
                    out[u].append(uv); incoming[v].append(uv)
                    out[v].append(vu); incoming[u].append(vu)
                for node in range(node_count):
                    arrival = z3.Sum([z3.If(s, 1, 0) for s, u, _ in selectors if u == node])
                    departure = z3.Sum([z3.If(s, 1, 0) for s, _, v in selectors if v == node])
                    balance = z3.Sum([z3.If(x, 1, 0) for x in out[node]]) \
                        - z3.Sum([z3.If(x, 1, 0) for x in incoming[node]])
                    rhs = ((1 if node == source else 0) - arrival if first_half
                           else departure - (1 if node == sink else 0))
                    opt.add(balance == rhs)

            add_target_half('left', True)
            add_target_half('right', False)
        else:
            add_flow(pid)
        for mid in impacted:
            if mid != pid:
                add_flow(mid)
        started = time.monotonic()
        models = 0
        best_score = None
        best_changes = None
        status = z3.unknown
        while models < max_models:
            remaining = timeout_ms - int(1000 * (time.monotonic() - started))
            if remaining <= 0: break
            opt.set(timeout=remaining)
            status = opt.check()
            if status != z3.sat: break
            model = opt.model()
            values = [model.eval(x).as_long() for x in ori]
            candidate = base_orient[:]
            for i, cell in enumerate(region): candidate[cell] = values[i]
            score = inst.evaluate(candidate)
            candidate_matched = {x[0] for x in score[4]}
            target_detail = next((x for x in score[4] if x[0] == pid), None)
            target_ok = target_detail is not None and (
                mode == 'connect' or target_detail[2] == inst.b)
            required_k = base[0] + (1 if mode == 'connect' else 0)
            if target_ok and (best_score is None or score[3] > best_score[3]):
                best_score = score
                best_changes = [(cell, values[i]) for i, cell in enumerate(region)
                                if values[i] != base_orient[cell]]
                if score[0] >= required_k and score[3] > base[3]:
                    models += 1
                    break
            opt.add(z3.Or(*[ori[i] != values[i] for i in range(len(ori))]))
            models += 1
        row = dict(row_base, status=str(status), models=models,
                   max_changes=max_changes)
        if best_score is not None:
            row.update({'k': best_score[0], 't': best_score[1], 'moves': best_score[2],
                        'score': best_score[3], 'delta_k': best_score[0] - base[0],
                        'delta_score': best_score[3] - base[3],
                         'improved': best_score[0] >= required_k and best_score[3] > base[3],
                        'changes': best_changes})
        results.append(row)
    return {'base': {'k': base[0], 't': base[1], 'moves': base[2], 'score': base[3]},
            'width': width, 'results': results}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--input', required=True)
    ap.add_argument('--output', required=True)
    ap.add_argument('--width', type=int, required=True)
    ap.add_argument('--timeout-ms', type=int, default=120000)
    ap.add_argument('--max-models', type=int, default=2000)
    ap.add_argument('--max-changes', type=int, default=12)
    ap.add_argument('--random-seed', type=int, default=0)
    ap.add_argument('--mode', choices=('bonus', 'connect'), default='bonus')
    ap.add_argument('--max-targets', type=int, default=1)
    ap.add_argument('--report', required=True)
    args = ap.parse_args()
    inst = Instance(args.input)
    orient = load_orientation(inst, args.output)
    report = solve_width(inst, orient, args.width, args.timeout_ms,
                         args.max_models, args.max_changes, args.random_seed,
                         args.mode, args.max_targets)
    Path(args.report).write_text(json.dumps(report, indent=2), encoding='utf-8')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
