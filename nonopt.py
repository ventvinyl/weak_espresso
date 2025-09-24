#!/usr/bin/env python3
# coded in utf-8
# by lee hanbyoel (aka. youngyangze, ventvinyl, nttntt1)

import sys
from collections import deque, defaultdict, Counter
from typing import List, Tuple, Dict, Set

class Implicant:
    def __init__(self, mask: int = 0, dc: int = 0, covers: List[int] = None):
        self.mask = mask
        self.dc = dc
        self.covers = covers if covers is not None else []

def popcount(n: int) -> int:
    return n.bit_count()

I = 0
O = 0
rows = 0
and_cnt = 0
or_cnt = 0
not_cnt = 0
xor_cnt = 0

in_edge: List[Tuple[str, str]] = []
out_edge: List[Tuple[str, str]] = []
inputs: List[str] = []
outputs: List[str] = []
not_in: Dict[int, str] = {}
not_wire: Dict[str, str] = {}
literal_and: Dict[str, str] = {}
literal_or: Dict[str, str] = {}
literal_xor: Dict[str, str] = {}

def const_one() -> str:
    return "1"

def const_zero() -> str:
    return "0"

def wnot(i: int) -> str:
    global not_cnt
    if i in not_in:
        return not_in[i]
    not_cnt += 1
    name = f"NOT{not_cnt}"
    not_in[i] = name
    in_edge.append((inputs[i], name))
    return name

def not_wire(src: str) -> str:
    global not_cnt
    if src == "1":
        return "0"
    if src == "0":
        return "1"
    if len(src) == 1 and 'A' <= src <= chr(ord('A') + I - 1):
        return wnot(ord(src) - ord('A'))
    if src in not_wire:
        return not_wire[src]
    not_cnt += 1
    name = f"NOT{not_cnt}"
    not_wire[src] = name
    in_edge.append((src, name))
    return name

def new_and(a: str, b: str) -> str:
    global and_cnt
    and_cnt += 1
    name = f"AND{and_cnt}"
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def new_or(a: str, b: str) -> str:
    global or_cnt
    or_cnt += 1
    name = f"OR{or_cnt}"
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def new_xor(a: str, b: str) -> str:
    global xor_cnt
    xor_cnt += 1
    name = f"XOR{xor_cnt}"
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def and_literal(lits: List[str]) -> str:
    if not lits:
        return const_one()
    lits_sorted = sorted(lits)
    key = "AND:" + ",".join(lits_sorted) + ","
    if key in literal_and:
        return literal_and[key]
    dq = deque(lits_sorted)
    while len(dq) > 1:
        nexts = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_and(a, b)
            nexts.append(g)
        if dq:
            nexts.append(dq.popleft())
        dq = deque(nexts)
    final = dq[0]
    literal_and[key] = final
    return final

def or_literal(terms: List[str]) -> str:
    if not terms:
        return const_zero()
    terms_sorted = sorted(terms)
    key = "OR:" + ",".join(terms_sorted) + ","
    if key in literal_or:
        return literal_or[key]
    dq = deque(terms_sorted)
    while len(dq) > 1:
        nexts = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_or(a, b)
            nexts.append(g)
        if dq:
            nexts.append(dq.popleft())
        dq = deque(nexts)
    final = dq[0]
    literal_or[key] = final
    return final

def xor_literal(terms: List[str]) -> str:
    if not terms:
        return const_zero()
    terms_sorted = sorted(terms)
    key = "XOR:" + ",".join(terms_sorted) + ","
    if key in literal_xor:
        return literal_xor[key]
    dq = deque(terms_sorted)
    while len(dq) > 1:
        nexts = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_xor(a, b)
            nexts.append(g)
        if dq:
            nexts.append(dq.popleft())
        dq = deque(nexts)
    final = dq[0]
    literal_xor[key] = final
    return final

def convert(imp: Implicant) -> List[Tuple[int, int]]:
    ret = []
    for i in range(I):
        wbit = (I - 1 - i)
        if imp.dc & (1 << wbit):
            continue
        v = (imp.mask >> wbit) & 1
        ret.append((i, v))
    return ret

def work_gate(imp: Implicant) -> str:
    lits = convert(imp)
    if not lits:
        return const_one()
    names = []
    for i, v in lits:
        if v == 1:
            names.append(inputs[i])
        else:
            names.append(wnot(i))
    if len(names) == 1:
        return names[0]
    return and_literal(names)

def qm_prime_implicants(minterms: List[int]) -> List[Implicant]:
    cur = []
    for m in minterms:
        imp = Implicant(mask=m, dc=0, covers=[m])
        cur.append(imp)
    primes = []
    while True:
        n = len(cur)
        merged = [False] * n
        nexts: List[Implicant] = []
        groups: Dict[int, List[int]] = defaultdict(list)
        for i, c in enumerate(cur):
            cnt = popcount(c.mask & ~c.dc)
            groups[cnt].append(i)
        keys = list(groups.keys())
        for cnt in keys:
            if (cnt + 1) not in groups:
                continue
            for i in groups[cnt]:
                for j in groups[cnt + 1]:
                    if cur[i].dc != cur[j].dc:
                        continue
                    diff = cur[i].mask ^ cur[j].mask
                    if popcount(diff) != 1:
                        continue
                    nim = Implicant()
                    nim.dc = cur[i].dc | diff
                    nim.mask = cur[i].mask & ~diff
                    nim.covers = cur[i].covers[:] + cur[j].covers[:]
                    nim.covers = sorted(set(nim.covers))
                    nexts.append(nim)
                    merged[i] = merged[j] = True
        for i in range(n):
            if not merged[i]:
                primes.append(cur[i])
        if not nexts:
            break
        unique = []
        seen = set()
        for x in nexts:
            key = (x.mask, x.dc)
            if key not in seen:
                seen.add(key)
                unique.append(x)
        cur = unique
    ret = []
    seen = set()
    for p in primes:
        key = (p.mask, p.dc)
        if key not in seen:
            seen.add(key)
            ret.append(p)
    return ret

def select_primes_for_cover(minterms: List[int], primes: List[Implicant]) -> List[int]:
    m = len(minterms)
    mpos = {minterms[i]: i for i in range(m)}
    p = len(primes)
    covers = [[] for _ in range(p)]
    for i in range(p):
        for j in primes[i].covers:
            if j in mpos:
                covers[i].append(mpos[j])
    counts = [0] * m
    for i in range(p):
        for j in covers[i]:
            counts[j] += 1
    chosen = [0] * p
    covered = [0] * m
    ret = []
    for i in range(m):
        if counts[i] == 1:
            for j in range(p):
                for x in covers[j]:
                    if x == i and not chosen[j]:
                        chosen[j] = 1
                        ret.append(j)
                        for y in covers[j]:
                            if not covered[y]:
                                covered[y] = 1
                        break
    # greedy
    while True:
        best = -1
        bestcov = 0
        for i in range(p):
            if not chosen[i]:
                cnt = sum(1 for x in covers[i] if not covered[x])
                if cnt > bestcov:
                    bestcov = cnt
                    best = i
        if best == -1 or bestcov == 0:
            break
        chosen[best] = 1
        ret.append(best)
        for x in covers[best]:
            covered[x] = 1
    return ret

def check_affine_xor(f: List[int]) -> Tuple[bool, List[int]]:
    nvars = I
    eqs = rows
    vars_num = nvars + 1
    # mx: eqs x (vars_num+1) augmented
    mx = [[0] * (vars_num + 1) for _ in range(eqs)]
    for r in range(eqs):
        for i in range(nvars):
            mx[r][i] = (r >> (nvars - 1 - i)) & 1
        mx[r][nvars] = 1
        mx[r][vars_num] = f[r]
    row = 0
    where = [-1] * (vars_num)
    for col in range(vars_num):
        if row >= eqs:
            break
        sel = -1
        for i in range(row, eqs):
            if mx[i][col]:
                sel = i
                break
        if sel == -1:
            continue
        mx[row], mx[sel] = mx[sel], mx[row]
        where[col] = row
        for i in range(eqs):
            if i != row and mx[i][col]:
                for j in range(col, vars_num + 1):
                    mx[i][j] ^= mx[row][j]
        row += 1
    for i in range(row, eqs):
        if mx[i][vars_num]:
            return False, []
    answer = [0] * (vars_num)
    for i in range(vars_num):
        if where[i] != -1:
            answer[i] = mx[where[i]][vars_num]
    ret = [0] * (nvars + 1)
    for i in range(nvars + 1):
        ret[i] = answer[i]
    return True, ret

def xor_cover(primes: List[Implicant], f: List[int]) -> Tuple[bool, List[int]]:
    r = rows
    p = len(primes)
    if p == 0:
        return False, []
    relevant = [0] * r
    for i in range(p):
        mask = primes[i].mask
        dc = primes[i].dc
        for j in range(r):
            if ((j & ~dc) == mask):
                relevant[j] = 1
    for i in range(r):
        if f[i]:
            relevant[i] = 1
    rowl = [i for i in range(r) if relevant[i]]
    n = len(rowl)
    if n == 0:
        if all(x == 0 for x in f):
            return True, [0] * p
        return False, []
    m = [[0] * (p + 1) for _ in range(n)]
    for i in range(n):
        r_ = rowl[i]
        for j in range(p):
            mask = primes[j].mask
            dc = primes[j].dc
            if ((r_ & ~dc) == mask):
                m[i][j] = 1
        m[i][p] = f[r_] & 1
    row = 0
    where = [-1] * p
    for col in range(p):
        if row >= n:
            break
        sel = -1
        for i in range(row, n):
            if m[i][col]:
                sel = i
                break
        if sel == -1:
            continue
        m[row], m[sel] = m[sel], m[row]
        where[col] = row
        for i in range(n):
            if i != row and m[i][col]:
                for j in range(col, p + 1):
                    m[i][j] ^= m[row][j]
        row += 1
    for i in range(row, n):
        if m[i][p]:
            return False, []
    answer = [0] * p
    for i in range(p):
        if where[i] != -1:
            answer[i] = m[where[i]][p]
    return True, answer

def factoring_create_terms(implics: List[Implicant]) -> List[str]:
    terms: List[Set[str]] = []
    for imp in implics:
        s = set()
        for b in range(I):
            wbit = I - 1 - b
            if imp.dc & (1 << wbit):
                continue
            if (imp.mask >> wbit) & 1:
                s.add(inputs[b])
            else:
                s.add("~" + inputs[b])
        terms.append(s)
    results: List[str] = []
    while terms:
        if len(terms) == 1:
            t = terms[0]
            lits = []
            for lit in t:
                if lit and lit[0] == '~':
                    v = lit[1:]
                    lits.append(wnot(ord(v[0]) - ord('A')))
                else:
                    lits.append(lit)
            if not lits:
                results.append(const_one())
            elif len(lits) == 1:
                results.append(lits[0])
            else:
                results.append(and_literal(lits))
            break
        freq = Counter()
        for t in terms:
            for lit in t:
                freq[lit] += 1
        best_lit = ""
        best = 0
        for lit, cnt in freq.items():
            if cnt > best:
                best = cnt
                best_lit = lit
        if best < 2:
            for t in terms:
                lits = []
                for lit in t:
                    if lit and lit[0] == '~':
                        v = lit[1:]
                        lits.append(wnot(ord(v[0]) - ord('A')))
                    else:
                        lits.append(lit)
                if not lits:
                    results.append(const_one())
                elif len(lits) == 1:
                    results.append(lits[0])
                else:
                    results.append(and_literal(lits))
            break
        with_list = []
        without = []
        for t in terms:
            if best_lit in t:
                with_list.append(t)
            else:
                without.append(t)
        rem_gate = []
        for t in with_list:
            r = set(t)
            r.discard(best_lit)
            lits = []
            for lit in r:
                if lit and lit[0] == '~':
                    v = lit[1:]
                    lits.append(wnot(ord(v[0]) - ord('A')))
                else:
                    lits.append(lit)
            rg = const_one() if not lits else (lits[0] if len(lits) == 1 else and_literal(lits))
            rem_gate.append(rg)
        rem_or = or_literal(rem_gate)
        if best_lit and best_lit[0] == '~':
            v = best_lit[1:]
            wire = wnot(ord(v[0]) - ord('A'))
        else:
            wire = best_lit
        factored = and_literal([wire, rem_or])
        results.append(factored)
        terms = without
    return results

def optimize_netlist():
    gate_inputs: Dict[str, List[str]] = defaultdict(list)
    gate_type: Dict[str, str] = {}
    for src, tgt in in_edge:
        if tgt.startswith("AND"):
            typ = "AND"
        elif tgt.startswith("OR"):
            typ = "OR"
        elif tgt.startswith("XOR"):
            typ = "XOR"
        elif tgt.startswith("NOT"):
            typ = "NOT"
        else:
            typ = "GATE"
        gate_type[tgt] = typ
        gate_inputs[tgt].append(src)
    changed = True
    passes = 0

    def replace_wire(oldw: str, neww: str):
        if oldw == neww:
            return
        for kv in gate_inputs.values():
            for i_, s in enumerate(kv):
                if s == oldw:
                    kv[i_] = neww
        for i_, oe in enumerate(out_edge):
            if oe[0] == oldw:
                out_edge[i_] = (neww, oe[1])
        for i_, ie in enumerate(in_edge):
            if ie[0] == oldw:
                in_edge[i_] = (neww, ie[1])

    while changed and passes < 10:
        changed = False
        passes += 1
        gates = list(gate_inputs.keys())
        for g in gates:
            typ = gate_type.get(g, "")
            ins = gate_inputs[g]
            ins = sorted(set(ins))
            gate_inputs[g] = ins
            if typ == "NOT":
                if not ins:
                    continue
                a = ins[0]
                if a == "1":
                    replace_wire(g, "0")
                    changed = True
                    continue
                if a == "0":
                    replace_wire(g, "1")
                    changed = True
                    continue
                if a.startswith("NOT"):
                    if a in gate_inputs and len(gate_inputs[a]) == 1:
                        replace_wire(g, gate_inputs[a][0])
                        changed = True
                        continue
            elif typ == "AND":
                if "0" in ins:
                    replace_wire(g, "0")
                    changed = True
                    continue
                newins = [s for s in ins if s != "1"]
                if len(newins) != len(ins):
                    gate_inputs[g] = newins
                    ins = newins
                    changed = True
                if not ins:
                    replace_wire(g, "1")
                    changed = True
                    continue
                if len(ins) == 1:
                    replace_wire(g, ins[0])
                    changed = True
                    continue
            elif typ == "OR":
                if "1" in ins:
                    replace_wire(g, "1")
                    changed = True
                    continue
                newins = [s for s in ins if s != "0"]
                if len(newins) != len(ins):
                    gate_inputs[g] = newins
                    ins = newins
                    changed = True
                if not ins:
                    replace_wire(g, "0")
                    changed = True
                    continue
                if len(ins) == 1:
                    replace_wire(g, ins[0])
                    changed = True
                    continue
            elif typ == "XOR":
                if len(ins) == 2:
                    a, b = ins[0], ins[1]
                    if a == b:
                        replace_wire(g, "0")
                        changed = True
                        continue
                    if a == "0":
                        replace_wire(g, b)
                        changed = True
                        continue
                    if b == "0":
                        replace_wire(g, a)
                        changed = True
                        continue
                    if a == "1":
                        nb = not_wire(b)
                        replace_wire(g, nb)
                        changed = True
                        continue
                    if b == "1":
                        na = not_wire(a)
                        replace_wire(g, na)
                        changed = True
                        continue
    reachable = set()
    dq = deque()
    for src, tgt in out_edge:
        if src:
            dq.append(src)
            reachable.add(src)
    while dq:
        w = dq.popleft()
        if w in gate_inputs:
            for s in gate_inputs[w]:
                if s != "0" and s != "1" and s not in reachable:
                    reachable.add(s)
                    dq.append(s)
    newIn: List[Tuple[str, str]] = []
    seen = set()
    for g, ins in gate_inputs.items():
        if g not in reachable:
            continue
        for s in ins:
            key = s + "->" + g
            if key not in seen:
                seen.add(key)
                newIn.append((s, g))
    in_edge.clear()
    in_edge.extend(newIn)
    newOut: List[Tuple[str, str]] = []
    seen.clear()
    for oe in out_edge:
        key = oe[0] + "->" + oe[1]
        if key not in seen:
            seen.add(key)
            newOut.append(oe)
    out_edge.clear()
    out_edge.extend(newOut)

data = sys.stdin.read().strip().split()
if not data:
    exit(0)
it = iter(data)
I = int(next(it))
O = int(next(it))
rows = 1 << I
table = [[0] * (I + O) for _ in range(rows)]
for _ in range(rows):
    tmp = [int(next(it)) for _ in range(I + O)]
    i_ = 0
    for i in range(I):
        if tmp[i]:
            i_ |= (1 << (I - 1 - i))
    for i in range(I + O):
        table[i_][i] = tmp[i]

inputs = [chr(ord('A') + i) for i in range(I)]
outputs = [chr(ord('A') + I + i) for i in range(O)]

for i in range(O):
    f = [0] * rows
    minterms = []
    for r in range(rows):
        f[r] = table[r][I + i]
        if f[r] == 1:
            minterms.append(r)
    lin_ok, coeffs = check_affine_xor(f)
    if lin_ok:
        to_xor = []
        for i2 in range(I):
            if coeffs[i2] == 1:
                to_xor.append(inputs[i2])
        if not to_xor:
            gate = const_one() if coeffs[I] else const_zero()
        elif len(to_xor) == 1:
            gate = to_xor[0]
            if coeffs[I] == 1:
                gate = not_wire(gate)
        else:
            gate = xor_literal(to_xor)
            if coeffs[I] == 1:
                gate = not_wire(gate)
        out_edge.append((gate, outputs[i]))
        continue
    if not minterms:
        out_edge.append((const_zero(), outputs[i]))
        continue
    if len(minterms) == rows:
        out_edge.append((const_one(), outputs[i]))
        continue

    primes = qm_prime_implicants(minterms)
    ok, sel = xor_cover(primes, f)
    if ok:
        terms = []
        for p in range(len(primes)):
            if sel[p]:
                terms.append(work_gate(primes[p]))
        if not terms:
            out_edge.append((const_zero(), outputs[i]))
        else:
            out_edge.append((xor_literal(terms), outputs[i]))
        continue
    chosen = select_primes_for_cover(minterms, primes)
    chosen_imp = [primes[j] for j in chosen]
    term_gate = factoring_create_terms(chosen_imp)
    out_edge.append((or_literal(term_gate), outputs[i]))

optimize_netlist()

print("[in]")
for s, t in in_edge:
    print(f"{s}->{t}")
print("[out]")
for o in outputs:
    for src, tgt in out_edge:
        if tgt == o:
            print(f"{src}->{tgt}")
