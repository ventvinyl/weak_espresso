from concurrent.futures import ThreadPoolExecutor, as_completed
from collections import deque, defaultdict
from typing import List
from dataclasses import dataclass, field

@dataclass
class implicant:
    mask: int = 0
    dc: int = 0
    covers: List[int] = field(default_factory=list)

I, O, rows, and_cnt, or_cnt, not_cnt, xor_cnt = 0, 0, 0, 0, 0, 0, 0
in_edge, out_edge, inputs, outputs = [], [], [], []
not_in, not_wire, literal_and, literal_or, literal_xor = {}, {}, {}, {}, {}

def const_one():
    return "1"

def const_zero():
    return "0"

def wnot(i):
    global not_cnt, not_in, in_edge, inputs
    if i in not_in:
        return not_in[i]
    not_cnt += 1
    name = "NOT" + str(not_cnt)
    not_in[i] = name
    in_edge.append((inputs[i], name))
    return name

def not_wire(src):
    global not_cnt, not_wire, in_edge, I
    if src == "1":
        return "0"
    if src == "0":
        return "1"
    if len(src) == 1 and 'A' <= src[0] < chr(ord('A') + I):
        idx = ord(src[0]) - ord('A')
        return wnot(idx)
    if src in not_wire:
        return not_wire[src]
    not_cnt += 1
    name = "NOT" + str(not_cnt)
    not_wire[src] = name
    in_edge.append((src, name))
    return name

def new_and(a, b):
    global and_cnt, in_edge
    and_cnt += 1
    name = "AND" + str(and_cnt)
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def new_or(a, b):
    global or_cnt, in_edge
    or_cnt += 1
    name = "OR" + str(or_cnt)
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def new_xor(a, b):
    global xor_cnt, in_edge
    xor_cnt += 1
    name = "XOR" + str(xor_cnt)
    in_edge.append((a, name))
    in_edge.append((b, name))
    return name

def and_literal(lits):
    global literal_and
    if not lits:
        return const_one()
    lits = sorted(lits)
    key = "AND:" + ",".join(lits) + ","
    if key in literal_and:
        return literal_and[key]
    
    dq = deque(lits)
    while len(dq) > 1:
        next_items = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_and(a, b)
            next_items.append(g)
        if dq:
            next_items.append(dq.popleft())
        dq.clear()
        for x in next_items:
            dq.append(x)
    
    final = dq[0]
    literal_and[key] = final
    return final

def or_literal(terms):
    global literal_or
    if not terms:
        return const_zero()
    terms = sorted(terms)
    key = "OR:" + ",".join(terms) + ","
    if key in literal_or:
        return literal_or[key]
    
    dq = deque(terms)
    while len(dq) > 1:
        next_items = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_or(a, b)
            next_items.append(g)
        if dq:
            next_items.append(dq.popleft())
        dq.clear()
        for x in next_items:
            dq.append(x)
    
    final = dq[0]
    literal_or[key] = final
    return final

def literal_xor(terms):
    global literal_xor
    if not terms:
        return const_zero()
    terms = sorted(terms)
    key = "XOR:" + ",".join(terms) + ","
    if key in literal_xor:
        return literal_xor[key]
    
    dq = deque(terms)
    while len(dq) > 1:
        next_items = []
        while len(dq) >= 2:
            a = dq.popleft()
            b = dq.popleft()
            g = new_xor(a, b)
            next_items.append(g)
        if dq:
            next_items.append(dq.popleft())
        dq.clear()
        for x in next_items:
            dq.append(x)
    
    final = dq[0]
    literal_xor[key] = final
    return final

def convert(imp):
    global I
    ret = []
    for i in range(I):
        bitpos = I - 1 - i
        if imp.dc & (1 << bitpos):
            continue
        val = (imp.mask >> bitpos) & 1
        ret.append((i, val))
    return ret

def work_gate(imp):
    global inputs
    lits = convert(imp)
    if not lits:
        return const_one()
    lit_name = []
    for p in lits:
        if p[1] == 1:
            lit_name.append(inputs[p[0]])
        else:
            lit_name.append(wnot(p[0]))
    if len(lit_name) == 1:
        return lit_name[0]
    return and_literal(lit_name)

"""
def popcount(x):
    return bin(x).count('1')
"""

def popcount(n):
    a = n
    a = ((a >> 1) & 0x55555555) + (a & 0x55555555)
    a = ((a >> 2) & 0x33333333) + (a & 0x33333333)
    a = ((a >> 4) & 0x0F0F0F0F) + (a & 0x0F0F0F0F)
    a = ((a >> 8) & 0x00FF00FF) + (a & 0x00FF00FF)
    a = ((a >> 16) & 0x0000FFFF) + (a & 0x0000FFFF)
    return a

def qm_prime_implicants(minterms):
    cur = []
    for m in minterms:
        imp = implicant()
        imp.mask = m
        imp.dc = 0
        imp.covers = [m]
        cur.append(imp)
    
    primes = []
    
    while True:
        n = len(cur)
        merged = [False] * n
        next_items = []
        groups = defaultdict(list)
        
        for i in range(n):
            cnt = popcount(cur[i].mask & ~cur[i].dc)
            groups[cnt].append(i)
        
        for i in groups:
            if i + 1 not in groups:
                continue
            for j in groups[i]:
                for k in groups[i + 1]:
                    if cur[j].dc != cur[k].dc:
                        continue
                    diff = cur[j].mask ^ cur[k].mask
                    if popcount(diff) != 1:
                        continue
                    nim = implicant()
                    nim.dc = cur[j].dc | diff
                    nim.mask = cur[j].mask & ~diff
                    nim.covers = cur[j].covers + cur[k].covers
                    nim.covers = sorted(list(set(nim.covers)))
                    next_items.append(nim)
                    merged[j] = merged[k] = True
        
        for i in range(n):
            if not merged[i]:
                primes.append(cur[i])
        
        if not next_items:
            break
        
        uniq = []
        for x in next_items:
            found = False
            for y in uniq:
                if x.mask == y.mask and x.dc == y.dc:
                    found = True
                    break
            if not found:
                uniq.append(x)
        cur = uniq
    
    ret = []
    for p in primes:
        found = False
        for q in ret:
            if p.mask == q.mask and p.dc == q.dc:
                found = True
                break
        if not found:
            ret.append(p)
    
    return ret

def select_primes_for_cover(minterms, primes):
    m = len(minterms)
    m_id = {}
    for i in range(m):
        m_id[minterms[i]] = i
    
    p = len(primes)
    covers = [[] for _ in range(p)]
    for p in range(p):
        for v in primes[p].covers:
            if v in m_id:
                covers[p].append(m_id[v])
    
    cover_cnt = [0] * m
    for p in range(p):
        for x in covers[p]:
            cover_cnt[x] += 1
    
    chosen = [False] * p
    covered = [False] * m
    result = []
    
    for i in range(m):
        if cover_cnt[i] == 1:
            for p in range(p):
                for x in covers[p]:
                    if x == i:
                        if not chosen[p]:
                            chosen[p] = True
                            result.append(p)
                            for y in covers[p]:
                                if not covered[y]:
                                    covered[y] = True
                        break
    
    while True:
        bestp = -1
        bestcov = 0
        for p in range(p):
            if not chosen[p]:
                cnt = 0
                for x in covers[p]:
                    if not covered[x]:
                        cnt += 1
                if cnt > bestcov:
                    bestcov = cnt
                    bestp = p
        
        if bestp == -1 or bestcov == 0:
            break
        
        chosen[bestp] = True
        result.append(bestp)
        for x in covers[bestp]:
            covered[x] = True
    
    return result

class bit_matrix:
    def __init__(self, r=0, c=0):
        self.init(r, c)
    
    def init(self, r, c):
        self.nrows = r
        self.ncols = c
        self.nwords = (c + 63) // 64
        self.rows = [[0] * self.nwords for _ in range(self.nrows)]
    
    def set_bit(self, r, c):
        self.rows[r][c >> 6] |= (1 << (c & 63))
    
    def test(self, r, c):
        return bool((self.rows[r][c >> 6] >> (c & 63)) & 1)
    
    def xor_row_into(self, tgt, src):
        for w in range(self.nwords):
            self.rows[tgt][w] ^= self.rows[src][w]
    
    def swap_row(self, a, b):
        self.rows[a], self.rows[b] = self.rows[b], self.rows[a]

def gaussian_solve_bitpacked(m):
    r = m.nrows
    c = m.ncols
    vars_count = c - 1
    where = [-1] * vars_count
    row = 0
    
    for col in range(vars_count):
        if row >= r:
            break
        
        sel = -1
        for i in range(row, r):
            if m.test(i, col):
                sel = i
                break
        
        if sel == -1:
            continue
        
        if sel != row:
            m.swap_row(sel, row)
        
        where[col] = row
        
        for i in range(r):
            if i != row and m.test(i, col):
                m.xor_row_into(i, row)
        
        row += 1
    
    for i in range(row, r):
        if m.test(i, c - 1):
            return False, []
    
    ans = [0] * vars_count
    for i in range(vars_count):
        if where[i] != -1:
            ans[i] = 1 if m.test(where[i], c - 1) else 0
    
    return True, ans

def check_affine_xor_bitpacked(f):
    global I, rows
    nvars = I
    rows_list = []
    for r in range(rows):
        if f[r] != -1:
            rows_list.append(r)
    
    eqs = len(rows_list)
    vars_count = nvars + 1
    
    if eqs == 0:
        return True, [0] * (nvars + 1)
    
    m = bit_matrix(eqs, vars_count + 1)
    
    for ri in range(eqs):
        r = rows_list[ri]
        for i in range(nvars):
            bit = (r >> (nvars - 1 - i)) & 1
            if bit:
                m.set_bit(ri, i)
        m.set_bit(ri, nvars)
        if f[r]:
            m.set_bit(ri, vars_count)
    
    success, sol = gaussian_solve_bitpacked(m)
    if not success:
        return False, []
    
    ret = [0] * (nvars + 1)
    ret[nvars] = sol[nvars]
    for i in range(nvars):
        ret[i] = sol[i]
    
    return True, ret

def try_xor_cover_with_primes_bitpacked(primes, f, sel_out):
    global rows
    r = rows
    p = len(primes)
    if p == 0:
        return False
    
    rows_list = []
    for r in range(r):
        if f[r] != -1:
            rows_list.append(r)
    
    n = len(rows_list)
    if n == 0:
        sel_out[:] = [0] * p
        return True
    
    m = bit_matrix(n, p + 1)
    
    for i in range(n):
        r = rows_list[i]
        for p in range(p):
            mask = primes[p].mask
            dc = primes[p].dc
            if (r & ~dc) == mask:
                m.set_bit(i, p)
        if f[r]:
            m.set_bit(i, p)
    
    success, sol = gaussian_solve_bitpacked(m)
    if not success:
        return False
    
    sel_out[:] = [0] * p
    for p in range(p):
        sel_out[p] = sol[p]
    
    return True

def factoring_create_terms(implics):
    global I, inputs
    terms = []
    
    for i in implics:
        s = set()
        for b in range(I):
            bitpos = I - 1 - b
            if i.dc & (1 << bitpos):
                continue
            val = (i.mask >> bitpos) & 1
            if val:
                s.add(inputs[b])
            else:
                s.add("~" + inputs[b])
        terms.append(s)
    
    results = []
    
    while terms:
        if len(terms) == 1:
            t = terms[0]
            lits = []
            for lit in t:
                if len(lit) > 0 and lit[0] == '~':
                    v = lit[1:]
                    idx = ord(v[0]) - ord('A')
                    lits.append(wnot(idx))
                else:
                    lits.append(lit)
            
            if not lits:
                g = const_one()
            elif len(lits) == 1:
                g = lits[0]
            else:
                g = and_literal(lits)
            
            results.append(g)
            break
        
        freq = defaultdict(int)
        for t in terms:
            for lit in t:
                freq[lit] += 1
        
        best_lit = ""
        best_cnt = 0
        for lit, cnt in freq.items():
            if cnt > best_cnt:
                best_cnt = cnt
                best_lit = lit
        
        if best_cnt < 2:
            for t in terms:
                lits = []
                for lit in t:
                    if len(lit) > 0 and lit[0] == '~':
                        v = lit[1:]
                        idx = ord(v[0]) - ord('A')
                        lits.append(wnot(idx))
                    else:
                        lits.append(lit)
                
                if not lits:
                    g = const_one()
                elif len(lits) == 1:
                    g = lits[0]
                else:
                    g = and_literal(lits)
                
                results.append(g)
            break
        
        with_terms = []
        without_terms = []
        for t in terms:
            if best_lit in t:
                with_terms.append(t)
            else:
                without_terms.append(t)
        
        rem_gate = []
        for t in with_terms:
            r = t.copy()
            r.discard(best_lit)
            lits = []
            for lit in r:
                if len(lit) > 0 and lit[0] == '~':
                    v = lit[1:]
                    idx = ord(v[0]) - ord('A')
                    lits.append(wnot(idx))
                else:
                    lits.append(lit)
            
            if not lits:
                rg = const_one()
            elif len(lits) == 1:
                rg = lits[0]
            else:
                rg = and_literal(lits)
            
            rem_gate.append(rg)
        
        or_rem = or_literal(rem_gate)
        
        if len(best_lit) > 0 and best_lit[0] == '~':
            v = best_lit[1:]
            lit_wire = wnot(ord(v[0]) - ord('A'))
        else:
            lit_wire = best_lit
        
        factored = and_literal([lit_wire, or_rem])
        results.append(factored)
        terms = without_terms
    
    return results

def optimize_netlist():
    global in_edge, out_edge
    
    gate_inputs = defaultdict(list)
    gate_type = {}
    
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
    
    def replace_wire(oldw, neww):
        if oldw == neww:
            return
        
        for _, vec in gate_inputs.items():
            for i in range(len(vec)):
                if vec[i] == oldw:
                    vec[i] = neww
        
        for i in range(len(out_edge)):
            if out_edge[i][0] == oldw:
                out_edge[i] = (neww, out_edge[i][1])
        
        for i in range(len(in_edge)):
            if in_edge[i][0] == oldw:
                in_edge[i] = (neww, in_edge[i][1])
    
    while changed and passes < 10:
        changed = False
        passes += 1
        gates = list(gate_inputs.keys())
        
        for g in gates:
            typ = gate_type.get(g, "")
            ins = gate_inputs[g]
            ins.sort()
            unique_ins = []
            for x in ins:
                if not unique_ins or unique_ins[-1] != x:
                    unique_ins.append(x)
            gate_inputs[g] = unique_ins
            ins = gate_inputs[g]
            
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
                        inner = gate_inputs[a][0]
                        replace_wire(g, inner)
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
                    ins = gate_inputs[g]
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
                    ins = gate_inputs[g]
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
    
    for src, _ in out_edge:
        if src:
            dq.append(src)
            reachable.add(src)
    
    while dq:
        w = dq.popleft()
        if w in gate_inputs:
            for s in gate_inputs[w]:
                if s not in ["0", "1"] and s not in reachable:
                    reachable.add(s)
                    dq.append(s)
    
    new_in = []
    seen = set()
    for g, inputs_list in gate_inputs.items():
        if g not in reachable:
            continue
        for s in inputs_list:
            key = s + "->" + g
            if key not in seen:
                seen.add(key)
                new_in.append((s, g))
    
    in_edge[:] = new_in
    
    new_out = []
    seen = set()
    for src, tgt in out_edge:
        key = src + "->" + tgt
        if key not in seen:
            seen.add(key)
            new_out.append((src, tgt))
    
    out_edge[:] = new_out

@dataclass
class out_plan:
    is_affine: bool = False
    affine_coeff: List[int] = field(default_factory=list)
    is_const: bool = False
    const_val: int = 0
    is_xor: bool = False
    implicants: List[implicant] = field(default_factory=list)

def process_output(oid, table):
    global I, O, rows
    
    plan = out_plan()
    f = [0] * rows
    on_set = []
    dc_set = []
    
    for r in range(rows):
        f[r] = table[r][I + oid]
        if f[r] == 1:
            on_set.append(r)
        elif f[r] == -1:
            dc_set.append(r)
    
    success, lin = check_affine_xor_bitpacked(f)
    if success:
        plan.is_affine = True
        plan.affine_coeff = lin
        return plan
    
    if not on_set:
        plan.is_const = True
        plan.const_val = 0
        return plan
    
    primesSeed = on_set + dc_set
    primesSeed = sorted(list(set(primesSeed)))
    
    primes = qm_prime_implicants(primesSeed)
    sel = [0] * len(primes)
    okxor = try_xor_cover_with_primes_bitpacked(primes, f, sel)
    
    if okxor:
        plan.is_xor = True
        for p in range(len(primes)):
            if sel[p]:
                plan.implicants.append(primes[p])
        return plan
    
    chosen = select_primes_for_cover(on_set, primes)
    for i in chosen:
        plan.implicants.append(primes[i])
    
    return plan

line = input().strip()
if not line:
    exit(0)
 
parts = line.split()
I, O = int(parts[0]), int(parts[1])
rows = 1 << I
 
table = [[0] * (I + O) for _ in range(rows)]
 
for _ in range(rows):
    line = input().strip()
    tmp = line.split()
    
    id = 0
    for i in range(I):
        if tmp[i] == "1":
            id |= (1 << (I - 1 - i))
        elif tmp[i] != "0":
            if tmp[i] and tmp[i][0] == '1':
                id |= (1 << (I - 1 - i))
    
    for k in range(I + O):
        if k < I:
            table[id][k] = 1 if tmp[k] == "1" else 0
        else:
            s = tmp[k]
            if s == "1":
                table[id][k] = 1
            elif s == "0":
                table[id][k] = 0
            elif s in ["X", "x"]:
                table[id][k] = -1
            else:
                table[id][k] = 1 if s == "1" else 0
 
inputs.clear()
outputs.clear()
for i in range(I):
    inputs.append(chr(ord('A') + i))
for j in range(O):
    outputs.append(chr(ord('A') + I + j))
 
with ThreadPoolExecutor(max_workers=O) as executor:
    futures = {}
    for i in range(O):
        future = executor.submit(process_output, i, table)
        futures[future] = i
    
    plans = [None] * O
    for future in as_completed(futures):
        i = futures[future]
        plans[i] = future.result()
 
for i in range(O):
    plan = plans[i]
    out_label = outputs[i]
    
    if plan.is_affine:
        vars_to_xor = []
        for i in range(I):
            if plan.affine_coeff[i] == 1:
                vars_to_xor.append(inputs[i])
        
        if not vars_to_xor:
            g = const_one() if plan.affine_coeff[I] == 1 else const_zero()
            out_edge.append((g, out_label))
        elif len(vars_to_xor) == 1:
            g = vars_to_xor[0]
            if plan.affine_coeff[I] == 1:
                g = not_wire(g)
            out_edge.append((g, out_label))
        else:
            g = literal_xor(vars_to_xor)
            if plan.affine_coeff[I] == 1:
                g = not_wire(g)
            out_edge.append((g, out_label))
        continue
    
    if plan.is_const:
        out_edge.append((const_one() if plan.const_val else const_zero(), out_label))
        continue
    
    if plan.is_xor:
        term_gate = []
        for imp in plan.implicants:
            term_gate.append(work_gate(imp))
        
        if not term_gate:
            out_edge.append((const_zero(), out_label))
        else:
            g = literal_xor(term_gate)
            out_edge.append((g, out_label))
        continue
    
    term_gate = factoring_create_terms(plan.implicants)
    final_gate = or_literal(term_gate)
    out_edge.append((final_gate, out_label))
 
optimize_netlist()
 
print("[in]")
for src, tgt in in_edge:
    print(f"{src}->{tgt}")
 
print("[out]")
for out_label in outputs:
    for src, tgt in out_edge:
        if tgt == out_label:
            print(f"{src}->{tgt}")
