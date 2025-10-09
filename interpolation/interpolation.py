"""
by hanbyoel lee(known as ventvinyl, youngyangze, nttntt1)
wrote in utf-8
using MIT LICENSE
"""

import sys
import random
from typing import List, Tuple, Optional, Dict
from math import gcd, isqrt

MAX_CANDIDATE_QUEUE = 512
MIN_CANDIDATE_PRIMES = 120

ENABLE_FIND_64BIT_PRIMES = True
FIND_64_START = 2147483648
FIND_64_END = 2147600000
MAX_64_PRIMES = 6
MIN_V2_FOR_NTT = 20

EXTRA_PRIME_SEARCH_START = 1000003
EXTRA_PRIME_SEARCH_END = 2147483647

random.seed(0x28ADE1877EB2)

def miller_rabin(n: int) -> bool:
    """
    tests n's primality
    """
    if n < 2:
        return False
    small_primes = (2,3,5,7,11,13,17,19,23,29,31,37)
    for p in small_primes:
        if n % p == 0:
            return n == p
    d = n - 1
    s = 0
    while d & 1 == 0:
        d >>= 1
        s += 1
    bases = (2, 325, 9375, 28178, 450775, 9780504, 1795265022)
    for a in bases:
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x == 1 or x == n - 1:
            continue
        composite = True
        for _ in range(s - 1):
            x = (x * x) % n
            if x == n - 1:
                composite = False
                break
        if composite:
            return False
    return True

def pollard_rho_one(n: int) -> int:
    """
    finds n's non-trivial factor (returns 0 when not possible)
    """
    if (n & 1) == 0: # n%2==0
        return 2
    if n % 3 == 0:
        return 3
    for _ in range(6):
        c = random.randrange(1, n)
        x = random.randrange(2, n - 1)
        y = x
        d = 1
        def f(v: int) -> int:
            return (v * v + c) % n
        i = 0
        while d == 1:
            x = f(x)
            y = f(f(y))
            diff = x - y if x > y else y - x
            d = gcd(diff, n)
            if d == n:
                break
            i += 1
            if i > 200000:
                break
        if d > 1 and d < n:
            return d
    return 0

def factor_pollard_rec(n: int, out: List[int]) -> None:
    """
    supports prime_factors_pollard
    """
    if n == 1:
        return
    if miller_rabin(n):
        out.append(n)
        return
    d = 0
    for _ in range(8):
        d = pollard_rho_one(n)
        if d:
            break
    if d == 0:
        p = 2
        while p * p <= n:
            if n % p == 0:
                while n % p == 0:
                    n //= p
                out.append(p)
                factor_pollard_rec(n, out)
                return
            p += 1
        if n > 1:
            out.append(n)
        return
    factor_pollard_rec(d, out)
    factor_pollard_rec(n // d, out)

def prime_factors_pollard(n: int) -> List[int]:
    """
    does prime factorize on n
    """
    fac: List[int] = []
    factor_pollard_rec(n, fac)
    fac.sort()
    unique = []
    for f in fac:
        if not unique or unique[-1] != f:
            unique.append(f)
    return unique

def find_primitive_root_pollard(p: int) -> int:
    """
    finds primitive root of p
    """
    if p == 2:
        return 1
    phi = p - 1
    fac = prime_factors_pollard(phi)
    for g in range(2, p):
        ok = True
        for q in fac:
            if pow(g, phi // q, p) == 1:
                ok = False
                break
        if ok:
            return g
    return 0

class NTTContext:
    def __init__(self, mod: int = 0, pr: int = 0):
        self.MOD = mod
        self.PR = pr
        self.rev_map: Dict[int, List[int]] = {}
        self.roots_map: Dict[int, List[int]] = {}

    def ensure(self, n: int) -> None:
        """
        caches and calculates rev and roots on n(2's power)
        """
        if n in self.rev_map:
            return
        rev = [0] * n
        logn = n.bit_length() - 1
        for i in range(n):
            x = i
            y = 0
            for _ in range(logn):
                y = (y << 1) | (x & 1)
                x >>= 1
            rev[i] = y
        root_pw = pow(self.PR, (self.MOD - 1) // n, self.MOD)
        roots = [1] * n
        for i in range(1, n):
            roots[i] = (roots[i - 1] * root_pw) % self.MOD
        self.rev_map[n] = rev
        self.roots_map[n] = roots

    def ntt(self, a: List[int], inv: int) -> None:
        """
        https://cubelover.tistory.com/12
        """
        n = len(a)
        self.ensure(n)
        rev = self.rev_map[n]
        roots = self.roots_map[n]
        for i in range(1, n):
            j = rev[i]
            if i < j:
                a[i], a[j] = a[j], a[i]
        length = 2
        while length <= n:
            step = n // length
            i = 0
            while i < n:
                idx = 0
                half = length // 2
                for j in range(half):
                    u = a[i + j]
                    v = (roots[idx] * a[i + j + half]) % self.MOD
                    x = u + v
                    if x >= self.MOD:
                        x -= self.MOD
                    y = u - v if u >= v else u + self.MOD - v
                    a[i + j] = x
                    a[i + j + half] = y
                    idx += step
                i += length
            length <<= 1
        if inv == -1:
            invn = pow(n, self.MOD - 2, self.MOD)
            for i in range(n):
                a[i] = (a[i] * invn) % self.MOD
            a[1:] = list(reversed(a[1:]))

Poly = List[int]

def add_mod_u(a: int, b: int, MOD: int) -> int:
    """
    calculates (a+b) mod MOD
    """
    s = a + b
    return s - (s >= MOD) * MOD

def sub_mod_u(a: int, b: int, MOD: int) -> int:
    """
    calculates (a-b) mod MOD
    """
    s = a - b
    return s + (s >= MOD) * MOD

def multiply_mod_u_ctx(a: Poly, b: Poly, MOD: int, ctx: NTTContext) -> Poly:
    """
    convolution on a and b
    """
    if not a or not b:
        return []
    need = len(a) + len(b) - 1
    n = 1
    while n < need:
        n <<= 1
    # naive algorithm when ntt is not available
    if ((MOD - 1) % n) != 0:
        res = [0] * need
        A = len(a); B = len(b)
        for i in range(A):
            ai = a[i]
            for j in range(B):
                prod = (ai * b[j]) % MOD
                cur = res[i + j] + prod
                if cur >= MOD:
                    cur -= MOD
                res[i + j] = cur
        return res
    fa = a[:] + [0] * (n - len(a))
    fb = b[:] + [0] * (n - len(b))
    ctx.ensure(n)
    ctx.ntt(fa, +1)
    ctx.ntt(fb, +1)
    for i in range(n):
        fa[i] = (fa[i] * fb[i]) % MOD
    ctx.ntt(fa, -1)
    return fa[:need]

def add_mod_u_poly(a: Poly, b: Poly, MOD: int) -> Poly:
    n = max(len(a), len(b))
    r = [0] * n
    for i in range(n):
        va = a[i] if i < len(a) else 0
        vb = b[i] if i < len(b) else 0
        s = va + vb
        if s >= MOD:
            s -= MOD
        r[i] = s - (s >= MOD) * MOD
    return r

def sub_mod_u_poly(a: Poly, b: Poly, MOD: int) -> Poly:
    n = max(len(a), len(b))
    r = [0] * n
    for i in range(n):
        va = a[i] if i < len(a) else 0
        vb = b[i] if i < len(b) else 0
        r[i] = va - vb if va >= vb else va + MOD - vb
    return r

def trim_u(a: Poly) -> None:
    """
    deletes high-degree term which has 0 coefficient
    """
    while a and a[-1] == 0:
        a.pop()

def poly_inv_u_ctx(A: Poly, k: int, MOD: int, ctx: NTTContext) -> Poly:
    """
    finds multiplicative inverse in polynomial A
    """
    R = [pow(A[0], MOD - 2, MOD)]
    cur = 1
    while cur < k:
        cur <<= 1
        A_cut = A[:min(len(A), cur)]
        AR = multiply_mod_u_ctx(A_cut, R, MOD, ctx)
        AR = AR[:cur]
        for i in range(len(AR)):
            AR[i] = 0 if AR[i] == 0 else MOD - AR[i]
        AR[0] = (AR[0] + 2) % MOD
        newR = multiply_mod_u_ctx(R, AR, MOD, ctx)
        newR = newR[:cur]
        R = newR
    return R[:k]

def poly_mod(A_in: Poly, B: Poly, MOD: int, ctx: NTTContext) -> Poly:
    """
    calculates A mod B
    """
    A = A_in[:]
    trim_u(A)
    BB = B[:]
    trim_u(BB)
    n = len(A); m = len(BB)
    if m == 0:
        return []
    if n < m:
        return A
    k = n - m + 1
    revA = A[::-1][:n]
    revB = BB[::-1][:m]
    invRevB = poly_inv_u_ctx(revB, k, MOD, ctx)
    qrev = multiply_mod_u_ctx(revA, invRevB, MOD, ctx)[:k]
    q = qrev[::-1]
    qB = multiply_mod_u_ctx(q, BB, MOD, ctx)
    if len(qB) < n:
        qB += [0] * (n - len(qB))
    Apad = A[:] + [0] * (len(qB) - len(A))
    r = sub_mod_u_poly(Apad, qB, MOD)
    r = r[:m-1]
    trim_u(r)
    return r

def eval_poly(a: Poly, x: int, MOD: int) -> int:
    """
    calculates (((a[n]*x+a[n-1])*x+a[n-2])*x+...) mod MOD
    """
    res = 0
    for coef in reversed(a):
        res = (res * x + coef) % MOD
    return res

def prase_rational(s: str) -> Tuple[int, int]:
    """
    converts s(formed like a/b) to (a,b) in tuple
    """
    slash = s.find('/')
    if slash == -1:
        neg = False
        i = 0
        if s and (s[0] == '+' or s[0] == '-'):
            if s[0] == '-':
                neg = True
            i = 1
        v = 0
        while i < len(s):
            if not s[i].isdigit():
                raise RuntimeError("bad rational input")
            v = v * 10 + int(s[i])
            i += 1
        if neg:
            v = -v
        return (v, 1)
    else:
        A = prase_rational(s[:slash])
        B = prase_rational(s[slash + 1:])
        if B[0] == 0:
            raise RuntimeError("bad rational denom")
        num = A[0] * B[1]
        den = A[1] * B[0]
        if den < 0:
            num = -num
            den = -den
        g = gcd(abs(num), abs(den))
        if g != 0:
            num //= g
            den //= g
        return (num, den)

def int_mod(a: int, MOD: int) -> int:
    """
    calculates a mod MOD
    """
    r = a % MOD
    return r + (r < 0) * MOD

def garner_to_XmodM(residues: List[int], mods: List[int]) -> int:
    """
    https://cp-algorithms.com/algebra/garners-algorithm.html
    """
    k = len(mods)
    c = [0] * k
    inv = [[0] * k for _ in range(k)]
    for j in range(k):
        for i in range(j + 1, k):
            inv[j][i] = pow(mods[j] % mods[i], mods[i] - 2, mods[i])
    for i in range(k):
        t = residues[i]
        for j in range(i):
            cj = c[j]
            mi = mods[i]
            tmp = (inv[j][i] * ((t - cj) % mi + mi)) % mi
            if tmp < 0:
                tmp += mi
            t = tmp
        c[i] = t
    x = 0
    Mpref = 1
    for i in range(k):
        x += Mpref * c[i]
        Mpref *= mods[i]
    if x < 0:
        M = Mpref
        x %= M
        if x < 0:
            x += M
    return x

def crt_all(mods_residues: List[List[int]], mods: List[int]) -> List[int]:
    k = len(mods_residues)
    deg = len(mods_residues[0])
    out = [0] * deg
    for j in range(deg):
        r = [mods_residues[i][j] for i in range(k)]
        out[j] = garner_to_XmodM(r, mods)
    return out

def rational_reconstruct(A: int, M: int) -> Optional[Tuple[int, int]]:
    """
    https://coursys.sfu.ca/2018sp-cmpt-384-d1/pages/Wang
    """
    if M == 0:
        return None
    if A % M == 0:
        return (0, 1)
    halfM = M // 2
    r0 = M
    r1 = A % M
    if r1 < 0:
        r1 += M
    s0 = 0
    s1 = 1
    while True:
        rr = r1 * r1
        if rr <= halfM:
            break
        if r1 == 0:
            break
        q = r0 // r1
        r2 = r0 - q * r1
        s2 = s0 - q * s1
        r0 = r1; r1 = r2; s0 = s1; s1 = s2
    if r1 == 0:
        return None
    p = r1
    q = s1
    if q < 0:
        p = -p; q = -q
    if q == 0:
        return None
    bound = isqrt(halfM)
    if q > bound:
        return None
    if p < -bound or p > bound:
        return None
    lhs = (A * q - p) % M
    if lhs < 0:
        lhs += M
    if lhs != 0:
        return None
    g = gcd(abs(p), abs(q))
    if g != 0:
        p //= g; q //= g
    return (p, q)

def segmented_primes(start: int, end: int, need: int) -> List[int]:
    if start < 2:
        start = 2
    limit = int(end**0.5) + 1
    base = [True] * (limit + 1)
    primes = []
    for i in range(2, limit + 1):
        if base[i]:
            primes.append(i)
            for j in range(i * i, limit + 1, i):
                base[j] = False
    segment_size = max(32768, min(1 << 20, end - start + 1))
    result = []
    low = start
    while low <= end and len(result) < need:
        high = min(low + segment_size - 1, end)
        mark = [True] * (high - low + 1)
        for p in primes:
            start_idx = (low + p - 1) // p * p
            if start_idx < p * p:
                start_idx = p * p
            for j in range(start_idx, high + 1, p):
                mark[j - low] = False
        for i, is_prime in enumerate(mark):
            if is_prime:
                val = low + i
                if val >= 2:
                    result.append(val)
                    if len(result) >= need:
                        break
        low = high + 1
    return result

def find_additional_32bit_primes(start: int, end: int, need: int) -> List[int]:
    if need <= 0:
        return []
    if end < start:
        return []
    return segmented_primes(start, end, need)

def interpolate(MOD: int, PR: int, xs_mod: List[int], ys_mod: List[int], ctx: NTTContext) -> List[int]:
    n = len(xs_mod)
    sizeTree = 4 * n + 5
    M_tree = [None] * sizeTree
    def build(idx: int, l: int, r: int) -> None:
        if l == r:
            p = [ (MOD - xs_mod[l] % MOD) % MOD, 1 % MOD ]
            M_tree[idx] = p
            return
        mid = (l + r) >> 1
        build(idx << 1, l, mid)
        build((idx << 1) | 1, mid + 1, r)
        M_tree[idx] = multiply_mod_u_ctx(M_tree[idx << 1], M_tree[(idx << 1) | 1], MOD, ctx)
    build(1, 0, n - 1)
    W = M_tree[1]
    Wd = [0] * max(0, len(W) - 1)
    for i in range(1, len(W)):
        Wd[i - 1] = (W[i] * i) % MOD
    Wd_at = [0] * n
    def remd(idx: int, l: int, r: int, rnode: Poly) -> None:
        if l == r:
            Wd_at[l] = eval_poly(rnode, xs_mod[l], MOD)
            return
        remL = poly_mod(rnode, M_tree[idx << 1], MOD, ctx)
        remR = poly_mod(rnode, M_tree[(idx << 1) | 1], MOD, ctx)
        mid = (l + r) >> 1
        remd(idx << 1, l, mid, remL)
        remd((idx << 1) | 1, mid + 1, r, remR)
    remd(1, 0, n - 1, Wd)
    a_mod = [0] * n
    for i in range(n):
        denom = Wd_at[i]
        if denom == 0:
            print("Error: derivative zero mod prime", file=sys.stderr)
            sys.exit(1)
        inv = pow(denom, MOD - 2, MOD)
        a_mod[i] = (ys_mod[i] * inv) % MOD
    def buildS(idx: int, l: int, r: int) -> Poly:
        if l == r:
            return [ a_mod[l] % MOD ]
        mid = (l + r) >> 1
        Sl = buildS(idx << 1, l, mid)
        Sr = buildS((idx << 1) | 1, mid + 1, r)
        leftmul = multiply_mod_u_ctx(Sl, M_tree[(idx << 1) | 1], MOD, ctx)
        rightmul = multiply_mod_u_ctx(Sr, M_tree[idx << 1], MOD, ctx)
        return add_mod_u_poly(leftmul, rightmul, MOD)
    Pmod = buildS(1, 0, n - 1)
    if len(Pmod) < n:
        Pmod += [0] * (n - len(Pmod))
    out_coeffs = [Pmod[i] if i < len(Pmod) else 0 for i in range(n)]
    return out_coeffs

CANDIDATE_PRIMES_32 = [
    167772161, 469762049, 754974721, 998244353, 1004535809,
    1045430273, 1053818881, 1224736769, 880803841, 645922817,
    7340033, 13631489, 152043521, 2013265921, 2113929217,
    1007681537, 1012924417, 1157627903, 1225054737, 1468006401,
    918552577, 279620401, 295279001, 321126553, 980995281,
    492283321, 506654539, 663351321, 771751937, 813802753
]

def find_64bit_primes_in_range(start: int, end: int, need_count: int, min_v2: int) -> List[int]:
    found = []
    if start % 2 == 0:
        start += 1
    p = start
    while p <= end and len(found) < need_count:
        if miller_rabin(p):
            t = p - 1
            cnt = 0
            while (t & 1) == 0:
                t >>= 1
                cnt += 1
                if cnt >= min_v2:
                    break
            if cnt >= min_v2:
                found.append(p)
        p += 2
    return found

try:
    n = int(sys.stdin.readline().strip())
except:
    exit(0)
if n <= 0:
    exit(0)
xs: List[Tuple[int,int]] = []
ys: List[Tuple[int,int]] = []
for _ in range(n):
    parts = sys.stdin.readline().strip().split()
    if len(parts) < 2:
        raise RuntimeError("invalid input")
    sx, sy = parts[0], parts[1]
    xs.append(prase_rational(sx))
    ys.append(prase_rational(sy))
for i in range(n):
    for j in range(i+1, n):
        if xs[i][0] * xs[j][1] == xs[j][0] * xs[i][1]:
            print("duplicate x values", file=sys.stderr)
            exit(0)
candidate = list(CANDIDATE_PRIMES_32)
if ENABLE_FIND_64BIT_PRIMES:
    extra = find_64bit_primes_in_range(FIND_64_START, FIND_64_END, MAX_64_PRIMES, MIN_V2_FOR_NTT)
    candidate.extend(extra)
candidate = sorted(set(candidate))
if len(candidate) < MIN_CANDIDATE_PRIMES:
    need = MIN_CANDIDATE_PRIMES - len(candidate)
    extra = find_additional_32bit_primes(EXTRA_PRIME_SEARCH_START, EXTRA_PRIME_SEARCH_END, need)
    candidate.extend(extra)
usable = []
for p in candidate:
    if p < 3:
        continue
    if miller_rabin(p):
        usable.append(p)
if len(usable) < MIN_CANDIDATE_PRIMES:
    need = MIN_CANDIDATE_PRIMES - len(usable)
    extra = find_additional_32bit_primes(2000003, EXTRA_PRIME_SEARCH_END, need)
    usable.extend(extra)
if not usable:
    print("no usable prime", file=sys.stderr)
    exit(0)
class PrimeInfo:
    def __init__(self, p: int, v2: int, score: int):
        self.p = p; self.v2 = v2; self.score = score
pinfos: List[PrimeInfo] = []
for p in usable:
    t = p - 1
    # count trailing zeros (v2)
    v2 = 0
    while (t & 1) == 0:
        v2 += 1
        t >>= 1
    score = v2 * 1000000000 - min(p, 9223372036854775807)
    pinfos.append(PrimeInfo(p, v2, score))
pinfos.sort(key=lambda a: (-a.score, a.p))
if len(pinfos) > MAX_CANDIDATE_QUEUE:
    pinfos = pinfos[:MAX_CANDIDATE_QUEUE]
used_mods: List[int] = []
residues_list: List[List[int]] = []
success = False
ctx_cache: Dict[int, NTTContext] = {}
for pi in pinfos:
    MOD = pi.p
    PR = find_primitive_root_pollard(MOD)
    if PR == 0:
        PR = 3
    if MOD not in ctx_cache:
        ctx_cache[MOD] = NTTContext(MOD, PR)
    ctx = ctx_cache[MOD]
    xs_mod = [0] * n
    ys_mod = [0] * n
    bad = False
    for i in range(n):
        xn = int_mod(xs[i][0], MOD)
        xd = int_mod(xs[i][1], MOD)
        if xd == 0:
            print(f"denominator of x is 0 mod {MOD}", file=sys.stderr)
            bad = True; break
        inv_xd = pow(xd, MOD - 2, MOD)
        xs_mod[i] = (xn * inv_xd) % MOD
        yn = int_mod(ys[i][0], MOD)
        yd = int_mod(ys[i][1], MOD)
        if yd == 0:
            print(f"denominator of y is 0 mod {MOD}", file=sys.stderr)
            bad = True; break
        inv_yd = pow(yd, MOD - 2, MOD)
        ys_mod[i] = (yn * inv_yd) % MOD
    if bad:
        continue
    coeffs_mod = interpolate(MOD, PR, xs_mod, ys_mod, ctx)
    used_mods.append(MOD)
    residues_list.append(coeffs_mod)
    coeffs_big = crt_all(residues_list, used_mods)
    Mprod = 1
    for m in used_mods:
        Mprod *= m
    all_ok = True
    coeffs_rational: List[Tuple[int,int]] = [(0,1)] * n
    for k in range(n):
        A = coeffs_big[k]
        res = rational_reconstruct(A, Mprod)
        if not res:
            Aneg = A if A <= 0 else A - Mprod
            res = rational_reconstruct((Aneg % Mprod + Mprod) % Mprod, Mprod)
        if not res:
            all_ok = False
            break
        Pp, Qp = res
        if Qp < 0:
            Pp = -Pp; Qp = -Qp
        coeffs_rational[k] = (Pp, Qp)
    if all_ok:
        any_printed = False
        out = ""
        for deg in range(n - 1, -1, -1):
            p = coeffs_rational[deg][0]
            q = coeffs_rational[deg][1]
            if p == 0:
                continue
            negative = p < 0
            mag = -p if negative else p
            if not any_printed:
                if negative:
                    out += "- "
            else:
                out += " - " if negative else " + "
            if q == 1:
                mag_s = str(mag)
            else:
                mag_s = str(mag) + "/" + str(q)
            if deg == 0:
                out += mag_s
            else:
                mag_is_one = False
                if q == 1:
                    if mag == 1:
                        mag_is_one = True
                else:
                    if mag == q:
                        mag_is_one = True
                if mag_is_one:
                    out += "x"
                else:
                    out += mag_s + " x"
                if deg >= 2:
                    out += "^" + str(deg)
            any_printed = True
        if not any_printed:
            out = "0"
        print(out)
        success = True
        break
if not success:
    print("not success", file=sys.stderr)
