"""Pair sequences to extended Buchholz terms: `pairTerm` and `pairOrdTerm`.

Lean sources (this repo):
- pairTerm     Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean:184
               pairTerm M = toTerm (PSS.Trans M)
- pairOrdTerm  Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean:344
               pairOrdTerm l = if l = [] then nil else addNF t1 (pairTerm l)
- toTerm, sub  Googology/Trans/BMS/ExBuchholz/PSS/Terms.lean:50, :123
- addNF        Googology/Notation/ExBuchholz/Onto.lean:128
- Term.cmp     Googology/Notation/ExBuchholz/Basic.lean:45

`PSS.Trans` and everything it uses are from pss-proof
(https://github.com/koteitan/pss-proof). Each function below cites its Lean
definition there:
- Defs.lean     https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Defs.lean
- Mono.lean     https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Mono.lean
- Adm.lean      https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Adm.lean
- Red.lean      https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Red.lean
- Scb.lean      https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Scb.lean
- Trans.lean    https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Trans.lean
- Buchholz-1986-2.1.lean, -2.2.lean, -3.2.lean
  https://github.com/koteitan/pss-proof/blob/main/lean/Buchholz-1986/Buchholz-1986-2.1.lean
  (and -2.2.lean, -3.2.lean in the same directory)

The port is literal, fuel arguments included. Nat subtraction is truncated
(`nsub`). A pair sequence `PS` is a tuple of 2-tuples; pss-proof's Buchholz
terms are kept as their own type `BT` / `BP` below, and `to_term` turns them
into the terms of notation/exb.py.

pss-proof has no computable test for "standard pair sequence": `STPS`
(https://github.com/koteitan/pss-proof/blob/main/lean/PSS/Standard.lean) and
`CTPS` (https://github.com/koteitan/pss-proof/blob/main/bijectivity/lean/Bijectivity/Defs.lean) are an
inductive predicate and a Prop built on it. So there is no `is_standard` here.
"""

import sys
from collections import namedtuple
from functools import lru_cache

from notation import exb

sys.setrecursionlimit(max(sys.getrecursionlimit(), 20000))

# ---------------------------------------------------------------- ℕ∞ and Nat

TOP = float('inf')          # ⊤ : ℕ∞ (the subscript ω of D_ω)


def nsub(a, b):
    """Nat subtraction, truncated at 0."""
    return a - b if a > b else 0


# ---------------------------------------------------------------- BT
# Buchholz-1986-2.1.lean: `inductive BT | trm : List BP → BT`,
# `inductive BP | db : ℕ∞ → BT → BP`.

BT = namedtuple('BT', 'ps')       # .trm ps,  ps a tuple of BP
BP = namedtuple('BP', 'u a')      # .db u a

BZERO = BT(())                    # Buchholz-1986-2.1.lean `BZero := .trm []`


def dprin(v, a):
    """Buchholz-1986-2.1.lean `Dprin v a := .trm [.db v a]`."""
    return BT((BP(v, a),))


def untrm(t):
    """Buchholz-1986-2.1.lean `untrm`."""
    return t.ps


def PB(t):
    """Buchholz-1986-2.1.lean `PB t := (untrm t).map (fun p => .trm [p])`."""
    return tuple(BT((p,)) for p in untrm(t))


def SigmaB(ts):
    """Buchholz-1986-2.1.lean `SigmaB ts := .trm (ts.flatMap untrm)`."""
    return BT(tuple(p for t in ts for p in untrm(t)))


def addBT(a, b):
    """Buchholz-1986-3.2.lean `addBT (.trm as) (.trm bs) := .trm (as ++ bs)`."""
    return BT(a.ps + b.ps)


def dfree_BT(t):
    """Buchholz-1986-2.2.lean `dfree_BT`."""
    return dfree_BPList(t.ps)


def dfree_BP(p):
    """Buchholz-1986-2.2.lean `dfree_BP (.db v b) := v != ⊤ && dfree_BT b`."""
    return p.u != TOP and dfree_BT(p.a)


def dfree_BPList(ps):
    """Buchholz-1986-2.2.lean `dfree_BPList`."""
    return all(dfree_BP(p) for p in ps)


# ---------------------------------------------------------------- Defs.lean

def Lng(M):
    """Defs.lean `Lng M := M.length`."""
    return len(M)


def entry(M, i, j):
    """Defs.lean `entry M i j`: `M[j]?`, component `i`, `0` out of range."""
    if j >= len(M):
        return 0
    return M[j][0] if i == 0 else M[j][1]


def range2(a, n):
    """Lean `List.range' a n` = [a, a+1, ..., a+n-1]."""
    return range(a, a + n)


@lru_cache(maxsize=None)
def nextrel0(M, j0, j1):
    """Defs.lean `nextrel0`."""
    L = Lng(M)
    return (j0 < L and j1 < L and j0 < j1
            and entry(M, 0, j0) < entry(M, 0, j1)
            and all((not (j0 < j)) or entry(M, 0, j1) <= entry(M, 0, j)
                    for j in range(j1)))


@lru_cache(maxsize=None)
def le0Aux(M, fuel, j0, j1):
    """Defs.lean `le0Aux`."""
    if fuel == 0:
        return j0 == j1
    return j0 == j1 or any(nextrel0(M, j, j1) and le0Aux(M, fuel - 1, j0, j)
                           for j in range(j1))


def le0(M, j0, j1):
    """Defs.lean `le0`."""
    return j0 < Lng(M) and j1 < Lng(M) and le0Aux(M, Lng(M), j0, j1)


@lru_cache(maxsize=None)
def nextrel1(M, j0, j1):
    """Defs.lean `nextrel1`."""
    L = Lng(M)
    return (j0 < L and j1 < L and j0 < j1
            and entry(M, 1, j0) < entry(M, 1, j1)
            and le0(M, j0, j1)
            and all((not (j0 < j and le0(M, j, j1))) or entry(M, 1, j1) <= entry(M, 1, j)
                    for j in range(L)))


@lru_cache(maxsize=None)
def le1Aux(M, fuel, j0, j1):
    """Defs.lean `le1Aux`."""
    if fuel == 0:
        return j0 == j1
    return j0 == j1 or any(nextrel1(M, j, j1) and le1Aux(M, fuel - 1, j0, j)
                           for j in range(j1))


def le1(M, j0, j1):
    """Defs.lean `le1`."""
    return j0 < Lng(M) and j1 < Lng(M) and le1Aux(M, Lng(M), j0, j1)


def nextR(M, i, j0, j1):
    """Defs.lean `nextR`."""
    return nextrel0(M, j0, j1) if i == 0 else nextrel1(M, j0, j1)


def leR(M, i, j0, j1):
    """Defs.lean `leR`."""
    return le0(M, j0, j1) if i == 0 else le1(M, j0, j1)


def Pred(M):
    """Defs.lean `Pred M := if Lng M ≤ 1 then M else M.dropLast`."""
    return M if Lng(M) <= 1 else M[:-1]


def idx1(M, j1):
    """Defs.lean `idx1`."""
    return 1 if 0 < entry(M, 1, j1) else 0


@lru_cache(maxsize=None)
def parents(M, i, j1):
    """Defs.lean `parents`."""
    return tuple(j0 for j0 in range(Lng(M)) if nextR(M, i, j0, j1))


def hasParent(M, i, j1):
    """Defs.lean `hasParent`."""
    return len(parents(M, i, j1)) == 1


def parent(M, i, j1):
    """Defs.lean `parent := (parents M i j1).headD 0`."""
    ps = parents(M, i, j1)
    return ps[0] if ps else 0


def seg(M, a, b):
    """Defs.lean `seg M a b`."""
    return tuple((entry(M, 0, j), entry(M, 1, j)) for j in range2(a, nsub(b + 1, a)))


def oper(M, n):
    """Defs.lean `oper M n`, the fundamental sequence M[n]."""
    j1 = nsub(Lng(M), 1)
    if j1 == 0:
        return M
    if entry(M, 0, j1) == 0 and entry(M, 1, j1) == 0:
        return Pred(M)
    i1 = idx1(M, j1)
    if not hasParent(M, i1, j1):
        return Pred(M)
    j0 = parent(M, i1, j1)
    d0 = nsub(entry(M, 0, j1), entry(M, 0, j0)) if 0 < i1 else 0
    d1 = nsub(entry(M, 1, j1), entry(M, 1, j0)) if 1 < i1 else 0
    return M[:j0] + tuple((entry(M, 0, j) + k * d0, entry(M, 1, j) + k * d1)
                          for k in range(n) for j in range2(j0, nsub(j1, j0)))


def IncrFirst(M):
    """Defs.lean `IncrFirst`."""
    return tuple((p[0] + 1, p[1]) for p in M)


# ---------------------------------------------------------------- Mono.lean

def zeroT(M):
    """Mono.lean `zeroT`."""
    return Lng(M) == 1 and entry(M, 1, 0) == 0


def monoT(M):
    """Mono.lean `monoT`."""
    return (not zeroT(M)) and leR(M, 0, 0, nsub(Lng(M), 1))


def multiT(M):
    """Mono.lean `multiT`."""
    return (not zeroT(M)) and not monoT(M)


def Pcut(M):
    """Mono.lean `Pcut`."""
    L = Lng(M)
    for j in range(L):
        if 0 < j and j <= nsub(L, 1) and leR(M, 0, j, nsub(L, 1)):
            return j
    return nsub(L, 1)


def PAux(fuel, M):
    """Mono.lean `PAux`."""
    if fuel == 0:
        return (M,)
    if multiT(M) and 1 < Lng(M):
        c = Pcut(M)
        return PAux(fuel - 1, M[:c]) + (M[c:],)
    return (M,)


@lru_cache(maxsize=None)
def P(M):
    """Mono.lean `P M := PAux (Lng M) M`."""
    return PAux(Lng(M), M)


def IdxSum(Q):
    """Mono.lean `IdxSum`."""
    return tuple(sum(Lng(x) for x in Q[:J]) for J in range(len(Q) + 1))


@lru_cache(maxsize=None)
def TrMax(M):
    """Mono.lean `TrMax`."""
    for j in range(Lng(M)):
        if not nextR(M, 1, j, j + 1):
            return j
    return nsub(Lng(M), 1)


def Br(M):
    """Mono.lean `Br`."""
    if TrMax(M) == nsub(Lng(M), 1):
        return ()
    return P(seg(M, TrMax(M) + 1, nsub(Lng(M), 1)))


def FirstNodes(M):
    """Mono.lean `FirstNodes`."""
    return tuple(TrMax(M) + 1 + x for x in IdxSum(Br(M)))


def Joints(M):
    """Mono.lean `Joints`."""
    fn = FirstNodes(M)
    return tuple(parent(M, 0, fn[J] if J < len(fn) else 0) for J in range(len(Br(M))))


# ---------------------------------------------------------------- Adm.lean

def nadm(M, j):
    """Adm.lean `nadm`."""
    return Lng(M) < j or (nextR(M, 1, nsub(j, 1), j) and nextR(M, 1, j, j + 1))


def adm(M, j):
    """Adm.lean `adm`."""
    return not nadm(M, j)


def Adm(M, j):
    """Adm.lean `Adm`: `j` if admissible, else the largest admissible `j' < j`, else 0."""
    if adm(M, j):
        return j
    for jj in reversed(range(j)):
        if adm(M, jj):
            return jj
    return 0


# ---------------------------------------------------------------- Red.lean

def diagSeq(a, b):
    """Red.lean `diagSeq a b = ((j,j))_(j=a)^b`."""
    return tuple((j, j) for j in range2(a, nsub(b + 1, a)))


def IncrFirstN(n, M):
    """Red.lean `IncrFirstN`."""
    for _ in range(n):
        M = IncrFirst(M)
    return M


def betaM(M):
    """Red.lean `betaM`."""
    return nsub(Lng(M), TrMax(M))


def coreReduce(M):
    """Red.lean `coreReduce`."""
    if entry(M, 1, 0) == 0:
        return tuple((nsub(entry(M, 0, j), entry(M, 0, 0)), entry(M, 1, j))
                     for j in range(Lng(M)))
    return diagSeq(0, nsub(entry(M, 1, 0), 1)) + IncrFirstN(entry(M, 1, 0), M)


def muMono(M):
    """Red.lean `muMono`."""
    if entry(M, 0, 0) == 0 and entry(M, 1, 0) == 0:
        return 2 * betaM(M)
    return 2 * betaM(coreReduce(M)) + 1


def nu(M):
    """Red.lean `nu`."""
    if multiT(M):
        return 1 + sum(muMono(Q) for Q in P(M))
    return muMono(M)


@lru_cache(maxsize=None)
def RedAux(fuel, M):
    """Red.lean `RedAux`."""
    if fuel == 0:
        return M
    fuel -= 1
    if zeroT(M):
        return ((0, 0),)
    if multiT(M):
        return tuple(x for Q in P(M) for x in RedAux(fuel, Q))
    j1 = nsub(Lng(M), 1)
    j1p = TrMax(M)
    m00 = entry(M, 0, 0)
    m10 = entry(M, 1, 0)
    if m00 == 0 and m10 == 0:
        if j1p == j1:
            return diagSeq(m10, m10 + j1)
        br, fns, jts = Br(M), FirstNodes(M), Joints(M)
        out = diagSeq(0, j1p)
        for J in range(len(br)):
            block = br[J]
            firstNode = fns[J] if J < len(fns) else 0
            joint = jts[J] if J < len(jts) else 0
            np_ = 0 if entry(block, 1, 0) == 0 else parent(M, 1, firstNode) + 1
            eJ = nsub(joint + 1, np_)
            NJ = ((m00 + joint + 1, m10 + np_),) + block[1:]
            out += IncrFirstN(eJ, RedAux(fuel, NJ))
        return out
    if m10 == 0:
        return RedAux(fuel, coreReduce(M))
    N = RedAux(fuel, coreReduce(M))
    jN = nsub(Lng(N), 1)
    S = seg(N, m10, jN)
    if m10 <= jN and monoT(S):
        return tuple((nsub(entry(N, 0, j), entry(N, 0, m10)) + entry(N, 1, m10), entry(N, 1, j))
                     for j in range2(m10, nsub(jN + 1, m10)))
    return M


def Red(M):
    """Red.lean `Red M := RedAux (nu M + 1) M`."""
    return RedAux(nu(M) + 1, M)


@lru_cache(maxsize=None)
def reduced(M):
    """Red.lean `reduced M := !M.isEmpty && (Red M == M)`."""
    return len(M) != 0 and Red(M) == M


# ---------------------------------------------------------------- Scb.lean
# Sym: 'lp' | 'cm' | 'rp' | 'zero' | ('d', u)   (Scb.lean `inductive Sym`)

LP, CM, RP, ZSYM = 'lp', 'cm', 'rp', 'zero'


def dsym(u):
    return ('d', u)


def is_dsym(x):
    return isinstance(x, tuple)


@lru_cache(maxsize=None)
def flatBT(t):
    """Scb.lean `flatBT`."""
    ps = t.ps
    if len(ps) == 0:
        return (ZSYM,)
    if len(ps) == 1:
        return flatBP(ps[0])
    return (LP,) + flatBP(ps[0]) + flatBPTail(ps[1:]) + (RP,)


def flatBP(p):
    """Scb.lean `flatBP (.db u a) := .dsym u :: flatBT a`."""
    return (dsym(p.u),) + flatBT(p.a)


def flatBPTail(ps):
    """Scb.lean `flatBPTail`."""
    out = ()
    for p in ps:
        out += (CM,) + flatBP(p)
    return out


# ---------------------------------------------------------------- Trans.lean

def parseBTAux(fuel, xs):
    """Trans.lean `parseBTAux`: one term from the front of `xs`, or None."""
    if fuel == 0 or len(xs) == 0:
        return None
    x, rest = xs[0], xs[1:]
    if x == ZSYM:
        return (BZERO, rest)
    if is_dsym(x):
        r = parseBTAux(fuel - 1, rest)
        if r is None:
            return None
        t, rest2 = r
        return (dprin(x[1], t), rest2)
    if x == LP:
        return parseBPSeqAux(fuel - 1, rest, ())
    return None


def parseBPAux(fuel, xs):
    """Trans.lean `parseBPAux`."""
    if fuel == 0:
        return None
    if len(xs) > 0 and is_dsym(xs[0]):
        r = parseBTAux(fuel - 1, xs[1:])
        if r is None:
            return None
        t, rest = r
        return (BP(xs[0][1], t), rest)
    return None


def parseBPSeqAux(fuel, xs, acc):
    """Trans.lean `parseBPSeqAux`."""
    if fuel == 0:
        return None
    r = parseBPAux(fuel - 1, xs)
    if r is None:
        return None
    p, rest = r
    if len(rest) > 0 and rest[0] == RP:
        return (BT(acc + (p,)), rest[1:])
    if len(rest) > 0 and rest[0] == CM:
        return parseBPSeqAux(fuel - 1, rest[1:], acc + (p,))
    return None


def unflatBT(xs):
    """Trans.lean `unflatBT`."""
    r = parseBTAux(len(xs) + 1, xs)
    if r is not None and r[1] == ():
        return r[0]
    return BZERO


def isPTBStr(xs):
    """Trans.lean `isPTBStr`."""
    r = parseBPAux(len(xs) + 1, xs)
    if r is not None and r[1] == ():
        return dfree_BP(r[0])
    return False


def scbContexts(t, c):
    """Trans.lean `scbContexts`: every (s, b) with flatBT t = s ++ c ++ b, left first."""
    f = flatBT(t)
    out = []
    for i in range(nsub(len(f), len(c)) + 1):
        s = f[:i]
        b = f[i + len(c):]
        if (f[i:][:len(c)] == c and (t == BZERO or isPTBStr(c))
                and all(x == RP for x in b)):
            out.append((s, b))
    return out


def replaceScb(t, c1, c2):
    """Trans.lean `replaceScb`."""
    ctx = scbContexts(t, flatBT(c1))
    if ctx:
        s, b = ctx[0]
        return unflatBT(s + flatBT(c2) + b)
    return BZERO


def lastIdx(M):
    """Trans.lean `lastIdx M := Lng M - 1`."""
    return nsub(Lng(M), 1)


def lastParent(M):
    """Trans.lean `lastParent M := parent M 0 (lastIdx M)`."""
    return parent(M, 0, lastIdx(M))


def transCondI(M):
    """Trans.lean `transCondI`."""
    return entry(M, 1, lastIdx(M)) == 0 and adm(M, lastParent(M))


def transCondII(M):
    """Trans.lean `transCondII`."""
    return entry(M, 1, lastIdx(M)) == 0 and not adm(M, lastParent(M))


def transCondIII(M):
    """Trans.lean `transCondIII`."""
    e = entry(M, 1, lastIdx(M))
    return 0 < e and e <= entry(M, 1, lastParent(M)) and adm(M, lastParent(M))


def transCondIV(M):
    """Trans.lean `transCondIV`."""
    e = entry(M, 1, lastIdx(M))
    return 0 < e and e <= entry(M, 1, lastParent(M)) and not adm(M, lastParent(M))


def transCondV(M):
    """Trans.lean `transCondV`."""
    e = entry(M, 1, lastIdx(M))
    return (0 < e and entry(M, 1, lastParent(M)) + 1 == e
            and lastParent(M) + 1 < lastIdx(M))


def transCondVI(M):
    """Trans.lean `transCondVI`."""
    e = entry(M, 1, lastIdx(M))
    return (0 < e and entry(M, 1, lastParent(M)) + 1 == e
            and lastParent(M) + 1 == lastIdx(M))


def bpHeadV(t):
    """Trans.lean `bpHeadV`: the subscript of the first principal term, else 0."""
    return t.ps[0].u if t.ps else 0


def bpHeadT(t):
    """Trans.lean `bpHeadT`: the argument of the first principal term, else 0."""
    return t.ps[0].a if t.ps else BZERO


def transC2Core(M, v, t2):
    """Trans.lean `transC2Core`."""
    j1 = lastIdx(M)
    jp = lastParent(M)
    if transCondI(M) or transCondIII(M) or transCondV(M):
        return dprin(v, addBT(t2, dprin(entry(M, 1, j1), BZERO)))
    if transCondVI(M):
        return dprin(v, dprin(entry(M, 1, j1), BZERO))
    if t2 == BZERO:
        return dprin(v, dprin(entry(M, 1, jp), dprin(entry(M, 1, j1), BZERO)))
    pt2 = PB(t2)
    J1 = nsub(len(pt2), 1)
    pJ = pt2[J1] if J1 < len(pt2) else BZERO
    leftDj0 = bpHeadV(pJ) == entry(M, 1, jp)
    t3 = SigmaB(pt2[:J1]) if leftDj0 else t2
    t4 = bpHeadT(pJ) if leftDj0 else t2
    return dprin(v, addBT(t3, dprin(entry(M, 1, jp),
                                    addBT(t4, dprin(entry(M, 1, j1), BZERO)))))


def transFuel(M):
    """Trans.lean `transFuel M := 8 * (nu M + 1) * (Lng M + 1) + 8`."""
    return 8 * (nu(M) + 1) * (Lng(M) + 1) + 8


@lru_cache(maxsize=None)
def TransAux(fuel, M):
    """Trans.lean `TransAux`."""
    if fuel == 0:
        return BZERO
    fuel -= 1
    if not reduced(M):
        return TransAux(fuel, Red(M))
    j1 = lastIdx(M)
    if j1 == 0:
        if (M[0] if M else (0, 0)) == (0, 0):
            return BZERO
        return dprin(entry(M, 1, 0), BZERO)
    if monoT(M):
        t1 = TransAux(fuel, Pred(M))
        if t1 == BZERO:
            return dprin(0, dprin(entry(M, 1, j1), BZERO))
        jp = lastParent(M)
        c1 = MarkAux(fuel, Pred(M), Adm(M, jp))
        c2 = transC2Core(M, bpHeadV(c1), bpHeadT(c1))
        return replaceScb(t1, c1, c2)
    ps = P(M)
    J1 = nsub(len(ps), 1)
    pJ = ps[J1] if J1 < len(ps) else ()
    j0 = nsub(j1, Lng(pJ)) + 1
    if pJ == ((0, 0),):
        return addBT(TransAux(fuel, seg(M, 0, nsub(j0, 1))), dprin(0, BZERO))
    return addBT(TransAux(fuel, seg(M, 0, nsub(j0, 1))), TransAux(fuel, pJ))


@lru_cache(maxsize=None)
def MarkAux(fuel, M, m):
    """Trans.lean `MarkAux`."""
    if fuel == 0:
        return BZERO
    fuel -= 1
    if not reduced(M):
        return MarkAux(fuel, Red(M), m)
    j1 = lastIdx(M)
    if j1 == 0:
        if (M[0] if M else (0, 0)) == (0, 0):
            return BZERO
        return dprin(entry(M, 1, 0), BZERO)
    if monoT(M):
        t1 = TransAux(fuel, Pred(M))
        if t1 == BZERO:
            if m == 0:
                return dprin(0, dprin(entry(M, 1, j1), BZERO))
            return dprin(entry(M, 1, j1), BZERO)
        jp = lastParent(M)
        c1 = MarkAux(fuel, Pred(M), Adm(M, jp))
        c2 = transC2Core(M, bpHeadV(c1), bpHeadT(c1))
        if m < j1:
            c0 = MarkAux(fuel, Pred(M), m)
            ctx = scbContexts(c0, flatBT(c1))
            if ctx:
                s, b = ctx[0]
                return unflatBT(s + flatBT(c2) + b)
            return dprin(entry(M, 1, j1), BZERO)
        return dprin(entry(M, 1, j1), BZERO)
    ps = P(M)
    J1 = nsub(len(ps), 1)
    pJ = ps[J1] if J1 < len(ps) else ()
    j0 = nsub(j1, Lng(pJ)) + 1
    if pJ == ((0, 0),):
        return dprin(0, BZERO)
    return MarkAux(fuel, pJ, nsub(m, j0))


def Trans(M):
    """Trans.lean `Trans M := TransAux (transFuel M) M`."""
    M = _ps(M)
    return TransAux(transFuel(M), M)


def Mark(M, m):
    """Trans.lean `Mark M m := MarkAux (transFuel M) M m`."""
    M = _ps(M)
    return MarkAux(transFuel(M), M, m)


def _ps(M):
    return tuple((int(p[0]), int(p[1])) for p in M)


# ---------------------------------------------------------------- to exb terms

def sub(u):
    """Terms.lean `sub`: the numeral n, or `tw` (= psi_0(1)) for ⊤."""
    return exb.OMEGA if u == TOP else exb.numeral(u)


def to_term(t):
    """Terms.lean `toTerm` / `toTermL`: D_u a + ... as psi_{sub u}(toTerm a) + ...."""
    return tuple((sub(p.u), to_term(p.a)) for p in t.ps)


def cmp(x, y):
    """Notation/ExBuchholz/Basic.lean `Term.cmp`: -1, 0, 1 for lt, eq, gt."""
    if not x:
        return 0 if not y else -1
    if not y:
        return 1
    (a, b), t = x[0], x[1:]
    (c, d), u = y[0], y[1:]
    return cmp(a, c) or cmp(b, d) or cmp(t, u)


def add_nf(x, y):
    """Notation/ExBuchholz/Onto.lean `addNF`."""
    if not x:
        return y
    if not y:
        return x
    if cmp(exb.psi(*x[0]), exb.psi(*y[0])) < 0:
        return y
    return (x[0],) + add_nf(x[1:], y)


# ---------------------------------------------------------------- public

def pair_term(m):
    """Rank.lean `pairTerm M := toTerm (PSS.Trans M)`."""
    return to_term(Trans(m))


def pair_ord_term(m):
    """Rank.lean `pairOrdTerm l := if l = [] then nil else addNF t1 (pairTerm l)`."""
    if len(m) == 0:
        return exb.ZERO
    return add_nf(exb.ONE, pair_term(m))
