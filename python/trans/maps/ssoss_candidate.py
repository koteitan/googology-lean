"""A CANDIDATE value of SSOSS sequences from (0,0,2) up to below
P2 = (0,0,2,1,0,2,1,1). NOT PROVED.

This is a port of the conjectural evaluator of https://github.com/koteitan/ssosn
(`work/token_value.py`, `value(s)`, with the flags P1_ROOT_EXPERIMENT,
P1_V_BITS_EXPERIMENT and P2_V7_EXPERIMENT on; notes 2026-10-17.md, sections
43-44), with the modules it uses: `work/token_tree.py`, `work/token_base2.py`,
`work/v_bits43.py`, `work/v_bits44.py`, `conj.py`, `conj2.py`. Only the code
paths reachable with those three flags on are ported; the other experiment
flags of the source are off. Where the source gives up (`Unknown`), the port
raises DomainError.

In the source, the values are checked by bounded audits only (successor and
limit consistency on the standard forms up to a bounded length); nothing above
(0,0,2) is proved, in Lean or elsewhere. Below (0,0,2), the proved value is the
map `o` of maps/ssoss.py, and this candidate is not used there.

Values are ordinals in Veblen normal form (maps/veblen.py). `ssoss_candidate_to_exb`
writes them as extended Buchholz terms.

Differences from the source that do not change values:
- The CNF trees of `token_tree` keep only what the values depend on: the
  terms and the frames of copied W/D units. The origins are dropped.
- The source switches `token_tree.P2_V7_EXPERIMENT` on and off around calls,
  and its caches are shared between the two modes. Here the mode is an
  argument (`p2`), and the caches are kept per mode. On the 18,128 standard
  forms of [(0,0,2), P2) of length at most 16, the source gives the same
  values in any evaluation order.
- `p1_v_anchor` (the sup of P V[n] = P D^n 0, found by the source from four
  terms) is the constant e_(e_(e_0)) that the source computes.
"""

import re
from dataclasses import dataclass, replace
from functools import lru_cache

from . import ssoss, veblen
from .errors import DomainError
from .veblen import ZERO as OZERO, ONE as OONE, OMEGA, P, add, cmp, lt, nat, next_fp, succ, w


class Unknown(Exception):
    """The source evaluator has no value here."""


E0 = P(OONE, OZERO)
P2 = (0, 0, 2, 1, 0, 2, 1, 1)
LOW = (0, 0, 2)


# ============================================================ conj.py, conj2.py

def conj_units(y):
    """conj.units: the units of a 0/1 word, as strings."""
    s = ''.join(map(str, y))
    out = []
    i = 0
    while i < len(s):
        if s[i] == '0':
            out.append('0')
            i += 1
            continue
        m = re.match(r'1(01|1)*', s[i:])
        out.append(m.group(0))
        i += len(m.group(0))
    return out


def conj_T(b):
    return tuple(int(c) for c in re.sub(r'1(1*)', r'\1', b))


@lru_cache(maxsize=None)
def conj_v(y):
    """conj.v: the value of a 0/1 word."""
    r = OZERO
    for u in conj_units(y):
        r = add(r, OONE if u == '0' else w(add(OONE, conj_v(conj_T(u)))))
    return r


def units(y):
    """conj2.units: a 0 outside blocks, or a block (nonzero runs joined by single 0s)."""
    y = tuple(y)
    out = []
    i = 0
    n = len(y)
    while i < n:
        if y[i] == 0:
            out.append((0,))
            i += 1
            continue
        j = i
        while j < n and (y[j] != 0 or (j + 1 < n and y[j + 1] != 0 and j > i and y[j - 1] != 0)):
            j += 1
        out.append(y[i:j])
        i = j
    return out


def _runs(word):
    runs, cur = [], []
    for x in word:
        if x == 0:
            runs.append(tuple(cur))
            cur = []
        else:
            cur.append(x)
    runs.append(tuple(cur))
    return tuple(runs)


def _join(runs):
    out = []
    for k, r in enumerate(runs):
        if k:
            out.append(0)
        out += r
    return tuple(out)


def T(b):
    """conj2.T: in every run of nonzero entries, drop the first entry if the run is all 1s."""
    return _join(r[1:] if r and all(x == 1 for x in r) else r for r in _runs(b))


# ================================================================ token_base2.py

def base2_parse(block):
    """token_base2.parse: the bits of (2) F(bits), A = (0,1,2) -> 0, D = (0,2) -> 1."""
    block = tuple(block)
    if block[:1] != (2,):
        return None
    tail = block[1:]
    bits = []
    while tail:
        if tail[:3] == (0, 1, 2):
            bits.append(0)
            tail = tail[3:]
        elif tail[:2] == (0, 2):
            bits.append(1)
            tail = tail[2:]
        else:
            return None
    return tuple(bits)


# =================================================================== v_bits43.py

def bits43(copies):
    out = []
    for t in copies:
        if t == 'W':
            out.append(0)
        elif t == 'D':
            out.append(1)
        elif t == 'V':
            if out and out[-1] == 1:
                out[-1] = 2
            else:
                out.append(2)
        else:
            raise Unknown(('bits: token', t))
    return tuple(out)


def T2(u):
    runs = _runs(u)
    if not all(r and r[0] == 2 for r in runs):
        raise Unknown(('T2: run not led by 2', u))
    return _join(r[1:] for r in runs)


@lru_cache(maxsize=None)
def v2(y):
    r = OZERO
    for u in units(y):
        if u == (0,):
            r = add(r, OONE)
            continue
        if u == (2,):
            r = add(r, E0)
            continue
        t = T(u)
        if t == u:
            r = add(r, P(OONE, v2(T2(u))))
            continue
        r = add(r, w(add(OONE, v2(t))))
    return r


def rank43(copies):
    return v2(bits43(copies))


# =================================================================== v_bits44.py

def Tk(word, k):
    runs = _runs(tuple(word))
    if k < 2 or not all(run and run[0] == k for run in runs):
        raise Unknown(('Tk: run heads do not all equal k', k, tuple(word)))
    return _join(run[1:] for run in runs)


def Tstar_k(word, k):
    runs = _runs(tuple(word))
    if k < 2 or not runs or any(not run or run[0] < k for run in runs):
        raise Unknown(('Tstar_k: run head below k', k, tuple(word)))
    return _join(run[1:] if run[0] == k else run for run in runs)


@lru_cache(maxsize=None)
def v4(word):
    word = tuple(word)
    value = OZERO
    for unit in units(word):
        if unit == (0,):
            value = add(value, OONE)
            continue
        if unit == (2,):
            value = add(value, E0)
            continue
        smaller = T(unit)
        if smaller != unit:
            value = add(value, w(add(OONE, v4(smaller))))
            continue
        heads = tuple(run[0] if run else None for run in _runs(unit))
        if not heads or any(head is None or head < 2 for head in heads):
            raise Unknown(('v4: self-reference with mixed/unsupported run heads', unit))
        k = min(heads)
        reduced = Tk(unit, k) if all(head == k for head in heads) else Tstar_k(unit, k)
        value = add(value, P(nat(k - 1), v4(reduced)))
    return value


def bits6(tokens):
    out = []
    for token in tokens:
        if token == 'W':
            out.append(0)
        elif token == 'D':
            out.append(1)
        elif token == 'V':
            if not out:
                out.append(('R', 2))
            elif isinstance(out[-1], tuple):
                out[-1] = ('R', out[-1][1] + 1)
            elif out[-1] >= 1:
                out[-1] += 1
            else:
                out.append(2)
        else:
            raise Unknown(('bits6: unsupported token', token))
    return tuple(out)


def _decode_bits6(word):
    digits = []
    root = None
    for i, item in enumerate(word):
        if isinstance(item, tuple):
            if i != 0 or root is not None:
                raise Unknown(('v6: misplaced root marker', word))
            root = item[1]
            digits.append(item[1])
        else:
            digits.append(item)
    return tuple(digits), root


def v7(tokens):
    """The root value: the marked root seed plus the v4 value of its tail."""
    digits, root = _decode_bits6(bits6(tuple(tokens)))
    if root is None:
        return v4(digits)
    seed = P(nat(root), OZERO)
    if len(digits) == 1:
        return seed
    us = units(digits)
    if us and us[0] == (root,):
        digits = digits[1:]
    return add(seed, v4(digits))


def B7(tokens):
    """The block value B(r) = phi(1, phi(1, w^r)) for the v7 root rank r."""
    return P(OONE, P(OONE, w(v7(tuple(tokens)))))


# ================================================================= token_tree.py
# A CNF tree is a tuple of Principal; its ordinal is the tuple of ('p', a, b).

@dataclass(frozen=True)
class Frame:
    copy: tuple
    covered_depth: int
    rank: object = None          # a tree, or None


@dataclass(frozen=True)
class Principal:
    index: tuple
    argument: tuple
    frame: object = None         # a Frame, or None


@lru_cache(maxsize=None)
def ordinal(tree):
    return tuple(('p', ordinal(t.index), ordinal(t.argument)) for t in tree)


TZERO = ()


def phi(a, b, frame=None):
    if len(b) == 1 and cmp(ordinal(b[0].index), ordinal(a)) > 0:
        return b
    return (Principal(a, b, frame),)


def power(b, frame=None):
    return phi(TZERO, b, frame)


def one():
    return power(TZERO)


def natural(n):
    return (Principal(TZERO, TZERO),) * n


def plus(a, b):
    if not b:
        return a
    head = ordinal((b[0],))
    k = len(a)
    while k and cmp(ordinal((a[k - 1],)), head) < 0:
        k -= 1
    return a[:k] + b


def successor(a):
    return plus(a, one())


def omega():
    return power(one())


def epsilon(b, frame=None):
    return phi(one(), b, frame)


def tower(seed, height, frame=None):
    for _ in range(height):
        seed = power(seed, frame)
    return seed


def from_ordinal(x):
    return tuple(Principal(from_ordinal(a), from_ordinal(b)) for _, a, b in x)


def next_fixed(level, x):
    base = phi(level, TZERO)
    if cmp(ordinal(x), ordinal(base)) < 0:
        return base
    term = x[0]
    order = cmp(ordinal(term.index), ordinal(level))
    if order == 0:
        return phi(level, successor(term.argument))
    if order > 0:
        return phi(level, successor(x))
    return next_fixed(level, term.argument)


def _exponent(term):
    return term.argument if not term.index else (term,)


def bump(tree, depth, amount, requested=None):
    """Walk CNF nodes, retaining the frame at a freshly opened WD term."""
    if requested is None:
        requested = depth
    if depth == 0:
        return plus(tree, amount)
    if not tree:
        raise Unknown('empty tree at bumped depth')
    term = tree[-1]
    pre = tree[:-1]
    frame = term.frame
    if frame is not None and 'D' in frame.copy and requested > frame.covered_depth:
        promoted = replace(frame, covered_depth=requested)
        seed = plus(frame.rank if frame.rank is not None else omega(), amount)
        return plus(pre, tower(seed, depth, promoted))
    exponent = _exponent(term)
    if not exponent:
        n = 0
        while n < len(tree) and ordinal((tree[-1 - n],)) == OONE:
            n += 1
        seed = plus(natural(n), amount)
        return plus(tree[:-n], tower(seed, depth, frame))    # tree[:-0] == (), as in the source
    changed = bump(exponent, depth - 1, amount, requested)
    return plus(pre, power(changed, frame))


def tree_epsilon_iteration(tree, depth, iterated, amount):
    term = tree[-1]
    pre = tree[:-1]
    if depth:
        exponent = _exponent(term)
        if not exponent:
            raise Unknown('epsilon beyond opened tree')
        return plus(pre, power(tree_epsilon_iteration(exponent, depth - 1, iterated, amount)))
    fixed = next_fixed(one(), (term,))
    q = fixed[0].argument
    if iterated:
        q = plus(q, amount)
    return plus(pre, epsilon(q))


def A(k):
    return (0, 1, 2) + (0, 2) * k


W_RAW = A(0) + (1,)
BOUNDARY = (2, 1, 0, 2)
OPS = ('W', 'D', 'V')


def tree_parse(tail, allow_d, p2):
    tail = tuple(tail)
    out = []
    while tail:
        if allow_d and tail[:3] == (0, 2, 1):
            out.append('V')
            tail = tail[3:]
            continue
        if allow_d and tail[:2] == (0, 2):
            out.append('D')
            tail = tail[2:]
            continue
        if allow_d and p2 and tail[:1] == (0,) and tail[:3] != A(0):
            j = 1
            while j < len(tail) and tail[j] == 1:
                j += 1
            if j > 1:
                out.append('L' + str(j - 1))
                tail = tail[j:]
            else:
                out.append('A0')
                tail = tail[1:]
            continue
        if tail[:3] != A(0):
            raise Unknown(('tree non-token suffix', tail))
        size, k = 3, 0
        while tail[size:size + 2] == (0, 2):
            size += 2
            k += 1
        if tail[size:size + 1] == (1,):
            out.append('W' if k == 0 else 'E' + str(k))
            size += 1
        else:
            out.append('A' + str(k))
        tail = tail[size:]
    return tuple(out)


def base_index(j):
    return epsilon(TZERO if j == 0 else power(natural(j)))


@lru_cache(maxsize=None)
def binary_index(bits):
    """The binary CNF tree of a 0/1 word: the tree of conj.v (no frames)."""
    return from_ordinal(conj_v(tuple(bits)))


def copy_rank(copies, p2):
    """W/D copy words use the binary rank; words with V use v7 (P2 mode) or v_bits43."""
    if p2 and 'V' in copies:
        return from_ordinal(v7(tuple(copies)))
    if 'V' in copies:
        return from_ordinal(rank43(tuple(copies)))
    return binary_index(tuple(0 if t == 'W' else 1 for t in copies))


def fold(tokens, boundary, general, p2):
    tokens = tuple(tokens)
    j = 0
    if general:
        while j < len(tokens) and tokens[j] in OPS:
            j += 1
    elif not boundary:
        while j < len(tokens) and tokens[j] == 'W':
            j += 1
    root_copy = ('W',) + tokens[:j] if general else ('W', 'D') if boundary else ('W',) * (j + 1)
    if general:
        rank = copy_rank(tokens[:j], p2)
        base = epsilon(power(rank)) if j else epsilon(TZERO)
        offset = copy_rank(root_copy, p2)
    elif boundary:
        base = epsilon(power(omega()))
        offset = omega()
    else:
        base = base_index(j)
        offset = natural(j + 1)
    value = base
    fresh, active_depth, i = True, 0, j
    while i < len(tokens):
        token = tokens[i]
        if token in OPS:
            raise Unknown(('tree unattached operator', token))
        i += 1
        m = 0
        while i < len(tokens) and tokens[i] == 'W':
            i += 1
            m += 1
        copies = ('W',) * m
        rank_limit = i < len(tokens) and tokens[i] == 'D'
        if rank_limit:
            if not m and not (general and token.startswith('E')):
                raise Unknown('tree D without iteration')
            copies += ('D',)
            i += 1
        if general:
            while i < len(tokens) and tokens[i] in OPS:
                copies += (tokens[i],)
                i += 1
        k = int(token[1:]) if token.startswith(('A', 'E')) else 0
        rank = copy_rank(copies, p2) if general else None
        amount = power(rank if general else omega() if rank_limit else natural(m))
        iterated = bool(copies) if general else m != 0
        frame = Frame(copies, k, rank) if iterated and token.startswith('A') else None
        if frame:
            amount = tuple(replace(t, frame=frame) for t in amount)
        if token.startswith('A'):
            if k == 0:
                value = plus(value, amount)
            elif fresh:
                value = plus(base, tower(plus(offset, amount), k, frame))
            else:
                value = bump(value, k, amount)
            active_depth = k
        elif token.startswith('L') and p2:
            # L_k = 0 1^k keeps its binary index; a following copy adds its amount.
            value = plus(value, binary_index((0,) + (1,) * int(token[1:])))
            if copies or rank_limit:
                value = plus(value, amount)
        elif token == 'E1':
            if p2 and general and fresh and iterated:
                seed_eps = next_fp(OONE, ordinal(offset))
                if len(seed_eps) != 1 or cmp(seed_eps[0][1], OONE):
                    raise Unknown('P2 E copy seed is not one epsilon term')
                value = plus(base, epsilon(plus(from_ordinal(seed_eps[0][2]), amount)))
            elif fresh and general and not iterated and not lt(ordinal(offset), E0):
                value = plus(base, from_ordinal(next_fp(OONE, ordinal(offset))))
            elif fresh:
                value = plus(base, epsilon(amount if iterated else TZERO))
            else:
                value = tree_epsilon_iteration(value, active_depth, iterated, amount)
        else:
            raise Unknown(('tree unsupported token', token))
        fresh = False
    return value


def known_block_tree(u, p2):
    binary = base2_parse(u)
    if binary is not None:
        return epsilon(binary_index(binary))
    if u == BOUNDARY:
        return epsilon(epsilon(power(omega())))
    if u[:len(BOUNDARY)] == BOUNDARY:
        return epsilon(fold(tree_parse(u[len(BOUNDARY):], True, p2), True, False, p2))
    if u[:2] == (2, 1):
        return epsilon(fold(tree_parse(u[2:], False, p2), False, False, p2))
    raise Unknown(('tree unsupported base', u))


@lru_cache(maxsize=None)
def block_tree(u, p2):
    if p2 and u[:5] == (2, 1, 0, 2, 1):
        return epsilon(fold(tree_parse(u[2:], True, p2), False, True, p2))
    try:
        return known_block_tree(u, p2)
    except Unknown:
        if u[:2] == (2, 1):
            return epsilon(fold(tree_parse(u[2:], True, p2), False, True, p2))
        raise


@lru_cache(maxsize=None)
def body_tree(body, p2):
    result = TZERO
    for unit in units(body):
        if unit == (0,):
            x = one()
        elif unit == (2,):
            x = epsilon(TZERO)
        else:
            t = T(unit)
            x = block_tree(unit, p2) if t == unit else power(plus(one(), body_tree(t, p2)))
        result = plus(result, x)
    return result


@lru_cache(maxsize=None)
def value_tree(s, p2):
    if s[:2] != (0, 0) or max(s, default=0) > 2:
        raise Unknown('tree outside 0/1/2 range')
    if len(s) > 2 and s[-1] == 0:
        return successor(value_tree(s[:-1], p2))
    return plus(natural(2), body_tree(s[2:], p2))


# ================================================================ token_value.py

def leading_w_index(exponent):
    """index(W^j) = e_(w^j) for j >= 1; continuous at exponent = w."""
    return P(OONE, w(exponent))


def parse_tail(tail):
    tail = tuple(tail)
    out = []
    i = 0
    while i < len(tail):
        if tail[i:i + 3] != (0, 1, 2):
            raise Unknown(('non-token suffix', tail[i:]))
        j = i + 3
        k = 0
        while tail[j:j + 2] == (0, 2):
            j += 2
            k += 1
        if tail[j:j + 1] == (1,):
            out.append('W' if k == 0 else 'E' + str(k))
            j += 1
        else:
            out.append('A' + str(k))
        i = j
    return tuple(out)


def bump_last(index, depth, amount):
    if depth == 0:
        return add(index, amount)
    if not index:
        raise Unknown('empty exponent')
    t = index[-1]
    exponent = t[2] if t[1] == OZERO else (t,)
    if not exponent:
        n = 0
        while n < len(index) and index[-1 - n] == OONE[0]:
            n += 1
        seed = add(nat(n), amount)
        for _ in range(depth):
            seed = w(seed)
        return add(index[:-n], seed)          # index[:-0] == (), as in the source
    changed = bump_last(exponent, depth - 1, amount)
    return add(index[:-1], w(changed))


def epsilon_iteration(value, depth, m):
    """Iterate the next-epsilon operation at the active depth."""
    if depth:
        t = value[-1]
        exponent = t[2] if t[1] == OZERO else (t,)
        if not exponent:
            raise Unknown('epsilon depth exceeds active tower')
        return add(value[:-1], w(epsilon_iteration(exponent, depth - 1, m)))
    t = value[-1]
    q = next_fp(OONE, (t,))[0][2]
    if m:
        q = add(q, w(nat(m)))
    return add(value[:-1], P(OONE, q))


@lru_cache(maxsize=None)
def index(tokens):
    j = 0
    while j < len(tokens) and tokens[j] == 'W':
        j += 1
    base = E0 if j == 0 else leading_w_index(nat(j))
    value = base
    fresh = True
    i = j
    active_depth = 0
    while i < len(tokens):
        token = tokens[i]
        if token == 'W':
            raise Unknown('unattached W')
        i += 1
        m = 0
        while i < len(tokens) and tokens[i] == 'W':
            m += 1
            i += 1
        amount = w(nat(m))
        k = int(token[1:])
        if token[0] == 'A':
            if k == 0:
                value = add(value, amount)
            elif fresh:
                seed = nat(j + 2) if m == 0 else amount
                for _ in range(k):
                    seed = w(seed)
                value = add(base, seed)
            else:
                value = bump_last(value, k, amount)
            active_depth = k
        elif token == 'E1':
            if fresh:
                value = add(base, P(OONE, OZERO if m == 0 else amount))
            else:
                value = epsilon_iteration(value, active_depth, m)
        else:
            raise Unknown(('unimplemented token', token))
        fresh = False
    return value


# The sup of P V[n] = P D^n 0 (P = (0,0,2,1,0,2)), as the source finds it from
# the terms n = 1..4: e_(e_(e_0)).
P1_V_ANCHOR = P(OONE, P(OONE, E0))


@lru_cache(maxsize=None)
def parse_p2_v7_copies(raw):
    """The unique W/D/V parse following the (2,1) prefix of a P1-root block."""
    pieces = (('W', W_RAW), ('D', (0, 2)), ('V', (0, 2, 1)))

    @lru_cache(maxsize=None)
    def go(i):
        if i == len(raw):
            return ((),)
        out = []
        for token, unit in pieces:
            if raw[i:i + len(unit)] == unit:
                out.extend((token,) + tail for tail in go(i + len(unit)))
        return tuple(dict.fromkeys(out))

    forms = go(0)
    if len(forms) != 1:
        raise Unknown(('P2 V7 token parse is not unique', raw))
    return forms[0]


@lru_cache(maxsize=None)
def block_value(u):
    if u[:5] == (2, 1, 0, 2, 1):
        try:
            return B7(parse_p2_v7_copies(u[2:]))
        except Unknown:
            try:
                return ordinal(block_tree(u, True))
            except Unknown:
                pass
    if u == (2, 1, 0, 2, 0, 2, 1):
        return P1_V_ANCHOR
    if u[:7] == (2, 1, 0, 2, 0, 2, 1):
        try:
            return ordinal(block_tree(u, False))
        except Unknown:
            pass
    binary = base2_parse(u)
    if binary is not None:
        return P(OONE, conj_v(binary))
    boundary = BOUNDARY
    if u == boundary + A(1):
        # L_A copies W D A0: increments w^w*(n-1)+1 with supremum w^(w+1).
        alpha = block_value(boundary)[0][2]
        return P(OONE, add(alpha, w(succ(OMEGA))))
    # Relative tails: A0 W^m adds w^m to the epsilon index of an independent base.
    base = u
    amounts = []
    while True:
        if base[-9:] == A(0) + W_RAW + (0, 2):
            base = base[:-9]
            amounts.append(w(OMEGA))
            continue
        rest = base
        m = 0
        while rest[-4:] == W_RAW:
            rest = rest[:-4]
            m += 1
        if rest[-3:] != A(0):
            break
        base = rest[:-3]
        amounts.append(w(nat(m)))
    if amounts and units(base) == [base] and T(base) == base:
        x = block_value(base)
        if len(x) == 1 and x[0][1] == OONE:
            i = x[0][2]
            for amount in reversed(amounts):
                i = add(i, amount)
            return P(OONE, i)
    if u[:2] != (2, 1):
        raise Unknown(('unrecognized self-reference', u))
    if u == (2, 1, 0, 2):
        return P(OONE, leading_w_index(OMEGA))
    return P(OONE, index(parse_tail(u[2:])))


@lru_cache(maxsize=None)
def body_value(body):
    value = OZERO
    for unit in units(body):
        if unit == (0,):
            x = OONE
        elif unit == (2,):
            x = E0
        else:
            t = T(unit)
            x = block_value(unit) if t == unit else w(add(OONE, body_value(t)))
        value = add(value, x)
    return value


ROOT = (0, 0, 2, 1, 0, 2)


def p1_root_candidate(s):
    if s[:len(ROOT)] != ROOT:
        raise Unknown('outside P root experiment')
    if s >= P2:
        raise Unknown('at or above P2: outside root experiments')
    if s == ROOT + (0, 2, 1):
        return B7(('V',))
    if s == ROOT + (0, 2, 0, 1):
        return w(succ(value(ROOT + (0, 2))))
    if s == ROOT + (0, 2, 1, 0, 1):
        return w(succ(value(ROOT + (0, 2, 1))))
    return ordinal(value_tree(s, True))


@lru_cache(maxsize=None)
def value(s):
    """The candidate value of s, a Veblen normal form (token_value.value)."""
    s = tuple(s)
    if s[:2] != (0, 0) or max(s, default=0) > 2:
        raise Unknown('outside 0/1/2 range')
    if len(s) > 2 and s[-1] == 0:
        return succ(value(s[:-1]))
    try:
        return add(nat(2), body_value(s[2:]))
    except Unknown:
        return p1_root_candidate(s)


# ======================================================================= the map

TOP = (0, 0, 3)


def is_standard(s):
    """The greedy descent of the source (`work/std.py`), started at (0,0,3).

    From T = (0,0,3): if T ends in 0, drop it; else go to the least
    T[n] = G B^n that is >= s. s is standard iff the descent reaches s. This
    decides standardness only under two properties that the source checks by
    bounded enumeration and does not prove: below a standard T, every standard
    form is <= some T[n] ("no gaps"), and the lexicographic order of standard
    forms is the order of their values.
    """
    s = tuple(s)
    t = TOP
    while True:
        if t == s:
            return True
        if t < s or not t:
            return False
        if t[-1] == 0:
            t = t[:-1]
            continue
        c = ssoss.cut(t)
        g, b = t[:c], t[c:-1] + (t[-1] - 1,)
        n = len(s) // len(b) + 2
        if (g + b * n)[:len(s)] < s:             # s is at or above every term
            return False
        n = 1
        x = g + b
        while x < s:
            n += 1
            x = g + b * n
        t = x


def candidate_value(s):
    """The candidate value of a sequence s with (0,0,2) <= s < P2, checked as above."""
    s = tuple(s)
    if s[:2] != (0, 0) or any(x > 2 for x in s):
        raise DomainError('o?: not of the form (0,0) followed by entries 0, 1, 2')
    if s < LOW:
        raise DomainError('o?: below (0,0,2), where the proved map o gives the value')
    if s >= P2:
        raise DomainError('o?: not below P2 = (0,0,2,1,0,2,1,1)')
    if not is_standard(s):
        raise DomainError('o?: not a standard form (by the greedy descent from (0,0,3))')
    try:
        return value(s)
    except Unknown as e:
        raise DomainError('o?: the candidate evaluator has no value here (%s)' % (e.args[0],))
    except (IndexError, RecursionError) as e:
        raise DomainError('o?: the candidate evaluator failed (%s)' % e)


def ssoss_candidate_to_exb(s):
    """The candidate value, as an extended Buchholz term. NOT PROVED."""
    return veblen.to_exb(candidate_value(s))
