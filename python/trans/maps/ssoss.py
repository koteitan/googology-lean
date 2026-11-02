"""Strong second-order searching sequences (SSOSS) below (0,0,2): the
expansion and the value `o`.

Ports of `Googology/Notation/SSOSS/`:

- `Def.lean`: `entry`, `suf`, `sp`, `p`, `mbp`, `fbp`, `breakAt`, `br`, `cut`,
  `good`, `bad`, `fs` (the expansion; `ssossSys.step a k = fs a (k + 1)`).
- `Tree.lean`, `Parse.lean`, `Flat.lean`: the units `U` (`z`, `b u`), `snocOne`,
  `parse`, `flat`, `encode`. A list of units is stored with the LAST unit first,
  as in Lean.
- `SequenceOrdinal.lean`, `Bridge.lean`: `o S = length S` for length below 2,
  else `treeOrdinal (parse (drop 2 S)) = 2 + vs (parse (drop 2 S))`, with
  `val z = 1`, `val (b u) = w^(1 + vs u)`.

The value is returned as an extended Buchholz term with every subscript 0: below
e0, psi_0(a) = w^a, so a Cantor normal form w^a1 + ... + w^ak (a1 >= ... >= ak)
is the term psi_0(a1) + ... + psi_0(ak).
"""

from notation import exb
from notation.exb_std import is_ot, lt
from .errors import DomainError

# ---------------------------------------------------------------- Def.lean


def entry(s, i):
    """One-based entry; 0 outside the sequence."""
    return s[i - 1] if 1 <= i <= len(s) else 0


def suf(s, i):
    return s[max(i - 1, 0):]


def sp(s, x):
    out = 1
    for i in range(x):
        if 1 <= i and suf(s, i) < suf(s, x):
            out = max(out, i)
    return out


def p(s, i):
    x = len(s)
    for _ in range(i):
        x = sp(s, x)
    return x


def mbp(s, x):
    n = len(s)
    if n <= x:
        return n
    m = n                          # mbp s n
    for y in range(n - 1, x - 1, -1):
        if entry(s, y) < entry(s, n) and suf(s, m + 1) < suf(s, y + 1):
            m = y
    return m


def fbp(s, i):
    return mbp(s, p(s, i))


def break_at(s, i):
    if suf(s, fbp(s, i) + 1) <= suf(s, fbp(s, i - 1) + 1):
        return True
    pi = p(s, i)
    return any(pi < j and entry(s, j) <= entry(s, pi) for j in range(fbp(s, i) + 1))


def br(s):
    for i in range(len(s) + 1):
        if 1 < i and break_at(s, i):
            return i
    return len(s)


def cut(s):
    return fbp(s, br(s))


def good(s):
    return s[:cut(s)]


def bad(s):
    return s[:-1][cut(s):] + (entry(s, len(s)) - 1,)


def fs(s, k):
    """Lean `Seq.fs`: the sequence part of the expansion with k copies of the bad part."""
    s = tuple(s)
    if not s:
        return ()
    if entry(s, len(s)) == 0:
        return s[:-1]
    return good(s) + bad(s) * k


def gen(n):
    """The generators (0,0) followed by n ones (System.lean, `gen`)."""
    return (0, 0) + (1,) * n

# ---------------------------------------------------- Tree / Parse / Flat

Z = ('z',)


def B(u):
    return ('b', tuple(u))


def snoc_one(t):
    t = tuple(t)
    if not t:
        return (B(()),)
    if t[0][0] == 'b':
        return (B(snoc_one(t[0][1])),) + t[1:]
    if len(t) == 1:                            # [z]
        return (B(()), Z)
    if t[1] == Z:                              # z :: z :: P
        return (B(()),) + t
    return (B((Z,) + t[1][1]),) + t[2:]       # z :: b u :: P


def parse(s):
    t = ()
    for n in s:
        t = (Z,) + t if n == 0 else snoc_one(t)
    return t


def raise_bits(s):
    out = [1]
    for n in s:
        out += [0, 1] if n == 0 else [1]
    return tuple(out)


def flat(t):
    out = ()
    for x in reversed(t):                      # the first unit is the last in the list
        out += (0,) if x == Z else raise_bits(flat(x[1]))
    return out


def encode(t):
    return (0, 0) + flat(t)

# ---------------------------------------------------------------- value


def add(x, y):
    """Ordinal sum of two Cantor normal forms written as exb terms with subscripts 0."""
    if not y:
        return x
    a = list(x)
    while a and lt((a[-1],), (y[0],)):
        a.pop()
    return tuple(a) + tuple(y)


def val(x):
    return exb.ONE if x == Z else exb.psi(exb.ZERO, add(exb.ONE, vs(x[1])))


def vs(t):
    out = exb.ZERO
    for x in reversed(t):                      # vs (x :: rest) = vs rest + val x
        out = add(out, val(x))
    return out


def o(s):
    """Lean `o`, as an exb term."""
    s = tuple(s)
    if len(s) < 2:
        return exb.numeral(len(s))
    return add(exb.numeral(2), vs(parse(s[2:])))


def ssoss_to_exb(s):
    """The value `o` of a sequence of the (0,0)-fragment.

    Lean proves its theorems on the standard forms (`Standard`, below (0,0,2)),
    which have no computable test in Lean. Only the conditions that give `o`
    its meaning are checked: every entry is 0 or 1 (`standard_binary`), and a
    sequence of length 2 or more starts with (0,0) (the (0,0)-fragment of
    `SequenceOrdinal.lean`; the shorter ones are the erased (), (0)).
    """
    s = tuple(s)
    if any(n > 1 for n in s):
        raise DomainError('o: an entry is not 0 or 1 (not below (0,0,2))')
    if len(s) >= 2 and s[:2] != (0, 0):
        raise DomainError('o: the sequence does not start with (0,0)')
    t = o(s)
    assert is_ot(t)
    return t


def standard_forms(gens, ks, explore, keep):
    """Sequences that `Standard` holds by construction: from `gen n` (n in gens),
    closed under `fs s k` (k in ks, k >= 1, last entry positive) and under the
    erasure of a final 0, through sequences of length <= explore; those of
    length <= keep."""
    seen = set()
    todo = [gen(n) for n in gens]
    while todo:
        s = todo.pop()
        if s in seen or len(s) > explore:
            continue
        seen.add(s)
        if not s:
            continue
        if s[-1] == 0:
            todo.append(s[:-1])
        else:
            todo.extend(fs(s, k) for k in ks if k >= 1)
    return sorted(x for x in seen if len(x) <= keep)
