"""Order and standard forms of extended Buchholz terms.

Port of `Term.cmp` and `Term.isOT` (Lean, `Googology.Notation.ExBuchholz`).
A term is as in `exb.py`: a tuple of principal terms `(a, b)` = psi_a(b);
`()` is `nil`, and `((a, b),) + t` is `cons a b t`.
"""

from .exb import BIG_OMEGA, ZERO


# Googology/Notation/ExBuchholz/Basic.lean:45  Term.cmp
#   cmp nil nil = eq;  cmp nil (cons ..) = lt;  cmp (cons ..) nil = gt
#   cmp (cons a b t) (cons c d u) = (cmp a c).then ((cmp b d).then (cmp t u))
# The recursion on the tail is unrolled into a loop over the summands.
def cmp(x, y):
    """-1, 0, 1 for Lean `.lt`, `.eq`, `.gt`."""
    for (a, b), (c, d) in zip(x, y):
        r = cmp(a, c)
        if r:
            return r
        r = cmp(b, d)
        if r:
            return r
    return (len(x) > len(y)) - (len(x) < len(y))


# Basic.lean:52 / :55  Term.lt, Term.le
def lt(x, y):
    return cmp(x, y) < 0


def le(x, y):
    return cmp(x, y) <= 0


# Googology/Notation/ExBuchholz/Std.lean:22  Term.G
#   G a nil = []
#   G a (cons c d t) = (if a <= c then d :: (G a c ++ G a d) else []) ++ G a t
def G(a, t):
    out = []
    for c, d in t:
        if le(a, c):
            out.append(d)
            out += G(a, c)
            out += G(a, d)
    return out


# Std.lean:33  Term.descHead: the head psi_c(d) of t satisfies psi c d <= psi a b
def desc_head(a, b, t):
    if not t:
        return True
    c, d = t[0]
    return le(((c, d),), ((a, b),))


# Std.lean:39  Term.isOT
#   isOT nil = true
#   isOT (cons a b t) = isOT a && isOT b && (G a b).all (· < b) && isOT t && descHead a b t
def is_ot(x):
    for k, (a, b) in enumerate(x):
        t = x[k + 1:]
        if not (is_ot(a) and is_ot(b) and all(lt(g, b) for g in G(a, b))
                and desc_head(a, b, t)):
            return False
    return True


# Googology/Notation/ExBuchholz/System.lean:40  exbOT.State = {X // OT X ∧ X < tW}
def is_countable_ot(x):
    """A state of `exbOT`: standard and below Omega = psi_1(0)."""
    return is_ot(x) and lt(x, BIG_OMEGA)


__all__ = ['cmp', 'lt', 'le', 'G', 'desc_head', 'is_ot', 'is_countable_ot', 'ZERO']
