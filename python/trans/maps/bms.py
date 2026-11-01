"""Maps between matrices, and the one-row reading into extended Buchholz terms.

Lean sources:
- zeroRow      Googology/Trans/BMS/BMS/ZeroRow.lean:38 (BMS r+1 rows -> r+2 rows),
               used for DBMS by dbmsL_homSucc, Googology/Trans/DBMS/DBMS/ZeroRow.lean:168;
               toPairS (Googology/Trans/BMS/BMS/Embed.lean:79) is the case of one row.
- l1ToPrim, primToL1   Googology/Trans/DBMS/BMS/OneRowL.lean:113, :116 (identity on lists)
- read         Googology/Trans/BMS/ExBuchholz/Basic.lean:49
- unread       Googology/Trans/BMS/ExBuchholz/Basic.lean:197

A one-row matrix l is standard when Col 0 l and OT (read 0 l) (PrimState,
Googology/Trans/BMS/ExBuchholz/Prim.lean:74); the edges below accept standard
inputs only.
"""

from .errors import DomainError
from notation import exb
from notation.exb_std import is_ot


def zero_row(m):
    """Lean `zeroRow`: a row of zeros underneath."""
    return tuple(c + (0,) for c in m)


def row_of(m):
    """A one-row matrix as its list of entries."""
    return tuple(c[0] for c in m)


def of_row(l):
    return tuple((a,) for a in l)


def read(b, s):
    """Lean `read b s`: the primitive-sequence reading at level b."""
    if not s:
        return exb.ZERO
    rest = s[1:]
    i = 0
    while i < len(rest) and b < rest[i]:
        i += 1
    return ((exb.ZERO, read(b + 1, rest[:i])),) + read(b, rest[i:])


def unread(b, t):
    """Lean `unread b t`: the inverse reading. Subscripts are ignored."""
    out = []
    for _, x in t:
        out.append(b)
        out.extend(unread(b + 1, x))
    return tuple(out)


def is_col(b, s):
    """Lean `Col b s`: starts at b, never goes below b, never rises by more than one."""
    if not s:
        return True
    if s[0] != b:
        return False
    return all(b <= y <= x + 1 for x, y in zip(s, s[1:]))


def zero_subscripts(t):
    """Every subscript of t is 0 (the terms below e0 that `unread` inverts)."""
    return all(a == exb.ZERO and zero_subscripts(x) for a, x in t)


# ---------------------------------------------------------------- edges

def bms1_to_exb(m):
    s = row_of(m)
    if not is_col(0, s):
        raise DomainError('read: not a primitive sequence matrix (Col 0): %s' % (s,))
    t = read(0, s)
    if not is_ot(t):
        raise DomainError('read: not a standard primitive sequence (its reading is not OT)')
    return t


def exb_to_bms1(t):
    if not zero_subscripts(t):
        raise DomainError('unread: a subscript is not 0 (the term is not below e0)')
    if not is_ot(t):
        raise DomainError('unread: the term is not standard (isOT)')
    return of_row(unread(0, t))
