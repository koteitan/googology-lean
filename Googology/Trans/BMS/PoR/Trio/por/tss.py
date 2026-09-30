"""Trio matrices (3-row BMS, z<2 mostly) as labelled row-0 trees.

term = (y, z, kids): a column with its row-0 subtree; x = depth.  ordinal = tuple of root terms.
Order: lexicographic order of column sequences (valid for standard matrices)."""
import re
from functools import lru_cache


def parse(s):
    out = []
    for c in re.findall(r'\(([^()]*)\)', s):
        v = tuple(int(u) for u in c.split(',')) if c.strip() else (0,)
        out.append(v + (0,) * (3 - len(v)))
    return out


def show(M):
    return ''.join('(%d,%d,%d)' % tuple(c) for c in M)


@lru_cache(maxsize=None)
def cols_term(t, d=0):
    out = [(d, t[0], t[1])]
    for ch in t[2]:
        out.extend(cols_term(ch, d + 1))
    return tuple(out)


@lru_cache(maxsize=None)
def mat(o):
    out = []
    for t in o:
        out.extend(cols_term(t, 0))
    return tuple(out)


def from_mat(M):
    M = [tuple(c) + (0,) * (3 - len(c)) for c in M]
    n = len(M)
    par = [-1] * n
    for i in range(n):
        for j in range(i - 1, -1, -1):
            if M[j][0] < M[i][0]:
                par[i] = j
                break
    kids = [[] for _ in range(n)]
    roots = []
    for i in range(n):
        (kids[par[i]] if par[i] >= 0 else roots).append(i)

    def build(i):
        return (M[i][1], M[i][2], tuple(build(k) for k in kids[i]))
    return tuple(build(r) for r in roots)


def tcmp(a, b):
    x, y = cols_term(a), cols_term(b)
    return (x > y) - (x < y)


def ocmp(a, b):
    x, y = mat(a), mat(b)
    return (x > y) - (x < y)


def add(a, b):
    if not b:
        return a
    a = list(a)
    while a and tcmp(a[-1], b[0]) < 0:
        a.pop()
    return tuple(a) + tuple(b)


def addall(terms):
    r = ()
    for t in terms:
        r = add(r, (t,))
    return r


def root(kids):
    return (0, 0, tuple(kids))


ONE = (0, 0, ())


def tshow(t):
    return show(cols_term(t, 0))


def oshow(o):
    return show(mat(o))
