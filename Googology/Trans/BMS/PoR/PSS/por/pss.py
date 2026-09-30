"""Pair sequences (2-row Bashicu matrices) as labelled trees, and PSS expansion.

A column (x, y).  Row-0 parent of column i: nearest j < i with x_j < x_i.
A term is (y, children) where children is a tuple of terms (the row-0 subtree);
an ordinal is a tuple of terms (the root segments, a descending sum).
Terms <-> matrices is a bijection (x = depth in the row-0 tree).
Order: lexicographic order of the column sequences (valid for standard matrices).
"""
import re
from functools import lru_cache


def parse(s):
    return [tuple(int(v) for v in c.split(',')) for c in re.findall(r'\(([^()]*)\)', s)]


def show(M):
    return ''.join('(%d,%d)' % c for c in M)


@lru_cache(maxsize=None)
def cols_term(t, d=0):
    out = [(d, t[0])]
    for ch in t[1]:
        out.extend(cols_term(ch, d + 1))
    return tuple(out)


@lru_cache(maxsize=None)
def mat(o):
    out = []
    for t in o:
        out.extend(cols_term(t, 0))
    return tuple(out)


def from_mat(M):
    """matrix -> ordinal (tuple of terms). Roots are columns with no row-0 parent."""
    M = list(M)
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
        return (M[i][1], tuple(build(k) for k in kids[i]))
    return tuple(build(r) for r in roots)


def tcmp(a, b):
    """compare terms"""
    x, y = cols_term(a), cols_term(b)
    return (x > y) - (x < y)


def ocmp(a, b):
    x, y = mat(a), mat(b)
    return (x > y) - (x < y)


def add(a, b):
    """ordinal sum with absorption (CNF)."""
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


# ---------------------------------------------------------------- expansion
def parents(M):
    n = len(M)
    p0 = [-1] * n
    for i in range(n):
        for j in range(i - 1, -1, -1):
            if M[j][0] < M[i][0]:
                p0[i] = j
                break
    p1 = [-1] * n
    for i in range(n):
        j = p0[i]
        while j >= 0:
            if M[j][1] < M[i][1]:
                p1[i] = j
                break
            j = p0[j]
    return p0, p1


def expand(M, k):
    """M[k] (2-row BMS / PSS rule), k >= 1: G B_0 B_1 ... B_k."""
    M = list(M)
    last = M[-1]
    if last == (0, 0):
        return M[:-1]
    p0, p1 = parents(M)
    n = len(M) - 1
    if last[1] > 0:
        r = p1[n]
        delta = last[0] - M[r][0]
    else:
        r = p0[n]
        delta = 0
    G = M[:r]
    B = M[r:n]
    # ascending columns: row-0 descendants of r (inclusive) within B
    asc = []
    for i in range(r, n):
        j = i
        while j > r:
            j = p0[j]
        asc.append(j == r)
    out = G + B
    for m in range(1, k + 1):
        for i, c in enumerate(B):
            out.append((c[0] + m * delta, c[1]) if asc[i] else c)
    return out
