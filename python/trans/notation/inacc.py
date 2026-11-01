"""Psi over omega weakly inaccessibles: inacc (notations.md, section 5).

Lean: `Googology.Notation.InaccPsi.Term` (Notation/InaccPsi/Term.lean:27).
A term is a tuple whose first entry names the constructor:
    ('zero',)          0
    ('I', n)           I_n
    ('Iw',)            I_w
    ('add', a, b)      a + b
    ('phi', a, b)      phi(a, b)
    ('om', a)          Omega_a
    ('psiS', s, a)     psi_{Omega_{s+1}}(a)
    ('psiI', n, a)     psi_{I_n}(a)
"""

from .common import Reader, strip_spaces

ZERO = ('zero',)
ONE = ('phi', ZERO, ZERO)             # phi(0, 0) = w^0 = 1
OMEGA = ('phi', ZERO, ONE)            # phi(0, 1) = w


def numeral(n):
    """0, and 1 + (1 + ... + 1) for n >= 1, right associative."""
    if n == 0:
        return ZERO
    t = ONE
    for _ in range(n - 1):
        t = ('add', ONE, t)
    return t


# ---------------------------------------------------------------- parsing

def parse(s):
    r = Reader(strip_spaces(s), 'inacc')
    t = _term(r)
    if not r.done():
        r.fail('unexpected character %r' % r.peek())
    return t


def _term(r):
    xs = [_summand(r)]
    while r.eat('+'):
        xs.append(_summand(r))
    t = xs[-1]
    for x in reversed(xs[:-1]):
        t = ('add', x, t)
    return t


def _summand(r):
    if r.peek().isdigit():
        return numeral(r.digits())
    if r.eat('phi('):
        a = _term(r)
        r.expect(',')
        b = _term(r)
        r.expect(')')
        return ('phi', a, b)
    if r.eat('pS_'):
        s = _sub(r)
        r.expect('(')
        a = _term(r)
        r.expect(')')
        return ('psiS', s, a)
    if r.eat('pI_'):
        n = r.digits()
        r.expect('(')
        a = _term(r)
        r.expect(')')
        return ('psiI', n, a)
    if r.eat('I_'):
        if r.eat('w'):
            return ('Iw',)
        return ('I', r.digits())
    if r.eat('W'):
        if r.eat('_'):
            return ('om', _sub(r))
        return ('om', ONE)
    if r.eat('w'):
        return OMEGA
    if r.eat('('):
        t = _term(r)
        r.expect(')')
        return t
    r.fail('expected a summand')


def _sub(r):
    if r.peek().isdigit():
        return numeral(r.digits())
    if r.eat('w'):
        return OMEGA
    if r.eat('('):
        t = _term(r)
        r.expect(')')
        return t
    r.fail('expected a subscript: a numeral, w or (term)')


# ---------------------------------------------------------------- printing

def _as_numeral(t):
    """n if t is numeral(n), else None."""
    n = 0
    while t[0] == 'add' and t[1] == ONE:
        n += 1
        t = t[2]
    if t == ONE:
        return n + 1
    if t == ZERO and n == 0:
        return 0
    return None


def show(t):
    """A sum a + (b + c) prints as `a+b+c`; a trailing run of 1s as a numeral."""
    n = _as_numeral(t)
    if n is not None:
        return str(n)
    if t[0] != 'add':
        return _show_atom(t)
    a, b = t[1], t[2]
    left = '(' + show(a) + ')' if a[0] == 'add' else show(a)
    return left + '+' + show(b)


def _show_atom(t):
    k = t[0]
    if t == OMEGA:
        return 'w'
    if k == 'zero':
        return '0'
    if k == 'I':
        return 'I_%d' % t[1]
    if k == 'Iw':
        return 'I_w'
    if k == 'phi':
        return 'phi(%s,%s)' % (show(t[1]), show(t[2]))
    if k == 'om':
        return 'W' if t[1] == ONE else 'W_' + _show_sub(t[1])
    if k == 'psiS':
        return 'pS_%s(%s)' % (_show_sub(t[1]), show(t[2]))
    if k == 'psiI':
        return 'pI_%d(%s)' % (t[1], show(t[2]))
    raise ValueError('not an inacc term: %r' % (t,))


def _show_sub(a):
    n = _as_numeral(a)
    if n is not None:
        return str(n)
    if a == OMEGA:
        return 'w'
    return '(' + show(a) + ')'


# ---------------------------------------------------------------- Lean form

def lean(t):
    k = t[0]
    if k in ('zero', 'Iw'):
        return {'zero': '.zero', 'Iw': '.inaccW'}[k]
    if k == 'I':
        return '(.inacc %d)' % t[1]
    if k == 'om':
        return '(.om %s)' % lean(t[1])
    if k == 'psiI':
        return '(.psiI %d %s)' % (t[1], lean(t[2]))
    name = {'add': 'add', 'phi': 'phi', 'psiS': 'psiS'}[k]
    return '(.%s %s %s)' % (name, lean(t[1]), lean(t[2]))
