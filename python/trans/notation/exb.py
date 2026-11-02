"""Extended Buchholz psi: exb (notations.md, section 3).

Lean: `Googology.Notation.ExBuchholz.Term` (Notation/ExBuchholz/Basic.lean:29),
`nil` = 0 and `cons a b t` = psi_a(b) + t.

Here a term is a tuple of principal terms, and a principal term is a pair
`(a, b)` of terms, meaning psi_a(b). So `()` is `nil`, and
`((a, b),) + t` is `cons a b t`.
"""

from .common import Reader, strip_spaces

ZERO = ()


def psi(a, b):
    """The principal term psi_a(b), standing alone (Lean `Term.psi`)."""
    return ((a, b),)


ONE = psi(ZERO, ZERO)                      # psi_0(0) = 1
P_ONE = ONE[0]
OMEGA = psi(ZERO, ONE)                     # psi_0(1) = w
P_OMEGA = OMEGA[0]
BIG_OMEGA = psi(ONE, ZERO)                 # psi_1(0) = W
P_W = BIG_OMEGA[0]
P_W2 = (ONE, BIG_OMEGA)                    # psi_1(psi_1(0)) = W^2 = p1(W)


def numeral(n):
    """Lean `numeral n`: psi_0(0) + ... + psi_0(0), n times."""
    return (P_ONE,) * n


def eps(n):
    """eN = psi_0(W + ... + W), N+1 copies of W (Lean `te0` for N = 0)."""
    return psi(ZERO, (P_W,) * (n + 1))


def zeta(n):
    """zN = psi_0(p1(W) + ... + p1(W)), N+1 copies (Lean `tzeta0` for N = 0)."""
    return psi(ZERO, (P_W2,) * (n + 1))


def omega_sub(a):
    """W_a = psi_a(0)."""
    return psi(a, ZERO)


# ---------------------------------------------------------------- parsing

def parse(s):
    r = Reader(strip_spaces(s), 'exb')
    t = _term(r)
    if not r.done():
        r.fail('unexpected character %r' % r.peek())
    return t


def _term(r):
    if r.at('0') and not r.peek(1).isdigit() and r.peek(1) != '+':
        r.eat('0')
        return ZERO
    out = _summand(r)
    while r.eat('+'):
        out += _summand(r)
    return out


def _summand(r):
    c = r.peek()
    if c.isdigit():
        return numeral(r.digits())
    if r.eat('w'):
        return OMEGA
    if r.eat('W'):
        if r.eat('_'):
            a = _sub(r)
            if a == ZERO:
                r.fail('W_0 is not a term: psi_0(0) is 1')
            return omega_sub(a)
        return BIG_OMEGA
    if c in 'ez' and r.peek(1).isdigit():
        r.eat(c)
        n = r.digits()
        return eps(n) if c == 'e' else zeta(n)
    if r.eat('p'):
        if r.at('('):
            a = ZERO
        elif r.eat('_'):
            a = _sub(r)
        elif r.peek().isdigit():
            a = numeral(r.digits())
        else:
            r.fail('expected "(", "_" or a numeral after "p"')
        r.expect('(')
        b = _term(r)
        r.expect(')')
        return psi(a, b)
    r.fail('expected a summand')


def _sub(r):
    c = r.peek()
    if c.isdigit():
        return numeral(r.digits())
    if r.eat('w'):
        return OMEGA
    if r.eat('W'):
        return BIG_OMEGA
    if c in 'ez' and r.peek(1).isdigit():
        r.eat(c)
        n = r.digits()
        return eps(n) if c == 'e' else zeta(n)
    if r.eat('('):
        t = _term(r)
        r.expect(')')
        return t
    r.fail('expected a subscript: a numeral, w, W, eN, zN or (term)')


# ---------------------------------------------------------------- printing

def _as_numeral(t):
    """n if t is the numeral n, else None."""
    return len(t) if all(p == P_ONE for p in t) else None


def _as_copies(b, p):
    """N if b is N+1 copies of the principal term p, else None."""
    if b and all(q == p for q in b):
        return len(b) - 1
    return None


def show(t):
    if not t:
        return '0'
    out = []
    i = 0
    while i < len(t):
        if t[i] == P_ONE:
            j = i
            while j < len(t) and t[j] == P_ONE:
                j += 1
            out.append(str(j - i))
            i = j
        else:
            out.append(_show_principal(t[i]))
            i += 1
    return '+'.join(out)


def _show_principal(p):
    a, b = p
    if p == P_OMEGA:
        return 'w'
    if p == P_W:
        return 'W'
    if a == ZERO:
        n = _as_copies(b, P_W)
        if n is not None:
            return 'e%d' % n
        n = _as_copies(b, P_W2)
        if n is not None:
            return 'z%d' % n
    if b == ZERO:
        return 'W_' + _show_sub(a)
    k = _as_numeral(a)
    if k is not None:
        return 'p%d(%s)' % (k, show(b))
    return 'p_%s(%s)' % (_show_sub(a), show(b))


def _show_sub(a):
    k = _as_numeral(a)
    if k is not None:
        return str(k)
    if len(a) == 1:
        s = _show_principal(a[0])
        if s in ('w', 'W') or (s[0] in 'ez' and s[1:].isdigit()):
            return s
    return '(' + show(a) + ')'


# ---------------------------------------------------------------- Lean form

def lean(t):
    """A Lean expression of type `Term` for the value, e.g. `.cons .nil .nil .nil`."""
    if not t:
        return '.nil'
    (a, b), rest = t[0], t[1:]
    return '.cons %s %s %s' % tuple(_paren(lean(x)) for x in (a, b, rest))


def _paren(s):
    return s if s == '.nil' else '(' + s + ')'
