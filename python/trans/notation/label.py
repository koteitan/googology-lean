"""Sheet labels: ord, input only (notations.md, section 4).

A port of `Googology.Trans.BMS.TrioRules` (Trans/ExBuchholz/BMS/Trio/TrioRules.lean),
which is itself a transcription of the reference program of
https://github.com/koteitan/trio (tools/probe_eps_range.py).

An ordinal is a Cantor normal form `Od`: a tuple of pairs (exponent, coefficient),
exponents decreasing. An exponent `Ex` is one of
    ('o', od)          the normal form od, as an exponent of w
    ('W', v)           Omega_v, v an Od
    ('psi', v, x)      psi_v(x), v and x Ods
The Lean functions keep a fuel of 200 on the depth of nesting; this port
recurses without fuel, which agrees whenever the depth stays below 200.
"""

from .common import ParseError

O0 = ('o', ())


def nat(n):
    """Lean `nat`."""
    return () if n == 0 else ((O0, n),)


ONE = nat(1)


def wpow(x):
    """Lean `wpow`: w^x."""
    return ((('o', x), 1),)


def ato(x):
    """Lean `ato`: the normal form an exponent denotes."""
    return x[1] if x[0] == 'o' else ((x, 1),)


def is_atom(x):
    return x[0] != 'o'


def lvl(x):
    """Lean `lvl`: the level v with Omega_v <= x < Omega_(v+1), None if countable."""
    if x[0] == 'W':
        return x[1]
    if x[0] == 'psi':
        v = x[1]
        if v == ():
            return None
        if len(v) == 1 and v[0][1] == 1 and v[0][0][0] == 'W':
            return v[0][0][1]
        return v
    od = x[1]
    if od == ():
        return None
    return lvl(od[0][0])


def is_card_psi(x):
    return (x[0] == 'psi' and len(x[1]) == 1 and x[1][0][1] == 1
            and x[1][0][0][0] == 'W')


def kind(x):
    if x[0] == 'W':
        return 0
    return -1 if is_card_psi(x) else 1


def _arg(x):
    return x[2] if x[0] == 'psi' else ()


def _cmp(a, b):
    return (a > b) - (a < b)


def cmp_atom(x, y):
    lx, ly = lvl(x), lvl(y)
    c = cmp_ord(() if lx is None else lx, () if ly is None else ly)
    if c:
        return c
    c = _cmp(kind(x), kind(y))
    if c:
        return c
    if x[0] == 'W':
        return 0
    return cmp_ord(_arg(x), _arg(y))


def cmp_exp(x, y):
    if is_atom(x) and is_atom(y):
        return cmp_atom(x, y)
    return cmp_ord(ato(x), ato(y))


def cmp_ord(a, b):
    """Lean `cmpOrd`: -1, 0 or 1."""
    for (ex, cx), (ey, cy) in zip(a, b):
        c = cmp_exp(ex, ey) or _cmp(cx, cy)
        if c:
            return c
    return _cmp(len(a), len(b))


def add(a, b):
    """Lean `add`: ordinal addition of normal forms."""
    if not b:
        return a
    lead, cb = b[0]
    keep = tuple(t for t in a if cmp_exp(t[0], lead) > 0)
    same = [t for t in a if cmp_exp(t[0], lead) == 0]
    if same:
        return keep + ((lead, same[0][1] + cb),) + b[1:]
    return keep + b


def add_exp(x, y):
    return add(ato(x), ato(y))


def mul(a, b):
    """Lean `mul`: ordinal multiplication of normal forms."""
    if not a or not b:
        return ()
    e1, c1 = a[0]
    ta = a[1:]
    out = ()
    for e, c in b:
        if e == O0:
            out = add(out, ((e1, c1 * c),) + ta)
        else:
            out = add(out, ((('o', add_exp(e1, e)), c),))
    return out


def power(a, b):
    """Lean `power`: exponentiation, as far as the notation needs it."""
    if not b:
        return ONE
    if a == ONE:
        return ONE
    if b == ONE:
        return a
    if len(b) == 1 and b[0][0] == O0:
        r = a
        for _ in range(b[0][1] - 1):
            r = mul(r, a)
        return r
    if not a:
        return ()
    e1 = a[0][0]
    if e1 == O0:
        return wpow(b)
    return wpow(mul(ato(e1), b))


# ---------------------------------------------------------------- parsing

def _canon(s):
    """Lean `canonGo`: `p(` and `p_` are sugar for `psi(` and `psi_`."""
    out = []
    prev = None
    for i, c in enumerate(s):
        follow = i + 1 < len(s) and s[i + 1] in '_('
        if c == 'p' and not (prev is not None and prev.isalpha()) and follow:
            out.append('psi')
        else:
            out.append(c)
        prev = c
    return ''.join(out)


def _tokens(s):
    """Lean `tokGo`: tokens 'psi', 'w', 'W', ints and the symbols + * ^ ( ) _."""
    toks = []
    i = 0
    while i < len(s):
        if s.startswith('psi', i):
            toks.append('psi')
            i += 3
        elif s[i].isdigit():
            j = i
            while j < len(s) and s[j].isdigit():
                j += 1
            toks.append(int(s[i:j]))
            i = j
        elif s[i] in 'wW+*^()_':
            toks.append(s[i])
            i += 1
        else:
            raise ParseError('ord: unexpected character %r in %r' % (s[i], s))
    return toks


class _P:
    def __init__(self, toks, src):
        self.t = toks
        self.i = 0
        self.src = src

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self):
        x = self.peek()
        self.i += 1
        return x

    def fail(self):
        raise ParseError('ord: cannot read %r (token %d)' % (self.src, self.i))

    def atom(self):
        x = self.take()
        if x == '(':
            e = self.expr()
            if self.take() != ')':
                self.fail()
            return e
        if x == 'w':
            return wpow(ONE)
        if x == 'W':
            if self.peek() == '_':
                self.take()
                return ato(('W', self.atom()))
            return ato(('W', ONE))
        if x == 'psi':
            v = ()
            if self.peek() == '_':
                self.take()
                v = self.atom()
            if self.take() != '(':
                self.fail()
            e = self.expr()
            if self.take() != ')':
                self.fail()
            return ((('psi', v, e), 1),)
        if isinstance(x, int):
            return nat(x)
        self.fail()

    def pw(self):
        b = self.atom()
        if self.peek() == '^':
            self.take()
            return power(b, self.pw())
        return b

    def term(self):
        f = self.pw()
        while True:
            x = self.peek()
            if x == '*':
                self.take()
                f = mul(f, self.pw())
            elif isinstance(x, int):
                f = mul(f, self.pw())
            else:
                return f

    def expr(self):
        e = self.term()
        while self.peek() == '+':
            self.take()
            e = add(e, self.term())
        return e


def parse(s):
    """Lean `parse`: the ordinal a label names."""
    src = ''.join(s.split())
    p = _P(_tokens(_canon(src)), s)
    e = p.expr()
    if p.peek() is not None:
        p.fail()
    return e


# ---------------------------------------------------------------- Lean form

def lean(a):
    """A Lean expression of type `Od` for the value, e.g. `[(.W [(.o [], 1)], 1)]`."""
    return '[' + ', '.join('(%s, %d)' % (lean_ex(e), c) for e, c in a) + ']'


def lean_ex(x):
    if x[0] == 'o':
        return '.o %s' % lean(x[1])
    if x[0] == 'W':
        return '.W %s' % lean(x[1])
    return '.psi %s %s' % (lean(x[1]), lean(x[2]))
