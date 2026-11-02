"""Strong second-order searching sequences: ssoss (notations.md, section 2).

A sequence is a tuple of naturals, the Lean `List Nat` of `Notation/SSOSS`
(`Seq.Sequence`). It is written as in the source, `(0,0,1,1)`; the empty
sequence is `()`. On input the parentheses may be left out.
"""

import re

from .common import ParseError, strip_spaces

_BODY = re.compile(r'[0-9]+(,[0-9]+)*')


def parse(s):
    t = strip_spaces(s)
    if t == '()':
        return ()
    if t.startswith('(') and t.endswith(')'):
        t = t[1:-1]
    if not _BODY.fullmatch(t):
        raise ParseError('ssoss: expected naturals separated by commas, as (0,0,1,1): %r' % s)
    return tuple(int(v) for v in t.split(','))


def show(q):
    return '(' + ','.join(str(v) for v in q) + ')'


def lean(q):
    return '[' + ', '.join(str(v) for v in q) + ']'
