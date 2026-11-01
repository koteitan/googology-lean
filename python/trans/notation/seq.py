"""Sequences: y and omegay (notations.md, section 2).

A sequence is a tuple of naturals, the Lean `List Nat`. It is written without
parentheses, `1,3,4,2,5`; the empty sequence is `()`.
"""

import re

from .common import ParseError, strip_spaces

_SEQ = re.compile(r'[0-9]+(,[0-9]+)*')


def parse(s):
    t = strip_spaces(s)
    if t == '()':
        return ()
    if not _SEQ.fullmatch(t):
        raise ParseError('sequence: expected naturals separated by commas: %r' % s)
    return tuple(int(v) for v in t.split(','))


def show(q):
    return ','.join(str(v) for v in q) if q else '()'
