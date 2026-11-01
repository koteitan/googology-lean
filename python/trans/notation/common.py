"""Shared pieces of the ASCII notations (notations.md, section 0)."""


class ParseError(ValueError):
    """A string that is not a term of the notation it was read in."""


def strip_spaces(s):
    """Spaces are ignored on input (notations.md, section 0)."""
    return ''.join(s.split())


class Reader:
    """A cursor on a string, for the recursive-descent parsers."""

    def __init__(self, s, what):
        self.s = s
        self.i = 0
        self.what = what

    def peek(self, k=0):
        j = self.i + k
        return self.s[j] if j < len(self.s) else ''

    def at(self, lit):
        return self.s.startswith(lit, self.i)

    def eat(self, lit):
        if self.at(lit):
            self.i += len(lit)
            return True
        return False

    def expect(self, lit):
        if not self.eat(lit):
            self.fail('expected %r' % lit)

    def digits(self):
        j = self.i
        while self.peek().isdigit():
            self.i += 1
        if j == self.i:
            self.fail('expected a numeral')
        return int(self.s[j:self.i])

    def done(self):
        return self.i >= len(self.s)

    def fail(self, msg):
        raise ParseError('%s: %s at position %d in %r' % (self.what, msg, self.i, self.s))
