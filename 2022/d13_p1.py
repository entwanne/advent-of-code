import itertools
import sys


def parse_pair(it):
    for line in it:
        line = line.strip()
        if not line:
            break
        yield eval(line)


def parse(f):
    it = iter(f)
    while pair := list(parse_pair(it)):
        yield pair


def cmp(left, right):
    if isinstance(left, int) and isinstance(right, int):
        return left - right
    if isinstance(left, int):
        left = [left]
    if isinstance(right, int):
        right = [right]

    for l, r in itertools.zip_longest(left, right):
        if l is None:
            return -1
        if r is None:
            return 1
        if x := cmp(l, r):
            return x

    return 0


print(sum(i for i, pair in enumerate(parse(sys.stdin), 1) if cmp(*pair) < 0))
