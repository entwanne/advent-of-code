import functools
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


d1, d2 = [[2]], [[6]]
packets = [p for pair in parse(sys.stdin) for p in pair] + [d1, d2]
packets.sort(key=functools.cmp_to_key(cmp))
print((packets.index(d1) + 1) * (packets.index(d2) + 1))
