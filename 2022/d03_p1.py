import string
import sys


def parse(f):
    for line in f:
        packs = line.strip()
        pivot = len(packs) // 2
        yield packs[:pivot], packs[pivot:]


def get_common(pairs):
    for p1, p2 in pairs:
        x, = set(p1) & set(p2)
        yield x

print(
    sum(
        string.ascii_letters.index(c) + 1
        for c in get_common(parse(sys.stdin))
    )
)
