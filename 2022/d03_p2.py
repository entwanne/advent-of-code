import string
import sys


def parse(f):
    for line in f:
        packs = line.strip()
        yield packs


def make_groups(it):
    it = iter(it)
    for item in it:
        yield item, next(it), next(it)


def get_common(groups):
    for group in groups:
        x, = set.intersection(*(set(pack) for pack in group))
        yield x


print(
    sum(
        string.ascii_letters.index(c) + 1
        for c in get_common(make_groups(parse(sys.stdin)))
    )
)
