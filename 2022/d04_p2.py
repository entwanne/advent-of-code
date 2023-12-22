import sys


def fullset(a, b):
    return set(range(a, b+1))


def parse(f):
    for line in f:
        elfs = line.strip().split(',')
        yield [
            fullset(*map(int, elf.split('-')))
            for elf in elfs
        ]


def overlap(pair):
    p1, p2 = pair
    return bool(p1 & p2)


print(sum(overlap(pair) for pair in parse(sys.stdin)))
