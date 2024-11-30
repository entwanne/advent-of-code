import sys
from itertools import pairwise


def solve(hist):
    while any(hist):
        yield hist
        hist = [b-a for a, b in pairwise(hist)]
    yield hist


def fill(histories):
    f = 0
    for y in range(len(histories) - 1, -1, -1):
        f += histories[y][-1]
        histories[y].append(f)
    return histories


if __name__ == '__main__':
    data = [list(map(int, line.split())) for line in sys.stdin]
    print(sum(fill(list(solve(hist)))[0][-1] for hist in data))
