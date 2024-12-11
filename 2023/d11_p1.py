import sys
from itertools import combinations


def parse_galaxies(f):
    return {
        (x, y)
        for y, line in enumerate(f)
        for x, char in enumerate(line)
        if char == '#'
    }


def expanse(galaxies):
    xset = {x for x, _ in galaxies}
    yset = {y for _, y in galaxies}
    xmiss = set(range(min(xset), max(xset) + 1)) - xset
    ymiss = set(range(min(yset), max(yset) + 1)) - yset
    return {
        (gx + sum(x < gx for x in xmiss), gy + sum(y < gy for y in ymiss))
        for gx, gy in galaxies
    }


def distance(p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    return abs(x2 - x1) + abs(y2 - y1)


if __name__ == '__main__':
    galaxies = expanse(parse_galaxies(sys.stdin))
    print(sum(distance(g1, g2) for g1, g2 in combinations(galaxies, 2)))
