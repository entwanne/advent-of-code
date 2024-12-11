import sys

from d11_p1 import *


def expanse(galaxies, n=2):
    xset = {x for x, _ in galaxies}
    yset = {y for _, y in galaxies}
    xmiss = set(range(min(xset), max(xset) + 1)) - xset
    ymiss = set(range(min(yset), max(yset) + 1)) - yset
    return {
        (gx + sum(x < gx for x in xmiss) * (n - 1), gy + sum(y < gy for y in ymiss) * (n - 1))
        for gx, gy in galaxies
    }


if __name__ == '__main__':
    galaxies = expanse(parse_galaxies(sys.stdin), n=1000000)
    print(sum(distance(g1, g2) for g1, g2 in combinations(galaxies, 2)))
