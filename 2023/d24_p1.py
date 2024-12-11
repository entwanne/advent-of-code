# pip install z3-solver
import sys
from itertools import combinations
from typing import NamedTuple

import z3


class Vector(NamedTuple):
    x: int
    y: int

    def __add__(self, rhs):
        return type(self)(*(l + r for l, r in zip(self, rhs)))

    def __sub__(self, rhs):
        return type(self)(*(l - r for l, r in zip(self, rhs)))

    def __mul__(self, k):
        return type(self)(*(k * c for c in self))

    def __rmul__(self, k):
        return type(self)(*(k * c for c in self))

    def __neg__(self):
        return type(self)(*(-c for c in self))


def parse_file(f):
    for line in f:
        pos, velocity = line.strip().split(' @ ')
        px, py, _ = map(int, pos.split(', '))
        vx, vy, _ = map(int, velocity.split(', '))
        yield Vector(px, py), Vector(vx, vy)


def intersect_at(p1, v1, p2, v2):
    k1, k2 = z3.Reals('k1 k2')
    s = z3.Solver()

    s.add(p1.x + k1 * v1.x == p2.x + k2 * v2.x)
    s.add(p1.y + k1 * v1.y == p2.y + k2 * v2.y)

    if s.check() == z3.unsat:
        return False

    m = s.model()
    k1 = m.evaluate(k1).as_fraction()
    k2 = m.evaluate(k2).as_fraction()
    if k1 < 0 or k2 < 0:
        return False

    ip = p1 + k1 * v1
    cmin = 200000000000000
    cmax = 400000000000000
    return cmin <= ip.x <= cmax and cmin <= ip.y <= cmax
    


def count_intersections(data):
    return sum(intersect_at(p1, v1, p2, v2) for (p1, v1), (p2, v2) in combinations(data, 2))


if __name__ == '__main__':
    print(count_intersections(list(parse_file(sys.stdin))))
