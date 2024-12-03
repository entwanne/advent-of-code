# pip install z3-solver
import sys
from itertools import islice
from typing import NamedTuple

import z3


class Vector(NamedTuple):
    x: int
    y: int
    z: int

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
    # Keep only 3 first lines
    for line in islice(f, 3):
        pos, velocity = line.strip().split(' @ ')
        yield Vector(*map(int, pos.split(', '))), Vector(*map(int, velocity.split(', ')))


def solve(data):
    s = z3.Solver()
    x, y, z, vx, vy, vz = z3.Ints('x y z vx vy vz')

    for i, (p, v) in enumerate(data):
        ki = z3.Int(f'k{i}')
        s.add(ki >= 0)
        s.add(x + ki * vx == p.x + ki * v.x)
        s.add(y + ki * vy == p.y + ki * v.y)
        s.add(z + ki * vz == p.z + ki * v.z)

    assert s.check() == z3.sat
    m = s.model()
    return m[x].as_long() + m[y].as_long() + m[z].as_long()


if __name__ == '__main__':
    print(solve(parse_file(sys.stdin)))
