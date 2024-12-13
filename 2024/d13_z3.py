# pip install z3-solver

import sys

import z3

from d13_p1 import parse_file


def check_machine(m, n=0):
    (ax, ay), (bx, by), (x, y) = m

    s = z3.Solver()
    ak, bk = z3.Ints('ak bk')
    s.add(0 < ak)
    s.add(0 < bk)
    if not n:
        s.add(ak <= 100)
        s.add(bk <= 100)
    s.add(ak * ax + bk * bx == x + n)
    s.add(ak * ay + bk * by == y + n)

    if s.check() != z3.sat:
        return 0

    sol = s.model()
    ak, bk = sol[ak].as_long(), sol[bk].as_long()
    return 3 * ak + bk


if __name__ == '__main__':
    machines = list(parse_file(sys.stdin))
    print(sum(check_machine(m) for m in machines))
    print(sum(check_machine(m, n=10000000000000) for m in machines))
