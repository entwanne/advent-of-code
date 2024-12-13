import sys

from d13_p1 import parse_file


def check_machine(m):
    (ax, ay), (bx, by), (x, y) = m
    x += 10000000000000
    y += 10000000000000

    # ak * ax + bk * bx = x
    # ak * ay + bk * by = y
    #
    # ak = (x - bk * bx) / ax
    # ay * (x - bk * bx) / ax + bk * by = y
    # ay * (x - bk * bx) + bk * by * ax = y * ax
    # ay * x - ay * bk * bx + bk * by * ax = y * ax
    # -ay * bx * bk + ax * by * bk = y * ax - x * ay
    # bk * (ax * by - ay * bx) = y * ax - x * ay
    # bk = (y * ax - x * ay) / (ax * by - ay * bx)

    bk = (y * ax - x * ay) / (ax * by - ay * bx)
    ak = (x - bk * bx) / ax

    if ak == int(ak) and bk == int(bk):
        return int(3 * ak + bk)
    return 0


if __name__ == '__main__':
    print(sum(check_machine(m) for m in parse_file(sys.stdin)))
