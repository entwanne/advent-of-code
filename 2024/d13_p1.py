import re
import sys


def parse_line(f):
    x, y = map(int, re.findall(r'\d+', f.readline()))
    return x, y


def parse_machine(f):
    return parse_line(f), parse_line(f), parse_line(f)


def parse_file(f):
    while True:
        yield parse_machine(f)
        if f.readline() == '':
            break


def check_machine(m):
    (ax, ay), (bx, by), (x, y) = m

    for ak in range(1, 101):
        if ak * ax > x or ak * ay > y:
            break
        for bk in range(1, 101):
            nx = ak * ax + bk * bx
            ny = ak * ay + bk * by
            if (nx, ny) == (x, y):
                return 3 * ak + bk
            elif nx > x or ny > y:
                break
    return 0


if __name__ == '__main__':
    print(sum(check_machine(m) for m in parse_file(sys.stdin)))
