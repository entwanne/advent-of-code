import sys

from d06_p1 import meters


def parse(f):
    return [
        int(''.join(c for c in row if c.isdigit()))
        for row in f
    ]


if __name__ == '__main__':
    time, distance = parse(sys.stdin)
    print(sum(1 for m in meters(time) if m > distance))
