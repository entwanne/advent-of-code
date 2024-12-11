import sys

from d09_p1 import solve


def fill(histories):
    f = 0
    for y in range(len(histories) - 1, -1, -1):
        f = histories[y][0] - f
        histories[y].insert(0, f)
    return histories


if __name__ == '__main__':
    data = [list(map(int, line.split())) for line in sys.stdin]
    print(sum(fill(list(solve(hist)))[0][0] for hist in data))
