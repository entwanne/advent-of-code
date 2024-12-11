import sys

from d16_p1 import *


def starting_positions(cells):
    xmin = min(x for x, _ in cells)
    xmax = max(x for x, _ in cells)
    ymin = min(y for _, y in cells)
    ymax = max(y for _, y in cells)

    for x in range(xmin, xmax + 1):
        yield (x, ymin, 0, 1)
        yield (x, ymax, 0, -1)

    for y in range(ymin, ymax + 1):
        yield (xmin, y, 1, 0)
        yield (xmax, y, -1, 0)


if __name__ == '__main__':
    cells = parse_map(sys.stdin)
    print(max(len(energized(cells, start)) for start in starting_positions(cells)))
