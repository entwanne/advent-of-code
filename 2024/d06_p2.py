import sys
from itertools import pairwise

from d06_p1 import parse_map


def walk(start, grid):
    x, y = start
    dx, dy = 0, -1
    seen = {start}

    yield x, y

    while True:
        np = x + dx, y + dy

        block = grid.get(np)
        if block is None:
            break

        if block:
            yield x, y
            seen.add(np)
            x, y = np
            continue

        dx, dy = -dy, dx

    return seen


def find_loop(start, direction, grid):
    x, y = start
    dx, dy = direction
    seen = {(x, y, dx, dy)}

    while True:
        np = x + dx, y + dy

        block = grid.get(np)
        if block is None:
            break

        key = (*np, dx, dy)
        if key in seen:
            return True
        seen.add(key)

        if block:
            x, y = np
            continue

        dx, dy = -dy, dx

    return False


def count_loops(start, grid):
    seen = set()
    return sum(
        find_loop((x1, y1), (x2 - x1, y2 - y1), grid | {(x2, y2): False})
        for (x1, y1), (x2, y2) in pairwise(walk(start, grid))
        if (x2, y2) not in seen and (seen.add((x2, y2)) is None)
    )


if __name__ == '__main__':
    start, grid = parse_map(sys.stdin)
    print(count_loops(start, grid))
