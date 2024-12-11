import sys

from d10_p2 import count_inside as base_count_inside, NORTH, SOUTH, WEST, EAST


DIRS = {
    'U': (0, -1),
    'D': (0, 1),
    'L': (-1, 0),
    'R': (1, 0),
}


def parse_file(f):
    for line in f:
        direction, distance, *_ = line.split()
        yield DIRS[direction], int(distance)


def dig(instructions):
    grid = set()
    x, y = 0, 0

    for (dx, dy), dist in instructions:
        for _ in range(dist):
            x += dx
            y += dy
            grid.add((x, y))

    return grid


def count_inside(grid):
    cases = {}
    for x, y in grid:
        s = cases[x, y] = set()
        if (x, y - 1) in grid:
            s.add(NORTH)
        if (x, y + 1) in grid:
            s.add(SOUTH)
        if (x - 1, y) in grid:
            s.add(WEST)
        if (x + 1, y) in grid:
            s.add(EAST)
    return base_count_inside(cases)


if __name__ == '__main__':
    grid = dig(parse_file(sys.stdin))
    print(len(grid) + count_inside(grid))
