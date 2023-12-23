import itertools
import sys


def parse(f):
    for line in f:
        yield [tuple(map(int, pos.split(','))) for pos in line.split(' -> ')]


def get_points(path):
    for (x1, y1), (x2, y2) in zip(path, path[1:]):
        rx = range(min(x1, x2), max(x1, x2) + 1)
        ry = range(min(y1, y2), max(y1, y2) + 1)
        yield from ((x, y) for y in ry for x in rx)


def fall_sand(grid, sand_src, floor):
    dirs = [(0, 1), (-1, 1), (1, 1)]

    for i in itertools.count(1):
        x, y = sand_src

        while True:
            for dx, dy in dirs:
                pos = x+dx, y+dy
                if pos[1] == floor:
                    continue
                if pos not in grid:
                    x, y = pos
                    break
            else:
                grid[x, y] = 'o'
                break

        if (x, y) == sand_src:
            return i

sand_src = (500, 0)

grid = {sand_src: '+'} | {rock_pos: '#' for path in parse(sys.stdin) for rock_pos in get_points(path)}
ymax = max(y for _, y in grid)

print(fall_sand(grid, sand_src, floor=ymax+2))
