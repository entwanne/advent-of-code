import sys


def parse(f):
    for line in f:
        yield [tuple(map(int, pos.split(','))) for pos in line.split(' -> ')]


def get_points(path):
    for (x1, y1), (x2, y2) in zip(path, path[1:]):
        rx = range(min(x1, x2), max(x1, x2) + 1)
        ry = range(min(y1, y2), max(y1, y2) + 1)
        yield from ((x, y) for y in ry for x in rx)


def fall_sand(grid, sand_src):
    dirs = [(0, 1), (-1, 1), (1, 1)]

    while True:
        x, y = sand_src

        while True:
            for dx, dy in dirs:
                pos = x+dx, y+dy
                if pos not in grid:
                    return
                if grid[pos] == '.':
                    x, y = pos
                    break
            else:
                grid[x, y] = 'o'
                break

sand_src = (500, 0)

grid = {sand_src: '+'} | {rock_pos: '#' for path in parse(sys.stdin) for rock_pos in get_points(path)}
xmin = min(x for x, _ in grid)
xmax = max(x for x, _ in grid)
ymin = min(y for _, y in grid)
ymax = max(y for _, y in grid)

for y in range(ymin, ymax+1):
    for x in range(xmin, xmax+1):
        grid.setdefault((x, y), '.')

fall_sand(grid, sand_src)
print(sum(v == 'o' for v in grid.values()))
