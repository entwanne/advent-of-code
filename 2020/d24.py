import sys

directions = {
    'e': (2, 0),
    'se': (1, 1),
    'sw': (-1, 1),
    'w': (-2, 0),
    'nw': (-1, -1),
    'ne': (1, -1),
}


def parse_line(line):
    dirs = []
    while line:
        for d in directions:
            if line.startswith(d):
                dirs.append(d)
                line = line[len(d):]
                break
    return dirs


lines = [parse_line(line.strip()) for line in sys.stdin]

# p1

black = set()

for line in lines:
    x, y = 0, 0
    for d in line:
        dx, dy = directions[d]
        x += dx
        y += dy
    key = (x, y)
    if key in black:
        black.remove(key)
    else:
        black.add(key)

print(len(black))

# p2

grid = {pos: True for pos in black}
grid2 = {}

for _ in range(100):
    for (x, y), c in grid.items():
        grid2[x, y] = c
        if c:
            for dx, dy in directions.values():
                key = x+dx, y+dy
                grid2.setdefault(key, False)
    grid, grid2 = grid2, grid

    for (x, y), cell in grid.items():
        count = sum(1 for dx, dy in directions.values() if grid.get((x+dx, y+dy)))
        if cell and (count == 0 or count > 2):
            cell = False
        elif not cell and count == 2:
            cell = True
        grid2[x, y] = cell
    grid, grid2 = grid2, grid

print(sum(1 for _, c in grid.items() if c))
