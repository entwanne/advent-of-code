import sys
from collections import Counter


grid = Counter()


def parse_code(code):
    return code[0], int(code[1:])


def distance(x, y):
    return abs(x) + abs(y)


for line in sys.stdin:
    wire = (parse_code(x) for x in line.split(','))
    subgrid = Counter()
    x, y = 0, 0
    for op, arg in wire:
        if op == 'U':
            xr = [x]
            yr = range(y+1, y+arg+1)
            y += arg
        elif op == 'D':
            xr = [x]
            yr = range(y-arg, y)
            y -= arg
        elif op == 'L':
            xr = range(x-arg, x)
            yr = [y]
            x -= arg
        elif op == 'R':
            xr = range(x+1, x+arg+1)
            yr = [y]
            x += arg
        for y_ in yr:
            for x_ in xr:
                subgrid[x_, y_] = 1

    grid += subgrid


print(min(distance(x, y) for (x, y), c in grid.items() if c > 1))
