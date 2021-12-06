import sys
from collections import Counter


grid = Counter()
dists = Counter()


def parse_code(code):
    return code[0], int(code[1:])


for line in sys.stdin:
    wire = (parse_code(x) for x in line.split(','))
    subgrid = Counter()
    x, y = 0, 0
    c = 0
    for op, arg in wire:
        if op == 'U':
            xr = [x]
            yr = range(y+1, y+arg+1)
            y += arg
        elif op == 'D':
            xr = [x]
            yr = range(y-1, y-arg-1, -1)
            y -= arg
        elif op == 'L':
            xr = range(x-1, x-arg-1, -1)
            yr = [y]
            x -= arg
        elif op == 'R':
            xr = range(x+1, x+arg+1)
            yr = [y]
            x += arg
        for y_ in yr:
            for x_ in xr:
                c += 1
                subgrid[x_, y_] = 1
                dists[x_, y_] += c

    grid += subgrid


print(min(dists[pos] for pos, c in grid.items() if c > 1))
