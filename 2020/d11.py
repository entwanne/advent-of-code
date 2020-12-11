import sys
from itertools import product
from copy import deepcopy

grid = [list(line.strip()) for line in sys.stdin]

adjacents = [
    (dx, dy) for dy, dx in product(range(-1, 2), repeat=2)
    if (dx, dy) != (0, 0)
]

def nb_adjacents_p1(grid, x, y, neighbors={}):
    count = 0
    k = (x, y)
    nbs = neighbors.get(k, None)
    if nbs is None:
        nbs = neighbors[k] = set()
        for dx, dy in adjacents:
            tx, ty = x+dx, y+dy
            if 0 <= ty < len(grid) and 0 <= tx < len(grid[ty]):
                if grid[ty][tx] == '#':
                    nbs.add((tx, ty))
                    count += 1
                elif grid[ty][tx] == 'L':
                    nbs.add((tx, ty))
    else:
        for tx, ty in nbs:
            if grid[ty][tx] == '#':
                count += 1
    return count

def process_seats(grid, nb_adjacents, nb_free):
    grid = deepcopy(grid)
    changes = True
    while changes:
        changes = []
        for y, line in enumerate(grid):
            for x, seat in enumerate(line):
                if seat == '.':
                    continue
                count = nb_adjacents(grid, x, y)
                if seat == 'L':
                    if count == 0:
                        changes.append((x, y, '#'))
                elif seat == '#' and count >= nb_free:
                    changes.append((x, y, 'L'))
        for x, y, s in changes:
            grid[y][x] = s
    return grid

def count_seats(grid):
    return sum(1 for line in grid for seat in line if seat == '#')

grid_p1 = process_seats(grid, nb_adjacents_p1, 4)
print(count_seats(grid_p1))

def nb_adjacents_p2(grid, x, y, neighbors={}):
    count = 0
    k = (x, y)
    nbs = neighbors.get(k, None)
    if nbs is None:
        nbs = neighbors[k] = set()
        for dx, dy in adjacents:
            tx, ty = x+dx, y+dy
            while 0 <= ty < len(grid) and 0 <= tx < len(grid[ty]):
                if grid[ty][tx] == 'L':
                    nbs.add((tx, ty))
                    break
                if grid[ty][tx] == '#':
                    nbs.add((tx, ty))
                    count += 1
                    break
                tx += dx
                ty += dy
    else:
        for tx, ty in nbs:
            if grid[ty][tx] == '#':
                count += 1
    return count

grid_p2 = process_seats(grid, nb_adjacents_p2, 5)
print(count_seats(grid_p2))
