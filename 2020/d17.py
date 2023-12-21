import sys
from itertools import product


puzzle = {}
for y, line in enumerate(sys.stdin):
    for x, state in enumerate(line.strip()):
        puzzle[(x, y)] = state


def get_neighbors(pos, adjacents):
    for d in adjacents:
        yield tuple(a+b for (a, b) in zip(pos, d))


def count_active_neighbors(grid, pos, adjacents):
    count = 0
    for key in get_neighbors(pos, adjacents):
        if grid.get(key, '.') == '#':
            count += 1
    return count


def get_new_state(state, grid, pos, adjcents):
    count = count_active_neighbors(grid, pos, adjacents)
    return '#' if count == 3 or (count == 2 and state == '#') else '.'


def process(grid, n, adjacents):
    grid2 = {}

    for _ in range(n):
        for pos, state in grid.items():
            grid2[pos] = state
            for key in get_neighbors(pos, adjacents):
                grid2.setdefault(key, '.')
        grid, grid2 = grid2, grid

        for pos, state in grid.items():
            grid2[pos] = get_new_state(state, grid, pos, adjacents)
        grid, grid2 = grid2, grid

    return grid


def count_active(grid):
    return sum(1 for s in grid.values() if s == '#')


# P1

grid = {(x, y, 0): state for (x, y), state in puzzle.items()}
adjacents = [
    pos for pos in product(range(-1, 2), repeat=3)
    if any(pos)
]

grid = process(grid, 6, adjacents)
print(count_active(grid))


# P2

grid = {(x, y, 0, 0): state for (x, y), state in puzzle.items()}
adjacents = [
    pos for pos in product(range(-1, 2), repeat=4)
    if any(pos)
]

grid = process(grid, 6, adjacents)
print(count_active(grid))
