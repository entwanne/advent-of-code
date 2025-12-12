import sys


def parse_map(f):
    start = None
    grid = {}

    for y, line in enumerate(f):
        line = line.strip()
        if not line:
            break

        for x, char in enumerate(line):
            match char:
                case '@':
                    start = x, y
                    grid[x, y] = False
                case 'O':
                    grid[x, y] = True
                case '.':
                    grid[x, y] = False

    return start, grid


def parse_directions(f):
    chars = {
        '<': (-1, 0),
        '>': (1, 0),
        '^': (0, -1),
        'v': (0, 1),
    }
    return [chars[c] for c in f.read() if c in chars]


def parse_file(f):
    return *parse_map(f), parse_directions(f)


def find_next_pos(grid, x, y, dx, dy):
    while (x, y) in grid:
        if not grid[x, y]:
            return x, y
        x, y = x + dx, y + dy
    return False


def moves(start, grid, directions):
    x, y = start

    for dx, dy in directions:
        np = x + dx, y + dy
        if np not in grid:
            continue
        if grid[np]:
            if r := find_next_pos(grid, *np, dx, dy):
                grid[r] = True
                grid[np] = False
                x, y = np
        else:
            x, y = np
    return grid


def score(grid):
    return sum(
        x + 100 * y
        for (x, y), c in grid.items()
        if c
    )


if __name__ == '__main__':
    print(score(moves(*parse_file(sys.stdin))))
