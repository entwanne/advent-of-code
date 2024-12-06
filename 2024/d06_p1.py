import sys


CHARS = {
    '.': True,
    '^': True,
    '#': False,
}


def parse_map(f):
    start = (0, 0)
    grid = {}
    for y, line in enumerate(f):
        for x, char in enumerate(line):
            if char in CHARS:
                grid[x, y] = CHARS[char]
            if char == '^':
                start = (x, y)

    return start, grid


def walk(start, grid):
    x, y = start
    dx, dy = 0, -1
    seen = {start}

    while True:
        np = x + dx, y + dy

        block = grid.get(np)
        if block is None:
            break

        if block:
            seen.add(np)
            x, y = np
            continue

        dx, dy = -dy, dx

    return seen


if __name__ == '__main__':
    print(len(walk(*parse_map(sys.stdin))))
