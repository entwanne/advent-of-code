import sys


def parse_grid(f):
    return {
        (x, y)
        for y, line in enumerate(f)
        for x, char in enumerate(line)
        if char == '@'
    }


def is_accessible(grid, pos):
    x, y = pos
    return pos in grid and sum((x+dx, y+dy) in grid for dy in range(-1, 2) for dx in range(-1, 2)) <= 4


def count_accessible(grid):
    return sum(is_accessible(grid, p) for p in grid)


if __name__ == '__main__':
    print(count_accessible(parse_grid(sys.stdin)))
