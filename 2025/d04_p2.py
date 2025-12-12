import sys

from d04_p1 import parse_grid, is_accessible


def get_accessible(grid):
    return {p for p in grid if is_accessible(grid, p)}


def remove_all_accessible(grid):
    while acc := get_accessible(grid):
        grid -= acc
    return grid


if __name__ == '__main__':
    grid = parse_grid(sys.stdin)
    start_count = len(grid)
    remove_all_accessible(grid)
    print(start_count - len(grid))
