import itertools
import sys


def parse_map(f):
    for line in f:
        yield map(int, line.strip().split(','))


def parse_grid(f):
    return {(x, y) for x, y in parse_map(f)}


def area(p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    return (abs(x2 - x1) + 1) * (abs(y2 - y1) + 1)


def find_largest_area(grid):
    return max(area(p1, p2) for p1, p2 in itertools.combinations(grid, 2))


if __name__ == '__main__':
    print(find_largest_area(parse_grid(sys.stdin)))
