import re
import sys


def find_numbers(data):
    for y, line in enumerate(data):
        for m in re.finditer(r'\d+', line):
            yield y, m.span(), int(m[0])


def find_part_numbers(data):
    grid = {
        (x, y): char
        for y, line in enumerate(data)
        for x, char in enumerate(line.rstrip())
    }

    for y, (x1, x2), number in find_numbers(data):
        xr = range(x1 - 1, x2 + 1)
        if any(grid.get((x, y - 1), '.') != '.' for x in xr) \
           or any(grid.get((x, y + 1), '.') != '.' for x in xr) \
           or grid.get((x1 - 1, y), '.') != '.' \
           or grid.get((x2, y), '.') != '.':
            yield number


if __name__ == '__main__':
    data = sys.stdin.readlines()
    print(sum(find_part_numbers(data)))
