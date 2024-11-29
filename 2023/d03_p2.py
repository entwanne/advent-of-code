import operator
import sys
from functools import reduce

from d03_p1 import find_numbers


def find_gears(data):
    grid = {
        (x, y): char
        for y, line in enumerate(data)
        for x, char in enumerate(line.rstrip())
    }

    gears = {}

    for y, (x1, x2), number in find_numbers(data):
        for x in range(x1 - 1, x2 + 1):
            if grid.get((x, y - 1), '.') == '*':
                gears.setdefault((x, y - 1), []).append(number)
            if grid.get((x, y + 1), '.') == '*':
                gears.setdefault((x, y + 1), []).append(number)
        if grid.get((x1 - 1, y), '.') == '*':
            gears.setdefault((x1 - 1, y), []).append(number)
        if grid.get((x2, y), '.') == '*':
            gears.setdefault((x2, y), []).append(number)

    return gears.values()


if __name__ == '__main__':
    data = sys.stdin.readlines()
    print(sum(reduce(operator.mul, gear) for gear in find_gears(data) if len(gear) == 2))
