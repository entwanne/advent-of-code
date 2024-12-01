# pip install shapely
import sys

import shapely


DIRS = {
    '3': (0, -1),
    '1': (0, 1),
    '2': (-1, 0),
    '0': (1, 0),
}


def parse_file(f):
    for line in f:
        _, _, value = line.split()
        value = value.removeprefix('(#').removesuffix(')')
        yield DIRS[value[-1]], int(value[:-1], 16)


def polygon(instructions):
    x, y = 0.5, 0.5
    points = [(x, y)]
    for (dx, dy), dist in instructions:
        x += dist * dx
        y += dist * dy
        points.append((x, y))

    return shapely.Polygon(points)


def area(poly):
    return int(poly.buffer(0.5, join_style='mitre').area)


if __name__ == '__main__':
    poly = polygon(parse_file(sys.stdin))
    print(area(poly))
