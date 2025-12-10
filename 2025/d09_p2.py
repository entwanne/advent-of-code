import itertools
import sys

from shapely import Polygon

from d09_p1 import parse_map, area


def parse_coords(f):
    return [(x, y) for x, y in parse_map(f)]


def is_valid(poly, p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    return poly.contains(Polygon(((x1, y1), (x2, y1), (x2, y2), (x1, y2))))


def find_largest_area(coords):
    coords = list(coords)
    poly = Polygon(coords)
    return max(area(p1, p2) for p1, p2 in itertools.combinations(coords, 2) if is_valid(poly, p1, p2))


if __name__ == '__main__':
    print(find_largest_area(parse_coords(sys.stdin)))
