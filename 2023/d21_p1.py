import sys


def parse_map(f):
    cells = {
        (x, y)
        for y, line in enumerate(f)
        for x, char in enumerate(line)
        if char == '.' or (char == 'S' and (start := (x, y)))
    }
    return start, cells


def walk(cells, points):
    return frozenset({
        p
        for x, y in points
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1))
        if (p := (x + dx, y + dy)) in cells
    })


def walkn(cells, starting_points, n):
    points = starting_points
    for _ in range(n):
        points = walk(cells, points)
    return points


if __name__ == '__main__':
    start, cells = parse_map(sys.stdin)
    print(len(walkn(cells, frozenset({start}), 64)))
