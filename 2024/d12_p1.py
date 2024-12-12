import sys
from collections import Counter


def parse_file(f):
    return {
        (x, y): char
        for y, line in enumerate(f)
        for x, char in enumerate(line.strip())
    }


def parse_region(cells, start):
    char = cells.pop(start)
    region = set()
    queue = [start]

    while queue:
        p = x, y = queue.pop(0)
        region.add(p)

        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            np = x + dx, y + dy
            if cells.get(np) == char:
                del cells[np]
                queue.append(np)
    
    return region


def parse_regions(cells):
    regions = []

    while cells:
        regions.append(parse_region(cells, min(cells)))

    return regions


def area(region):
    return len(region)


def get_segments(region):
    segments = Counter()

    for x, y in region:
        segments[x, y, x, y + 1] += 1
        segments[x, y, x + 1, y] += 1
        segments[x, y + 1, x + 1, y + 1] += 1
        segments[x + 1, y, x + 1, y + 1] += 1

    return (s for s, c in segments.items() if c == 1)


def perimeter(region):
    return sum(1 for _ in get_segments(region))


def score(regions):
    return sum(
        area(r) * perimeter(r)
        for r in regions
    )


if __name__ == '__main__':
    print(score(parse_regions(parse_file(sys.stdin))))
