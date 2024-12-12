import sys

from d12_p1 import Counter, parse_file, parse_regions, area, get_segments


def sides(region):
    segments = sorted(get_segments(region))
    seen = set()
    count = 0

    for (x1, y1, x2, y2) in segments:
        new = True

        for (x3, y3, x4, y4) in seen:
            # previous segment continues with no inversion
            if ((x3, y3) in region) == ((x4, y4) in region):
                # (x1, y1, x2, y2) continues same segment than (x3, y3, x4, y4)
                if (x1, y1) == (x4, y4) and x2 - x1 == x4 - x3 and y2 - y1 == y4 - y3:
                    new = False
                    break

        if new:
            count += 1
        seen.add((x1, y1, x2, y2))

    return count


def score(regions):
    return sum(
        area(r) * sides(r)
        for r in regions
    )


if __name__ == '__main__':
    print(score(parse_regions(parse_file(sys.stdin))))
