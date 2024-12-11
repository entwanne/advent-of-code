import sys

from d10_p1 import NORTH, SOUTH, WEST, EAST, parse_cases, parse_graph, count_distances


def clean(cases):
    graph, start = parse_graph(cases)
    loop = count_distances(graph, start).keys()
    cases = {pos: dirs for pos, dirs in cases.items() if pos in loop}

    # Replace start point by the real pipe
    x, y = start
    cases[start] = set()
    if SOUTH in cases.get((x, y - 1), ()):
        cases[start].add(NORTH)
    if NORTH in cases.get((x, y + 1), ()):
        cases[start].add(SOUTH)
    if EAST in cases.get((x - 1, y), ()):
        cases[start].add(WEST)
    if WEST in cases.get((x + 1, y), ()):
        cases[start].add(EAST)

    return cases


def bounds(cases):
    return (
        min(x for x, _ in cases),
        max(x for x, _ in cases),
        min(y for _, y in cases),
        max(y for _, y in cases),
    )


def count_inside(cases):
    xmin, xmax, ymin, ymax = bounds(cases)
    count = 0

    for y in range(ymin, ymax + 1):
        inside = False
        north_enabled = False
        south_enabled = False
        for x in range(xmin, xmax + 1):
            if (x, y) in cases:
                if NORTH in cases[x, y]:
                    north_enabled = not north_enabled
                if SOUTH in cases[x, y]:
                    south_enabled = not south_enabled
            elif north_enabled and south_enabled:
                count += 1

    return count


if __name__ == '__main__':
    cases = clean(parse_cases(sys.stdin))
    print(count_inside(cases))
