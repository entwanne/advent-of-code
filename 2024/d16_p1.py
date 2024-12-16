import heapq
import sys


def parse_map(f):
    grid = set()
    start = stop = None

    for y, line in enumerate(f):
        for x, char in enumerate(line):
            if char not in '.SE':
                continue
            grid.add((x, y))
            if char == 'S':
                start = x, y
            elif char == 'E':
                stop = x, y

    return grid, start, stop


def find_best_path(grid, start, stop):
    queue = [(0, start, (1, 0))]
    seen = {}

    while queue:
        score, (x, y), (dx, dy) = heapq.heappop(queue)
        if (x, y) == stop:
            return score

        for ndx, ndy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            np = x + ndx, y + ndy
            s = score + 1 + (0 if (ndx, ndy) == (dx, dy) else 1000)
            if np in grid and (np not in seen or s < seen[np]):
                seen[np] = s
                heapq.heappush(queue, (s, np, (ndx, ndy)))


if __name__ == '__main__':
    print(find_best_path(*parse_map(sys.stdin)))
