import heapq
import sys


def parse_map(f):
    cells = set()
    start = end = None

    for y, line in enumerate(f):
        for x, char in enumerate(line):
            if char in 'SE.':
                cells.add((x, y))
            if char == 'S':
                start = x, y
            elif char == 'E':
                end = x, y

    return start, end, cells


DIRECTIONS = ((-1, 0), (1, 0), (0, -1), (0, 1))


def count_distances(cells, reach):
    distances = {reach: 0}
    queue = [(0, reach)]

    while queue:
        dist, (x, y) = queue.pop(0)

        for dx, dy in DIRECTIONS:
            np = x + dx, y + dy
            if np in cells and np not in distances:
                distances[np] = dist + 1
                queue.append((dist + 1, np))

    return distances


def count_cheats(distances, start, threashold=1):
    queue = [start]
    seen = {start}
    cheats = 0

    while queue:
        x, y = queue.pop(0)

        for dx, dy in DIRECTIONS:
            np = x + dx, y + dy
            if np in distances:
                if np not in seen:
                    seen.add(np)
                    queue.append(np)
            else: # cheat
                nx, ny = np
                for dx, dy in DIRECTIONS:
                    np = nx + dx, ny + dy
                    if np not in distances:
                        continue
                    save = distances[x, y] - 2 - distances[np]
                    if save >= threashold:
                        cheats += 1

    return cheats


if __name__ == '__main__':
    start, end, cells = parse_map(sys.stdin)
    distances = count_distances(cells, end)
    print(count_cheats(distances, start, 100))
