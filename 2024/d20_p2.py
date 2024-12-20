import itertools
import sys

from d20_p1 import DIRECTIONS, parse_map, count_distances


def find_cheats(distances, start, threashold=1):
    queue = [start]
    seen = {start}
    cheats = set()

    while queue:
        x, y = queue.pop(0)

        for dx, dy in DIRECTIONS:
            np = x + dx, y + dy
            if np in distances:
                if np not in seen:
                    seen.add(np)
                    queue.append(np)

        # cheat
        for dx, dy in itertools.product(range(-20, 21), repeat=2):
            d = abs(dx) + abs(dy)
            if d > 20:
                continue

            np = x + dx, y + dy
            if np not in distances:
                continue

            save = distances[x, y] - d - distances[np]
            if save >= threashold:
                cheats.add((x, y, *np))

    return cheats


if __name__ == '__main__':
    start, end, cells = parse_map(sys.stdin)
    distances = count_distances(cells, end)
    print(len(find_cheats(distances, start, 100)))
