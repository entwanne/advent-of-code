import heapq
import sys


def parse_heats(f):
    return {
        (x, y): int(heat)
        for y, line in enumerate(f)
        for x, heat in enumerate(line.strip())
    }


def find_best_path(heats):
    start = min(heats)
    end = max(heats)

    queue = [(0, start, (1, 0), 3), (0, start, (0, 1), 3)]
    seen = {start}

    while queue:
        total, (x, y), (dx, dy), remaining = heapq.heappop(queue)
        if (x, y) == end:
            return total

        directions = [(dx, dy), (dy, -dx), (-dy, dx)]

        for ndx, ndy in directions:
            if (ndx, ndy) == (dx, dy):
                r = remaining - 1
            else:
                r = 3
            if r <= 0:
                continue

            nx, ny = x + ndx, y + ndy
            heat = heats.get((nx, ny))
            if heat is None:
                continue
            if (nx, ny, ndx, ndy, r) not in seen:
                seen.add((nx, ny, ndx, ndy, r))
                heapq.heappush(queue, (total + heat, (nx, ny), (ndx, ndy), r))


if __name__ == '__main__':
    print(find_best_path(parse_heats(sys.stdin)))
