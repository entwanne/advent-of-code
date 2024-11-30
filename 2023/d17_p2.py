import heapq
import sys

from d17_p1 import parse_heats


def find_best_path(heats):
    start = min(heats)
    end = max(heats)

    queue = [(0, start, (0, 0), 0)]
    seen = {start}

    while queue:
        total, (x, y), (dx, dy), remaining = heapq.heappop(queue)
        if (x, y) == end:
            return total

        if (dx, dy) == (0, 0):
            directions = [(1, 0), (0, 1)]
        else:
            directions = [(dx, dy), (dy, -dx), (-dy, dx)]

        for ndx, ndy in directions:
            if (ndx, ndy) == (dx, dy):
                r = remaining - 1
                loop = 1
            else:
                r = 7
                loop = 4
            if r <= 0:
                continue

            out = False
            t = total
            nx, ny = x, y

            for _ in range(loop):
                nx, ny = nx + ndx, ny + ndy
                heat = heats.get((nx, ny))
                if heat is None:
                    out = True
                    break
                t += heat

            if out:
                continue

            if (nx, ny, ndx, ndy, r) not in seen:
                seen.add((nx, ny, ndx, ndy, r))
                heapq.heappush(queue, (t, (nx, ny), (ndx, ndy), r))


if __name__ == '__main__':
    print(find_best_path(parse_heats(sys.stdin)))
