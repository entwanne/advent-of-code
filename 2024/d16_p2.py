import heapq
import sys

from d16_p1 import parse_map


def best_path_cells(grid, start, stop):
    best_score = None
    best_cells = set()
    queue = [(0, start, (1, 0), {start})]
    gseen = {start: 0}

    while queue:
        score, (x, y), (dx, dy), seen = heapq.heappop(queue)
        if (x, y) == stop:
            if best_score is None or score == best_score:
                best_score = score
                best_cells.update(seen)
            else:
                break

        for ndx, ndy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            np = x + ndx, y + ndy
            s = score + 1 + (0 if (ndx, ndy) == (dx, dy) else 1000)
            if np in grid and (np not in gseen or s <= gseen[np] + 1000) and np not in seen:
                gseen[np] = s
                heapq.heappush(queue, (s, np, (ndx, ndy), seen | {np}))

    return best_cells


if __name__ == '__main__':
    print(len(best_path_cells(*parse_map(sys.stdin))))
