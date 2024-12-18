import heapq
import itertools
import sys


WIDTH = HEIGHT = 71
N = 1024
CELLS = frozenset(itertools.product(range(WIDTH), range(HEIGHT)))


def parse_blocks(f, n=None):
    if n is not None:
        f = itertools.islice(f, n)
    return [tuple(map(int, line.split(','))) for line in f]


def parse_grid(blocks):
    return CELLS - set(blocks)


def best_path_length(grid):
    start = min(grid)
    stop = max(grid)

    queue = [(0, start)]
    seen = {start}

    while queue:
        length, node = heapq.heappop(queue)
        if node == stop:
            return length

        x, y = node
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            np = x + dx, y + dy
            if np in grid and np not in seen:
                seen.add(np)
                heapq.heappush(queue, (length + 1, np))


if __name__ == '__main__':
    print(best_path_length(parse_grid(parse_blocks(sys.stdin, N))))
