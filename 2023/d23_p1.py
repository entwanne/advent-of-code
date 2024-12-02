import heapq
import sys


CHARS = {
    '.': [(-1, 0), (1, 0), (0, -1), (0, 1)],
    '<': [(-1, 0)],
    '>': [(1, 0)],
    '^': [(0, -1)],
    'v': [(0, 1)],
}


def parse_map(f):
    return {
        (x, y): CHARS[char]
        for y, line in enumerate(f)
        for x, char in enumerate(line)
        if char in CHARS
    }


def find_longest_path(grid):
    start = min(grid, key=lambda p: p[1])
    reach = max(grid, key=lambda p: p[1])
    queue = [(0, start, {start})]

    max_dist = 0

    while queue:
        dist, (x, y), seen = heapq.heappop(queue)
        for dx, dy in grid[x, y]:
            np = x + dx, y + dy
            if np == reach:
                max_dist = max(max_dist, -dist + 1)
                continue
            if np not in grid or np in seen:
                continue
            heapq.heappush(queue, (dist - 1, np, seen | {np}))

    return max_dist


if __name__ == '__main__':
    print(find_longest_path(parse_map(sys.stdin)))
