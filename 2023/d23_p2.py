import heapq
import sys

from d23_p1 import CHARS, parse_map


CHARS['<'] = CHARS['>'] = CHARS['^'] = CHARS['v'] = CHARS['.']


def normalize_map(grid):
    return {
        (x, y): {
            p
            for dx, dy in directions
            if (p := (x + dx, y + dy)) in grid
        }
        for (x, y), directions in grid.items()
    }


def simplify_map(grid):
    start = min(grid, key=lambda p: p[1])
    reach = max(grid, key=lambda p: p[1])

    sgrid = {}
    seen = {start}

    queue = [(start, start, 0)]

    while queue:
        node_src, node_dst, length = queue.pop(0)
        prev_node = node_src

        while len(grid[node_dst]) <= 2:
            nodes = grid[node_dst] - {prev_node}
            if not nodes:
                break
            prev_node = node_dst
            node_dst, = nodes
            length += 1

        sgrid.setdefault(node_src, {})[node_dst] = length
        for next_node in grid[node_dst] - {prev_node}:
            if next_node not in seen:
                queue.append((node_dst, next_node, 1))
                seen.add(next_node)

    sgrid[reach] = {}
    return sgrid


def find_longest_path(grid):
    start = min(grid, key=lambda p: p[1])
    reach = max(grid, key=lambda p: p[1])
    queue = [(0, start, {start})]

    max_dist = 0

    while queue:
        total_dist, (x, y), seen = heapq.heappop(queue)
        for np, dist in grid[x, y].items():
            if np == reach:
                if -total_dist + dist > max_dist:
                    max_dist = -total_dist + dist
                    print(max_dist)
                continue
            if np not in grid or np in seen:
                continue
            heapq.heappush(queue, (total_dist - dist, np, seen | {np}))

    return max_dist


if __name__ == '__main__':
    print(find_longest_path(simplify_map(normalize_map(parse_map(sys.stdin)))))
