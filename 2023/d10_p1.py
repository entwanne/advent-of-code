import sys

NORTH = (0, -1)
SOUTH = (0, 1)
WEST = (-1, 0)
EAST = (1, 0)
CHARS = {
    '|': {NORTH, SOUTH},
    '-': {WEST, EAST},
    'L': {NORTH, EAST},
    'J': {NORTH, WEST},
    '7': {SOUTH, WEST},
    'F': {SOUTH, EAST},
    'S': {NORTH, SOUTH, WEST, EAST},
}


def parse_cases(f):
    return {
        (x, y): CHARS[char]
        for y, line in enumerate(sys.stdin)
        for x, char in enumerate(line.strip())
        if char in CHARS
    }


def parse_graph(cases):
    start = None
    graph = {}

    for (x, y), directions in cases.items():
        if len(directions) == 4:
            start = (x, y)
        node = graph.setdefault((x, y), [])

        for dx, dy in directions:
            x2, y2 = x + dx, y + dy
            if (x2, y2) in cases and (-dx, -dy) in cases[x2, y2]:
                node.append((x2, y2))

    return graph, start


def count_distances(graph, start):
    distances = {}
    queue = [(start, 0)]
    seen = {start}

    while queue:
        node, dist = queue.pop(0)
        if node in distances:
            continue
        distances[node] = dist
        for next_node in graph[node]:
            if next_node not in seen:
                queue.append((next_node, dist + 1))
                seen.add(next_node)

    return distances


if __name__ == '__main__':
    print(max(count_distances(*parse_graph(parse_cases(sys.stdin))).values()))
