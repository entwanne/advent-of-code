import heapq
import sys


def parse_connections(f):
    graph = {}

    for line in f:
        name, connections = line.split(': ')
        connections = connections.split()
        graph.setdefault(name, set())
        for c in connections:
            graph[name].add(c)
            graph.setdefault(c, set()).add(name)

    return graph


def get_edges(graph):
    return {
        frozenset({node1, node2})
        for node1, children in graph.items()
        for node2 in children
    }


def get_node_distances(graph, node):
    distances = {}
    queue = [(0, node)]

    while queue:
        dist, node = heapq.heappop(queue)
        if node in distances:
            continue
        distances[node] = dist

        for child in graph[node]:
            if child not in distances:
                queue.append((dist + 1, child))

    return distances


def to_dot(graph):
    lines = ['graph {']
    for node1, node2 in get_edges(graph):
        lines.append(f'{node1} -- {node2}')
    lines.append('}')
    return '\n'.join(lines)


def find_lowest_edge(graph):
    edges = get_edges(graph)
    nodes_distances = {
        node: get_node_distances(graph, node)
        for node in graph
    }
    edges_distances = {
        frozenset({n1, n2}): {
            n3: min(nodes_distances[n1][n3], nodes_distances[n2][n3])
            for n3 in graph
        }
        for n1, n2 in edges
    }

    total_distances = {edge: sum(dists.values()) for edge, dists in edges_distances.items()}

    #for edge, dist in sorted(distances.items(), key=lambda p: p[1]):
    #    print(edge, dist)

    return min(total_distances.items(), key=lambda p: p[1])[0]


if __name__ == '__main__':
    graph = parse_connections(sys.stdin)

    for _ in range(3):
        edge = find_lowest_edge(graph)
        print('Cutting', edge)
        n1, n2 = edge
        graph[n1].discard(n2)
        graph[n2].discard(n1)

    left_size = len(get_node_distances(graph, n1))
    right_size = len(graph) - left_size
    assert right_size > 0
    print(left_size * right_size)
