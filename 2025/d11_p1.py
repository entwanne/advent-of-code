import sys


def parse_graph(f):
    graph = {}

    for line in f:
        input, outputs = line.strip().split(': ')
        graph[input] = outputs.split()

    return graph


def find_all_paths(graph, start, end):
    queue = [(start,)]
    seen = set(queue)

    while queue:
        path = queue.pop(0)
        if path[-1] == end:
            yield path

        for node in graph.get(path[-1], ()):
            p = (*path, node)
            if p not in seen:
                seen.add(p)
                queue.append(p)


if __name__ == '__main__':
    print(len(list(find_all_paths(parse_graph(sys.stdin), 'you', 'out'))))
