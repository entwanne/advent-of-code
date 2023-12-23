import re
import sys

pattern = re.compile(r'Valve (?P<name>.+) has flow rate=(?P<rate>\d+); tunnels? leads? to valves? (?P<nexts>.+)')


def parse(f):
    for line in f:
        m = pattern.match(line)
        yield {
            'name': m['name'],
            'rate': int(m['rate']),
            'nexts': m['nexts'].split(', '),
        }


def compute_distances(graph, start):
    distances = {}
    nexts = [(start, 0)]
    seen = {start}

    while nexts:
        name, dist = nexts.pop(0)
        distances[name] = dist

        node = graph[name]
        for link in node['nexts']:
            if link not in seen:
                nexts.append((link, dist+1))
                seen.add(link)

    del distances[start]
    return distances


def compute_all_distances(graph):
    return {
        name: compute_distances(graph, name)
        for name in graph
    }


def find_best_path(graph, start='AA'):
    distances = compute_all_distances(graph)
    toopen = {name for name, node in graph.items() if node['rate'] > 0}
    nexts = [(start, set(), 30, 0, 0)]

    while nexts:
        name, opened, n, value, inc = nexts.pop(0)

        yield value + n * inc

        if n == 0:
            continue

        if name not in opened and name in toopen:
            node = graph[name]
            nexts.append((name, opened | {name}, n-1, value+inc, inc+node['rate']))
        for link, dist in distances[name].items():
            if link not in opened and link in toopen and dist <= n:
                node = graph[link]
                dist += 1
                nexts.append((link, opened | {link}, n-dist, value+dist*inc, inc+node['rate']))


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(max(find_best_path(graph)))
