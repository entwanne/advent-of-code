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
    #nexts = [(start, start, frozenset(), 26, 26, 0, 0, 0, 0)]
    nexts = [(start, start, set(), 26, 26, 0, 0, 0, 0)]
    #seen = set(nexts)

    while nexts:
        name1, name2, opened, n1, n2, value1, value2, inc1, inc2 = nexts.pop(0)

        yield value1 + n1 * inc1 + value2 + n2 * inc2

        if n1 <= 0 and n2 <= 0:
            continue

        for link in toopen - opened:
            dist1, dist2 = distances[name1][link], distances[name2][link]
            node = graph[link]
            new = None
            if dist1 <= dist2 and dist1 <= n1:
                dist1 += 1
                new = (link, name2, opened | {link}, n1-dist1, n2, value1+dist1*inc1, value2, inc1+node['rate'], inc2)
            elif dist2 <= n2:
                dist2 += 1
                new = (name1, link, opened | {link}, n1, n2-dist2, value1, value2+dist2*inc2, inc1, inc2+node['rate'])
            if new: #and new not in seen:
                nexts.append(new)
                #seen.add(new)


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(max(find_best_path(graph)))
