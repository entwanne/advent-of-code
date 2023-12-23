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
    nexts = {0: [(start, start, frozenset(), 26, 26, 0, 0, 0, 0)]}
    seen = set(nexts[0])

    while nexts:
        v = max(nexts)
        name1, name2, opened, n1, n2, value1, value2, inc1, inc2 = nexts[v].pop(0)
        if not nexts[v]:
            del nexts[v]

        yield value1 + n1 * inc1 + value2 + n2 * inc2

        if n1 == n2 == 0:
            continue

        if opened == toopen:
            continue

        for link1, dist1 in distances[name1].items():
            if link1 not in opened and link1 in toopen and dist1 <= n1:
                node1 = graph[link1]
                dist1 += 1
                new = (link1, name2, opened | {link1}, n1-dist1, n2, value1+dist1*inc1, value2, inc1+node1['rate'], inc2)
                if new not in seen:
                    nexts.setdefault(value1+dist1*inc1+(n1-dist1)*(inc1+node1['rate'])+value2+n2*inc2, []).append(new)
                    seen.add(new)

        for link2, dist2 in distances[name2].items():
            if link2 not in opened and link2 in toopen and dist2 <= n2:
                node2 = graph[link2]
                dist2 += 1
                new = (name1, link2, opened | {link2}, n1, n2-dist2, value1, value2+dist2*inc2, inc1, inc2+node2['rate'])
                if new not in seen:
                    nexts.setdefault(value1+n1*inc1+value2+dist2*inc2+(n2-dist2)*(inc2+node2['rate']), []).append(new)
                    seen.add(new)


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(max(find_best_path(graph)))
