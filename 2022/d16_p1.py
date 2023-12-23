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


def find_max_path(graph):
    nexts = {0: [('AA', frozenset(), 30, 0, 0)]}
    seen = {('AA', frozenset(), 0, 0)}

    while nexts:
        v = max(nexts)
        q = nexts[v]
        name, open, n, value, inc = q.pop(0)
        if not q:
            del nexts[v]
        #print(name, open, n, value, inc)

        #print(n)
        if n == 0:
            #print(value)
            #break
            print(name, open)
            yield value
            continue

        node = graph[name]
        children = []

        if name not in open and node['rate']:
            key = (name, open | {name}, value+inc, inc+node['rate'])
            p = (value+inc) * n
            if key not in seen:
                nexts.setdefault(p, []).append((name, open | {name}, n-1, value+inc, inc+node['rate']))
                seen.add(key)

        for name_next in node['nexts']:
            key = (name_next, open, value+inc, inc)
            p = (value+inc) * n
            if key not in seen:
                nexts.setdefault(p, []).append((name_next, open, n-1, value+inc, inc))
                seen.add(key)

    #return max(children)


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
    nexts = [('AA', set(), 30, 0, 0)]

    while nexts:
        name, opened, n, value, inc = nexts.pop(0)

        if n == 0:
            yield value
            continue

        #if opened == toopen:
        #    value += n * inc
        #    yield value
        #    continue
        yield value + n * inc

        if name not in opened and name in toopen:
            node = graph[name]
            nexts.append((name, opened | {name}, n-1, value+inc, inc+node['rate']))
        for link, dist in distances[name].items():
            if link not in opened and link in toopen and dist <= n:
                node = graph[link]
                dist += 1
                nexts.append((link, opened | {link}, n-dist, value+dist*inc, inc+node['rate']))
                #nexts.append((link, opened, n-dist, value+dist*inc, inc))


graph = {valve['name']: valve for valve in parse(sys.stdin)}
#print(graph)
#print(max(find_max_path(graph)))
'''
n = 0
for v in find_max_path(graph):
    print(v)
    n += 1
    if n == 20:
        break
'''
#for p in find_best_path(graph):
#    print(p)
print(max(find_best_path(graph)))
