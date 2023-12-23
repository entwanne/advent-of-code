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
    seen = set(nexts[0])

    while nexts:
        v = max(nexts)
        q = nexts[v]
        name, open, n, value, inc = q.pop(0)
        if not q:
            del nexts[v]

        #print(n)
        if n == 0:
            #print(value)
            #break
            yield value
            continue

        node = graph[name]
        children = []

        if name not in open:
            v = inc + node['rate']
            new = (name, open | {name}, n-1, value+inc, inc+node['rate'])
            if new not in seen:
                nexts.setdefault(v, []).append(new)
                seen.add(new)

        for name_next in node['nexts']:
            v = inc
            new = (name_next, open, n-1, value+inc, inc)
            if new not in seen:
                nexts.setdefault(v, []).append(new)
                seen.add(new)

    #return max(children)


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(graph)
print(max(find_max_path(graph)))
