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
    nexts = [('AA', set(), 30, 0, 0)]

    while nexts:
        name, open, n, value, inc = nexts.pop(0)
        print(n)
        if n == 0:
            print(value)
            continue

        node = graph[name]
        children = []

        if name not in open:
            nexts.append((name, open | {name}, n-1, value+inc, inc+node['rate']))

        for name_next in node['nexts']:
            nexts.append((name_next, open, n-1, value+inc, inc))
            #children.append(find_max_path(graph, open, (name_next, n-1, value+inc, inc)))

    #return max(children)


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(graph)
print(find_max_path(graph))
