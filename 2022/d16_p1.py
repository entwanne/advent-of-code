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


def find_max_path(graph, open=set(), current=('AA', 30, 0, 0)):
    name, n, value, inc = current
    if n == 0:
        return value

    node = graph[name]
    children = []

    if name not in open:
        children.append(find_max_path(graph, open | {name}, (name, n-1, value+inc, inc+node['rate'])))

    for name_next in node['nexts']:
        children.append(find_max_path(graph, open, (name_next, n-1, value+inc, inc)))

    return max(children)


graph = {valve['name']: valve for valve in parse(sys.stdin)}
print(graph)
print(find_max_path(graph))
