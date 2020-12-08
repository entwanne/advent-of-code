import re
import sys

rules = [line.strip() for line in sys.stdin]

graph_p1 = {}
graph_p2 = {}

for rule in rules:
    m = re.match(r'(.+) bags contain (.+)\.$', rule)

    kind, contain = m.groups()
    if contain == 'no other bags':
        continue

    graph_p2[kind] = {}

    for c in contain.split(', '):
        m = re.match(r'(\d+) (.+) bags?', c)
        n, k = m.groups()
        graph_p1.setdefault(k, set()).add(kind)
        graph_p2[kind][k] = int(n)


def find_parents(key):
    parents = graph_p1.get(key, [])
    all_parents = set(parents)
    for p in parents:
        all_parents |= find_parents(p)
    return all_parents


def count_children(key):
    total = 0
    for child, n in graph_p2.get(key, {}).items():
        total += (1 + count_children(child)) * n
    return total

print(len(find_parents('shiny gold')))
print(count_children('shiny gold'))
