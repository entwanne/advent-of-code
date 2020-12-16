import operator
import sys
from functools import reduce

class multirange:
    def __init__(self, ranges):
        self.ranges = list(ranges)

    def __contains__(self, value):
        return any(value in r for r in self.ranges)

    def __repr__(self):
        return f'{self.__class__.__name__}({self.ranges!r})'


def parse_range(r):
    a, b = r.split('-')
    return range(int(a), int(b)+1)


def parse_multirange(m):
    return multirange(parse_range(r) for r in m.split(' or '))


rules, ticket, nearby = sys.stdin.read().split('\n\n')

rules = [line.split(': ') for line in rules.splitlines()]
rules = {name: parse_multirange(value) for name, value in rules}

ticket = [int(v) for v in ticket.splitlines()[1].split(',')]
nearby = [[int(v) for v in line.split(',')] for line in nearby.splitlines()[1:]]


# p1

tot = 0
discard = set()
for i, t in enumerate(nearby):
    for v in t:
        if not any(v in rule for rule in rules.values()):
            tot += v
            discard.add(i)

print(tot)
nearby = [t for i, t in enumerate(nearby) if i not in discard]


# p2

rulesets = {name: set(range(len(rules))) for name in rules}

for t in nearby:
    for i, v in enumerate(t):
        for name, rule in rules.items():
            if v not in rule:
                rulesets[name].remove(i)

fields = {}
while rulesets:
    name, ruleset = min(rulesets.items(), key=lambda x: len(x[1]))
    del rulesets[name]
    value, = ruleset
    for r in rulesets.values():
        r.remove(value)
    fields[name] = value

indices = [i for name, i in fields.items() if name.startswith('departure')]
print(reduce(operator.mul, (ticket[i] for i in indices)))
