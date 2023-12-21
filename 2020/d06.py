import sys
from functools import reduce

groups = sys.stdin.read().split('\n\n')
groups = [[p for p in g.split('\n') if p] for g in groups]

# p1

print(sum(len(set(x for p in g for x in p)) for g in groups))

# p2

groups = [[set(p) for p in g] for g in groups]
print(sum(len(reduce(set.intersection, g)) for g in groups))
