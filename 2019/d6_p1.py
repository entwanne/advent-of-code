import sys


parents = {}


def count_level(key):
    n = 0
    while key in parents:
        n += 1
        key = parents[key]
    return n


for line in sys.stdin:
    left, right = line.strip().split(')')
    parents[right] = left


print(sum(count_level(k) for k in parents.keys()))
