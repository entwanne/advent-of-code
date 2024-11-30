import math
import sys
from itertools import cycle

from d08_p1 import parse


def count(directions, blocks, node):
    directions = cycle(directions)
    lastn = 0
    for n in range(100_000):
        if node.endswith('Z'):
            yield n - lastn
            lastn = n
        node = blocks[node][next(directions)]


def walk(directions, blocks):
    nodes = [node for node in blocks if node.endswith('A')]
    counts = [list(count(directions, blocks, node)) for node in nodes]
    for c in counts:
        assert len(set(c)) == 1

    counts = [c[0] for c in counts]
    return math.lcm(*counts)


if __name__ == '__main__':
    print(walk(*parse(sys.stdin)))
