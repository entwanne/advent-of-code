import re
import sys
from itertools import cycle

DIRS = {'L': 0, 'R': 1}
START = 'AAA'
END = 'ZZZ'


def parse(f):
    directions = [DIRS[c] for c in f.readline().strip()]
    assert f.readline().strip() == ''
    blocks = {}
    for line in f:
        m = re.fullmatch(r'(\w+) = \((\w+), (\w+)\)', line.strip())
        blocks[m[1]] = (m[2], m[3])
    return directions, blocks


def walk(directions, blocks):
    directions = cycle(directions)
    n = 0
    node = START
    while node != END:
        node = blocks[node][next(directions)]
        n += 1
    return n


if __name__ == '__main__':
    print(walk(*parse(sys.stdin)))
