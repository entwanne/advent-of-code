import sys
from typing import NamedTuple


class Position(NamedTuple):
    x: int
    y: int


directions = {
    'L': (-1, 0),
    'R': (1, 0),
    'U': (0, -1),
    'D': (0, 1),
}


def parse(f):
    for line in f:
        d, n = line.split()
        for _ in range(int(n)):
            yield directions[d]


def print_grid():
    grid = seen | {head}
    xmin = min(x for x, _ in grid)
    xmax = max(x for x, _ in grid)
    ymin = min(y for _, y in grid)
    ymax = max(y for _, y in grid)

    chars = {p: '#' for p in seen}
    chars |= {
        (0, 0): 's',
        tail: 'T',
        head: 'H',
    }

    print('-'*10)
    for y in range(ymin, ymax+1):
        print(''.join(
            chars.get((x, y), '.')
            for x in range(xmin, xmax+1)
        ))
            


head = tail = Position(0, 0)
seen = {tail}
#print_grid()
        

for dx, dy in parse(sys.stdin):
    head = Position(head.x + dx, head.y + dy)

    if abs(tail.x - head.x) > 1 or abs(tail.y - head.y) > 1:
        tdx = 0 if head.x == tail.x else 1 if head.x > tail.x else -1
        tdy = 0 if head.y == tail.y else 1 if head.y > tail.y else -1
        tail = Position(tail.x + tdx, tail.y + tdy)

    seen.add(tail)
    #print_grid()

print(len(seen))
