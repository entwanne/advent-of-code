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


def print_grid(with_snake=True, with_seen=False):
    grid = seen | set(snake)
    xmin = min(x for x, _ in grid)
    xmax = max(x for x, _ in grid)
    ymin = min(y for _, y in grid)
    ymax = max(y for _, y in grid)

    chars = {}
    if with_seen:
        chars |= {p: '#' for p in seen}

    chars[0, 0] = 's'

    if with_snake:
        head, *tail = snake
        for i, pos in reversed(list(enumerate(tail))):
            chars[pos] = str(i+1)
        chars[head] = 'H'

    print('-'*10)
    for y in range(ymin, ymax+1):
        print(''.join(
            chars.get((x, y), '.')
            for x in range(xmin, xmax+1)
        ))
            


snake = [Position(0, 0) for _ in range(10)]
seen = {snake[-1]}
#print_grid()
        

for dx, dy in parse(sys.stdin):
    snake[0] = Position(snake[0].x + dx, snake[0].y + dy)

    for i, tail in enumerate(snake[1:], 1):
        head = snake[i-1]
        if abs(tail.x - head.x) > 1 or abs(tail.y - head.y) > 1:
            tdx = 0 if head.x == tail.x else 1 if head.x > tail.x else -1
            tdy = 0 if head.y == tail.y else 1 if head.y > tail.y else -1
            snake[i] = Position(tail.x + tdx, tail.y + tdy)

    seen.add(snake[-1])
    #print_grid()


#print_grid(with_snake=False, with_seen=True)
print(len(seen))
