from d14_p1 import parse_file as base_parse_file, load

import sys


def parse_file(f):
    blocks = base_parse_file(f)

    xmin = min(x for x, _ in blocks)
    xmax = max(x for x, _ in blocks)
    ymin = 1
    ymax = max(y for _, y in blocks)

    for x in range(xmin, xmax + 1):
        blocks[x, ymin - 1] = '#'

    for y in range(ymin, ymax + 1):
        blocks[xmin - 1, y] = '#'
        blocks[xmax + 1, y] = '#'

    return blocks


def slide(blocks, direction):
    dx, dy = direction

    rocks = [pos for pos, char in blocks.items() if char == 'O']
    #rocks.sort(key=lambda rock: -rock[1])
    rocks.sort(key=lambda rock: (-dx * rock[0], -dy * rock[1]))

    for x, y in rocks:
        del blocks[x, y]
        while (x + dx, y + dy) not in blocks:
            x += dx
            y += dy
        blocks[x, y] = 'O'

    return blocks


def cycle(blocks):
    for direction in ((0, 1), (-1, 0), (0, -1), (1, 0)):
        blocks = slide(blocks, direction)
    return blocks


def ncycles(blocks, n):
    seen = {tuple(sorted(blocks.items())): 0}
    cycle_size = 0
    start = 0

    for i in range(1, n+1):
        blocks = cycle(blocks)
        sig = tuple(sorted(blocks.items()))
        if sig in seen:
            start = seen[sig]
            cycle_size = i - start
            break
        seen[sig] = i

    if cycle_size:
        remaining = n - i
        pos = start + remaining % cycle_size
        return dict(next(sig for sig, i in seen.items() if i == pos))

    return blocks


def debug(blocks):
    xmin = 0
    ymin = 1
    xmax = max(x for x, _ in blocks) - 1
    ymax = max(y for _, y in blocks) - 1
    print('=' * ymax)
    for y in range(ymax, ymin - 1, -1):
        print(''.join(blocks.get((x, y), '.') for x in range(xmin, xmax + 1)))


if __name__ == '__main__':
    print(load(ncycles(parse_file(sys.stdin), 1000000000)))
