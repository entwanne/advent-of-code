import sys


def parse_file(f):
    blocks = {}

    lines = f.readlines()
    for y, line in enumerate(reversed(lines), start=1):
        for x, char in enumerate(line):
            if char in {'O', '#'}:
                blocks[x, y] = char

    xmin = min(x for x, _ in blocks)
    xmax = max(x for x, _ in blocks)
    for x in range(xmin, xmax + 1):
        blocks[x, y + 1] = '#'

    return blocks


def slide(blocks):
    rocks = [pos for pos, char in blocks.items() if char == 'O']
    rocks.sort(key=lambda rock: -rock[1])

    for x, y in rocks:
        del blocks[x, y]
        while (x, y + 1) not in blocks:
            y += 1
        blocks[x, y] = 'O'

    return blocks


def load(blocks):
    return sum(y for (_, y), char in blocks.items() if char == 'O')


if __name__ == '__main__':
    print(load(slide(parse_file(sys.stdin))))
