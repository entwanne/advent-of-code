import sys


CHARS = {
    '.': lambda x, y, dx, dy: [(x+dx, y+dy, dx, dy)],
    '|': lambda x, y, dx, dy: [(x, y-1, 0, -1), (x, y+1, 0, 1)],
    '-': lambda x, y, dx, dy: [(x-1, y, -1, 0), (x+1, y, 1, 0)],
    '/': lambda x, y, dx, dy: [(x-dy, y-dx, -dy, -dx)],
    '\\': lambda x, y, dx, dy: [(x+dy, y+dx, dy, dx)],
}


def parse_map(f):
    return {
        (x, y): CHARS[char]
        for y, line in enumerate(f)
        for x, char in enumerate(line.strip())
    }


def energized(cells, start=(0, 0, 1, 0)):
    seen = {start}
    queue = [start]

    while queue:
        x, y, dx, dy = queue.pop(0)
        new = cells[x, y](x, y, dx, dy)
        for x, y, dx, dy in new:
            if (x, y) in cells and (x, y, dx, dy) not in seen:
                queue.append((x, y, dx, dy))
                seen.add((x, y, dx, dy))

    return {(x, y) for (x, y, dx, dy) in seen}


if __name__ == '__main__':
    print(len(energized(parse_map(sys.stdin))))
