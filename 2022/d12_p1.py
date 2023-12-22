import string
import sys


def parse(f):
    start = end = None
    grid = {}
    for y, line in enumerate(f):
        for x, char in enumerate(line.strip()):
            if char == 'S':
                start = (x, y)
                grid[x, y] = 0
            elif char == 'E':
                end = (x, y)
                grid[x, y] = 25
            else:
                grid[x, y] = string.ascii_lowercase.index(char)

    return start, end, grid


start, end, grid = parse(sys.stdin)
nexts = [(start, 0)]
seen = {start}

while nexts:
    pos, n = nexts.pop(0)
    if pos == end:
        print(n)
        break
    for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        new = pos[0]+dx, pos[1]+dy
        if new in grid and new not in seen and grid[new] <= grid[pos] + 1:
            seen.add(new)
            nexts.append((new, n+1))
