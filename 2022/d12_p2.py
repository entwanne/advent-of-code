import string
import sys


def parse(f):
    end = None
    grid = {}
    for y, line in enumerate(f):
        for x, char in enumerate(line.strip()):
            if char == 'S':
                grid[x, y] = 0
            elif char == 'E':
                end = (x, y)
                grid[x, y] = 25
            else:
                grid[x, y] = string.ascii_lowercase.index(char)

    return end, grid


end, grid = parse(sys.stdin)
starts = {pos for pos, level in grid.items() if level == 0}
nexts = [(start, 0) for start in starts]
seen = starts

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
