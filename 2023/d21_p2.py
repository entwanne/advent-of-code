import sys


'''
class InfiniteMap:
    def __init__(self, cells, width, height):
        self.cells = cells
        self.width = width
        self.height = height

    def __contains__(self, p):
        x, y = p
        return (x % self.width, y % self.height) in self.cells
'''


def parse_map(f):
    cells = {
        pos
        for y, line in enumerate(f)
        for x, char in enumerate(line.strip())
        if (pos := (x, y)) and (char == '.' or (char == 'S' and (start := pos)))
    }
    xmax, ymax = pos
    return start, (xmax + 1, ymax + 1), cells


def walk(cells, dims, points):
    """
    return {
        p: maps
        for ((x, y), maps) in points.items()
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1))
        if (p := (x + dx, y + dy)) in cells
    }
    """
    next_points = {}
    width, height = dims
    for (x, y), maps in points.items():
        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            mdx, nx = divmod(x + dx, width)
            mdy, ny = divmod(y + dy, height)
            if (nx, ny) in cells:
                next_points.setdefault((nx, ny), set()).update((mx+mdx, my+mdy) for mx, my in maps)

    return next_points


def walkn(cells, dims, starting_points, n):
    points = starting_points
    #sig = tuple(sorted(((p, tuple(sorted(maps))) for p, maps in points.items())))
    #memory = {sig: 0}

    for i in range(1, n + 1):
        #print(i, len(memory))
        points = walk(cells, dims, points)
        #sig = tuple(sorted(((p, tuple(sorted(maps))) for p, maps in points.items())))
        #if sig in memory:
        #    #print(memory[points])
        #    #break
        #    print('!!!!')
        #memory[sig] = i

    return points


if __name__ == '__main__':
    start, dims, cells = parse_map(sys.stdin)
    #cells = InfiniteMap(cells, width, height)
    #print(len(walkn(cells, frozenset({start}), 26501365)))
    for n in (6, 10, 50, 100, 500, 1000, 5000):
        #for n in [500]:
        points = walkn(cells, dims, {start: {(0, 0)}}, n)
        print(n, len(points), sum(len(v) for v in points.values()))
