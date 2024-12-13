import math
import sys

from d17_p1 import PIECES, WIDTH, size, parse_directions, cycle


def parse_directions(f):
    s = f.read().strip()
    return len(s), cycle(-1 if c == '<' else 1 for c in s)


def fall(blocks, directions, piece):
    sx, sy = 2, 3 + size(blocks)
    piece = {(x + sx, y + sy) for x, y in piece}

    while True:
        # Jet move
        dx = next(directions)
        npiece = {(x + dx, y) for x, y in piece}
        if all(0 <= x < WIDTH for x, _ in npiece) and not blocks & npiece:
            piece = npiece

        # Gravity move
        npiece = {(x, y - 1) for x, y in piece}
        if any(y < 0 for _, y in npiece) or blocks & npiece:
            break
        piece = npiece

    #x = min(x for x, _ in piece)
    #y = min(y for _, y in piece) - size(blocks)
    blocks.update(piece)
    #return x, y
    ys = [max((y for x2, y in blocks if x2 == x), default=-1) for x in range(WIDTH)]
    ymax = max(ys)
    return tuple(ymax - y for y in ys)


def simulation(n, cycle_size, directions):
    blocks = set()
    pieces = cycle(PIECES)

    seen = {}
    sizes = {}

    for i in range(n):
        p = fall(blocks, directions, next(pieces))
        sizes[i] = size(blocks)
        if i % cycle_size == 0:
            #print(p)
            if p in seen:
                cycle_range = i - seen[p]
                cycle_size = sizes[i] - sizes[seen[p]]
                print('!!!', seen[p], sizes[seen[p]], i, sizes[i])
                break
            seen[p] = i

    print(cycle_range, cycle_size)
    k = (n - i) // cycle_range
    r = n - (i + cycle_range * k)
    #print(i, n, k, r)
    #return blocks
    #print(i + k * cycle_range + r)
    #print(sizes[seen[p] + r], sizes[seen[p]])
    return sizes[i] + k * cycle_size + (sizes[seen[p] + r - 1] - sizes[seen[p]])


if __name__ == '__main__':
    ndirs, directions = parse_directions(sys.stdin)
    #print(size(simulation(1000000000000, parse_directions(sys.stdin))))
    # TODO: identify cycle
    # identify at each step (multiple of lcm(ndirs, len(PIECES))) the pattern is repeating
    # (= piece placed at the same x and y-size)
    #print(ndirs, len(PIECES), math.lcm(ndirs, len(PIECES)))
    cycle_size = math.lcm(ndirs, len(PIECES))
    #print(simulation(2022, cycle_size, directions))
    print(simulation(1000000000000, cycle_size, directions))
