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

    x = min(x for x, _ in piece)
    y = min(y for _, y in piece) - size(blocks)
    blocks.update(piece)
    return x, y


def simulation(n, cycle_size, directions):
    blocks = set()
    pieces = cycle(PIECES)

    seen = {}

    for i in range(n):
        p = fall(blocks, directions, next(pieces))
        if i % cycle_size == 0:
            print(p)
            if p in seen:
                print('!!!', seen[p], i, size(blocks))
            seen[p] = i

    return blocks


if __name__ == '__main__':
    ndirs, directions = parse_directions(sys.stdin)
    #print(size(simulation(1000000000000, parse_directions(sys.stdin))))
    # TODO: identify cycle
    # identify at each step (multiple of lcm(ndirs, len(PIECES))) the pattern is repeating
    # (= piece placed at the same x and y-size)
    #print(ndirs, len(PIECES), math.lcm(ndirs, len(PIECES)))
    cycle_size = math.lcm(ndirs, len(PIECES))
    print(size(simulation(2022, cycle_size, directions)))
