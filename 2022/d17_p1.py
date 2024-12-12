import sys
from itertools import cycle


WIDTH = 7
PIECES = [
    # XXXX
    {(0, 0), (1, 0), (2, 0), (3, 0)},
    # .X.
    # XXX
    # .X.
    {(1, 0), (0, 1), (1, 1), (2, 1), (1, 2)},
    # ..X
    # ..X
    # XXX
    {(0, 0), (1, 0), (2, 0), (2, 1), (2, 2)},
    # X
    # X
    # X
    # X
    {(0, 0), (0, 1), (0, 2), (0, 3)},
    # XX
    # XX
    {(0, 0), (1, 0), (0, 1), (1, 1)},
]


def parse_directions(f):
    return cycle(-1 if c == '<' else 1 for c in f.read().strip())


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
    blocks.update(piece)


def simulation(n, directions):
    blocks = set()
    pieces = cycle(PIECES)

    for _ in range(n):
        fall(blocks, directions, next(pieces))

    return blocks


def size(blocks):
    if not blocks:
        return 0
    return max(y for _, y in blocks) + 1


def debug(blocks):
    if not blocks:
        return

    ymax = size(blocks) - 1
    for y in range(ymax, -1, -1):
        print('|' + ''.join('#' if (x, y) in blocks else '.' for x in range(WIDTH)) + '|')

    print('+' + '-' * WIDTH + '+')


if __name__ == '__main__':
    print(size(simulation(2022, parse_directions(sys.stdin))))
