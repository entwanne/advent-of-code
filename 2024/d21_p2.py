import sys
from functools import cache

from d21_p1 import DOOR_KEYPAD, DOOR_START, DIR_KEYPAD, DIR_START, parse_file, format_debug_output


class Pad:
    "Hashable wrapper for reverse pad"

    def __init__(self, rev_pad):
        self.rev = rev_pad
        self.pad = {num: pos for pos, num in rev_pad.items()}

    def __getitem__(self, k):
        return self.pad[k]


DOOR_KEYPAD = Pad(DOOR_KEYPAD)
DIR_KEYPAD = Pad(DIR_KEYPAD)


N = 25
PADS = (
    *(DIR_KEYPAD for _ in range(N)),
    DOOR_KEYPAD,
)
STARTS = (
    *(DIR_START for _ in range(N)),
    DOOR_START,
)


@cache
def simple_move(pad, start, end):
    x, y = start
    nx, ny = end
    dx, dy = nx - x, ny - y

    ndx = abs(dx)
    idx = dx // ndx if ndx else 0
    rx = tuple((idx, 0) for _ in range(ndx))

    ndy = abs(dy)
    idy = dy // ndy if ndy else 0
    ry = tuple((0, idy) for _ in range(ndy))

    paths = frozenset()
    if (x + dx, y) in pad.rev:
        paths |= {rx + ry + ((),)}
    if (x, y + dy) in pad.rev:
        paths |= {ry + rx + ((),)}

    return paths


@cache
def best_length(pads, starts, expected):
    pad, pads = pads[-1], pads[:-1]
    start, starts = starts[-1], starts[:-1]

    solutions = [
        simple_move(pad, start, start := pad[s])
        for s in expected
    ]

    return sum(
        min(
            best_length(pads, starts, move) if pads else len(move)
            for move in moves
        ) 
        for moves in solutions
    )


if __name__ == '__main__':
    print(sum(code * best_length(PADS, STARTS, line) for code, line in parse_file(sys.stdin)))
