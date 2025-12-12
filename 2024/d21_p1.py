import heapq
import sys


DOOR_KEYPAD = {
    # +---+---+---+
    # | 7 | 8 | 9 |
    # +---+---+---+
    # | 4 | 5 | 6 |
    # +---+---+---+
    # | 1 | 2 | 3 |
    # +---+---+---+
    #     | 0 | A |
    #     +---+---+
    (0, 0): '7',
    (1, 0): '8',
    (2, 0): '9',
    (0, 1): '4',
    (1, 1): '5',
    (2, 1): '6',
    (0, 2): '1',
    (1, 2): '2',
    (2, 2): '3',
    (1, 3): '0',
    (2, 3): 'A',
}
DOOR_START = (2, 3)

DIR_KEYPAD = {
    #     +---+---+
    #     | ^ | A |
    # +---+---+---+
    # | < | v | > |
    # +---+---+---+
    (1, 0): (0, -1),
    (2, 0): (),
    (0, 1): (-1, 0),
    (1, 1): (0, 1),
    (2, 1): (1, 0),
}
DIR_START = (2, 0)

PADS = (
    DIR_KEYPAD,
    DIR_KEYPAD,
    DOOR_KEYPAD,
)
PADS_STARTS = (
    DIR_START,
    DIR_START,
    DOOR_START,
)


def apply(starts, d):
    for i, (x, y) in enumerate(starts):
        pad = PADS[i]
        if d == ():
            d = pad[x, y]
        else:
            dx, dy = d
            p = x + dx, y + dy
            if p not in pad:
                return False, None
            starts[i] = p
            return True, None

    return True, d


def process(starts, inputs):
    starts = list(starts)
    output = []

    for d in inputs:
        valid, out = apply(starts, d)
        if not valid:
            return False, output
        elif out is not None:
            output.append(out)

    return True, output


def find_best(starts, expected):
    queue = [(0, (), starts, expected)]
    seen = {(tuple(starts), tuple(expected))}

    while queue:
        length, path, starts, expected = heapq.heappop(queue)
        for d in DIR_KEYPAD.values():
            s = list(starts)
            valid, out = apply(s, d)
            if not valid:
                continue

            e = expected
            if out is not None:
                if out == e[0]:
                    e = e[1:]
                    if not e:
                        return path + (d,)
                else:
                    continue

            k = (tuple(s), tuple(e))
            if k not in seen:
                seen.add(k)
                heapq.heappush(queue, (length + 1, path + (d,), s, e))


def parse_file(f):
    for line in f:
        line = line.strip()
        code = int(''.join(c for c in line if c.isdigit()))
        yield code, line


def parse_debug_input(s):
    dirs = {
        '<': (-1, 0),
        '>': (1, 0),
        '^': (0, -1),
        'v': (0, 1),
        'A': (),
    }
    return [dirs[c] for c in s]


def format_debug_output(l):
    dirs = {
        (-1, 0): '<',
        (1, 0): '>',
        (0, -1): '^',
        (0, 1): 'v',
        (): 'A',
    }
    return ''.join(dirs[d] for d in l)


if __name__ == '__main__':
    # Process inputs to produce output
    # print(process(PADS_STARTS, parse_debug_input('<vA<AA>>^AvAA<^A>A<v<A>>^AvA^A<vA>^A<v<A>^A>AAvA^A<v<A>A>^AAAvA<^A>A')))
    # Find best input to product output
    # print(format_debug_output(find_best(PADS_STARTS, '029A')))
    # print(len(find_best(PADS_STARTS, '029A')))
    print(sum(code * len(find_best(PADS_STARTS, line)) for code, line in parse_file(sys.stdin)))
