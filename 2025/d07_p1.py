import sys


def parse_map(f):
    splits = set()

    for y, line in enumerate(f):
        for x, char in enumerate(line):
            match char:
                case 'S':
                    start = x, y
                case '^':
                    splits.add((x, y))

    return y + 1, start, splits


def find_splits(height, start, splits):
    applied_splits = set()
    assert start[1] == 0
    positions = {start[0]}

    for y in range(1, height):
        new_positions = set()

        for x in positions:
            if (x, y) in splits:
                applied_splits.add((x, y))
                new_positions.add(x - 1)
                new_positions.add(x + 1)
            else:
                new_positions.add(x)

        positions = new_positions

    return applied_splits


if __name__ == '__main__':
    print(len(find_splits(*parse_map(sys.stdin))))
