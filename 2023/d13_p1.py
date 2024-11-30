import sys


def parse_file(f):
    current = []

    for line in f:
        line = line.strip()
        if not line:
            if current:
                yield current
            current = []
            continue

        current.append(line)

    if current:
        yield current


def rotate(pattern):
    height = len(pattern)
    width = len(pattern[0])
    return [
        ''.join(pattern[y][x] for y in range(height))
        for x in range(width)
    ]


def find_reflection(pattern):
    for y in range(0, len(pattern) - 1):
        up = pattern[y::-1]
        down = pattern[y+1:]
        if all(up_line == down_line for up_line, down_line in zip(up, down)):
            return y + 1
    return 0


if __name__ == '__main__':
    patterns = parse_file(sys.stdin)
    print(sum(find_reflection(p) * 100 + find_reflection(rotate(p)) for p in patterns))
