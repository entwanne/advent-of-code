import sys


def parse_ranges(f):
    for line in f:
        if not line.strip():
            break
        start, stop = map(int, line.split('-'))
        yield range(start, stop + 1)


def parse_numbers(f):
    return (int(line) for line in f)


def is_fresh(ranges, n):
    return any(n in r for r in ranges)


if __name__ == '__main__':
    ranges = list(parse_ranges(sys.stdin))
    print(sum(is_fresh(ranges, n) for n in parse_numbers(sys.stdin)))
