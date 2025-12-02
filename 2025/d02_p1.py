import sys


def is_valid(n):
    s = str(n)
    size = len(s)
    if size % 2 == 1:
        return True
    return s[:size//2] != s[size//2:]


def parse_ranges(f):
    for r in f.read().split(','):
        start, stop = r.split('-')
        yield range(int(start), int(stop)+1)


def find_invalid_numbers(ranges):
    for r in ranges:
        for n in r:
            if not is_valid(n):
                yield n


if __name__ == '__main__':
    print(sum(find_invalid_numbers(parse_ranges(sys.stdin))))
