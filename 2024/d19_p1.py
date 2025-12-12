import sys
from functools import cache


def parse_input(f):
    patterns = frozenset(f.readline().strip().split(', '))
    assert f.readline().strip() == ''
    return patterns, [line.strip() for line in f]


@cache
def is_possible(patterns, string):
    if not string:
        return True

    for p in patterns:
        if string.startswith(p) and is_possible(patterns, string[len(p):]):
            return True

    return False


if __name__ == '__main__':
    patterns, lines = parse_input(sys.stdin)
    print(sum(is_possible(patterns, line) for line in lines))
