import sys

from d19_p1 import cache, parse_input


@cache
def count_solutions(patterns, string):
    if not string:
        return True

    return sum(
        string.startswith(p) and count_solutions(patterns, string[len(p):])
        for p in patterns
    )


if __name__ == '__main__':
    patterns, lines = parse_input(sys.stdin)
    print(sum(count_solutions(patterns, line) for line in lines))
