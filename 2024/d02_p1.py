import sys
from itertools import pairwise


def parse_file(f):
    for line in f:
        yield map(int, line.split())


def check_numbers(numbers):
    increase = None

    for n1, n2 in pairwise(numbers):
        inc = n2 > n1
        if increase is not None and increase != inc:
            return False
        if not 1 <= abs(n2 - n1) <= 3:
            return False
        increase = inc

    return True


if __name__ == '__main__':
    print(sum(check_numbers(n) for n in parse_file(sys.stdin)))
