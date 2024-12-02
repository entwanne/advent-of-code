import sys
from itertools import pairwise

from d02_p1 import parse_file, check_numbers


def double_check(numbers):
    numbers = list(numbers)
    if check_numbers(numbers):
        return True

    for i, n in enumerate(numbers):
        copy = list(numbers)
        del copy[i]
        if check_numbers(copy):
            return True

    return False


if __name__ == '__main__':
    print(sum(double_check(n) for n in parse_file(sys.stdin)))
