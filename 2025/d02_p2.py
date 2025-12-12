import itertools
import sys

import d02_p1


def split(s, size):
    return (''.join(batch) for batch in itertools.batched(s, size))


def is_valid(n):
    s = str(n)
    size = len(s)
    for i in range(2, size + 1):
        if size % i != 0:
            continue
        if len(set(split(s, size//i))) == 1:
            return False
    return True


d02_p1.is_valid = is_valid


if __name__ == '__main__':
    print(sum(d02_p1.find_invalid_numbers(d02_p1.parse_ranges(sys.stdin))))
