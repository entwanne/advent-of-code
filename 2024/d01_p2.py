import sys
from collections import Counter

from d01_p1 import parse_file


def score(left, right):
    right = Counter(right)
    return sum(l * right[l] for l in left)


if __name__ == '__main__':
    print(score(*parse_file(sys.stdin)))
