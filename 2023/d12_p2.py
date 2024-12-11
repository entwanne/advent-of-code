import sys

from d12_p1 import *


def unfold(blocks, counts):
    return '?'.join([blocks] * 5), counts * 5


if __name__ == '__main__':
    print(sum(count_arrangements(*unfold(blocks, counts)) for blocks, counts in parse(sys.stdin)))
