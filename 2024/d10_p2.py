import sys

from d10_p1 import *


if __name__ == '__main__':
    print(score(find_trailheads(parse_heights(sys.stdin), unique=False)))
