import math
import operator
import sys

from d07_p1 import parse_file, solve


def op(a, b):
    return a * 10**(int(math.log(b, 10)) + 1) + b


if __name__ == '__main__':
    print(sum(
        result
        for result, args in parse_file(sys.stdin)
        if solve(result, args, [op, operator.add, operator.mul])
    ))
