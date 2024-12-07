import operator
import sys


def parse_file(f):
    for line in f:
        result, args = line.split(': ')
        yield int(result), map(int, args.split())


def solve(result, args, ops):
    first, *args = args
    queue = [(first, args)]

    while queue:
        r, args = queue.pop(0)

        first, *args = args
        for op in ops:
            nr = op(r, first)
            if not args and nr == result:
                return True
            elif args and nr <= result:  # no zero
                queue.append((nr, args))

    return False


if __name__ == '__main__':
    print(sum(
        result
        for result, args in parse_file(sys.stdin)
        if solve(result, args, [operator.add, operator.mul])
    ))
