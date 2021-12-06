import sys
from itertools import product

with open(sys.argv[1]) as f:
    init_code = [int(op) for op in f.read().split(',')]


def get_args(code, cur, n):
    spec = code[cur] // 100
    for i in range(1, n+1):
        t = spec % 10
        p = code[cur+i]
        if t == 0:
            yield p, code[p]
        elif t == 1:
            yield None, p
        else:
            raise ValueError
        spec //= 10


def run(code):
    cur = 0

    while (op := code[cur] % 100) != 99:
        if op == 1:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3)
            code[p3] = x1 + x2
            cur += 4
        elif op == 2:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3)
            code[p3] = x1 * x2
            cur += 4
        elif op == 3:
            (p, _), = get_args(code, cur, 1)
            code[p] = int(input('> '))
            cur += 2
        elif op == 4:
            (_, x), = get_args(code, cur, 1)
            print(x)
            cur += 2
        elif op == 5:
            (_, x1), (_, x2) = get_args(code, cur, 2)
            if x1:
                cur = x2
            else:
                cur += 3
        elif op == 6:
            (_, x1), (_, x2) = get_args(code, cur, 2)
            if not x1:
                cur = x2
            else:
                cur += 3
        elif op == 7:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3)
            code[p3] = int(x1 < x2)
            cur += 4
        elif op == 8:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3)
            code[p3] = int(x1 == x2)
            cur += 4

    return code[0]

run(init_code)
