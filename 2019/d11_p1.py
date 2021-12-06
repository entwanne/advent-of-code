import sys
from collections import defaultdict

init_code = (int(op) for op in sys.stdin.read().split(','))
init_code = defaultdict(int, {i: op for i, op in enumerate(init_code)})


def get_args(code, cur, n, rel_base):
    spec = code[cur] // 100
    for i in range(1, n+1):
        t = spec % 10
        p = code[cur+i]
        if t == 0:
            yield p, code[p]
        elif t == 1:
            yield None, p
        elif t == 2:
            yield rel_base+p, code[rel_base+p]
        else:
            raise ValueError
        spec //= 10


def run(code, inq, outq):
    cur = 0
    rel_base = 0

    while (op := code[cur] % 100) != 99:
        if op == 1:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3, rel_base)
            code[p3] = x1 + x2
            cur += 4
        elif op == 2:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3, rel_base)
            code[p3] = x1 * x2
            cur += 4
        elif op == 3:
            (p, _), = get_args(code, cur, 1, rel_base)
            while not inq:
                yield
            code[p] = inq.pop(0)
            cur += 2
        elif op == 4:
            (_, x), = get_args(code, cur, 1, rel_base)
            outq.append(x)
            cur += 2
        elif op == 5:
            (_, x1), (_, x2) = get_args(code, cur, 2, rel_base)
            if x1:
                cur = x2
            else:
                cur += 3
        elif op == 6:
            (_, x1), (_, x2) = get_args(code, cur, 2, rel_base)
            if not x1:
                cur = x2
            else:
                cur += 3
        elif op == 7:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3, rel_base)
            code[p3] = int(x1 < x2)
            cur += 4
        elif op == 8:
            (_, x1), (_, x2), (p3, _) = get_args(code, cur, 3, rel_base)
            code[p3] = int(x1 == x2)
            cur += 4
        elif op == 9:
            (_, x), = get_args(code, cur, 1, rel_base)
            rel_base += x
            cur += 2

    return code[0]


inq = []
outq = []
robot = run(init_code, inq, outq)

grid = defaultdict(int)
pos = 0
direction = 1j

while True:
    inq.append(grid[pos])
    try:
        next(robot)
    except StopIteration:
        break

    paint = outq.pop(0)
    turn = outq.pop(0)
    grid[pos] = paint
    if turn == 0:
        direction *= 1j
    elif turn == 1:
        direction *= -1j
    pos += direction

print(len(grid.keys()))
