import sys
import time
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
init_code[0] = 2
robot = run(init_code, inq, outq)

grid = defaultdict(int)

def print_game():
    while outq:
        x = outq.pop(0)
        y = outq.pop(0)
        t = outq.pop(0)
        grid[x, y] = t
    width = max(x for x, _ in grid) + 1
    height = max(y for _, y in grid) + 1

    return
    chars = {
        0: ' ',
        1: '|',
        2: '#',
        3: '=',
        4: 'o',
    }
    for y in range(height):
        for x in range(width):
            t = grid.get((x, y), 0)
            print(chars[t], end='')
        print()
    print()


while True:
    try:
        next(robot)
    except StopIteration:
        break

    print_game()
    xb, _ = next(k for k, v in grid.items() if v == 4)
    xp, _ = next(k for k, v in grid.items() if v == 3)
    if xb == xp:
        inq.append(0)
    elif xb < xp:
        inq.append(-1)
    else:
        inq.append(1)
    
    #time.sleep(0.01)

print_game()
print(grid[-1, 0])
