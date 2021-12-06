import sys
from itertools import product

init_code = [int(op) for op in sys.stdin.read().split(',')]


def run(code):
    cur = 0

    while (op := code[cur]) != 99:
        if op == 1:
            p1, p2, p3 = code[cur+1], code[cur+2], code[cur+3]
            x1, x2 = code[p1], code[p2]
            code[p3] = x1 + x2
            cur += 4
        elif op == 2:
            p1, p2, p3 = code[cur+1], code[cur+2], code[cur+3]
            x1, x2 = code[p1], code[p2]
            code[p3] = x1 * x2
            cur += 4

    return code[0]

for noun, verb in product(range(100), range(100)):
    code = init_code[:]
    code[1], code[2] = noun, verb
    if run(code) == 19690720:
        print(100 * noun + verb)
        break
