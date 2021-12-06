import sys

code = [int(op) for op in sys.stdin.read().split(',')]
cur = 0

code[1] = 12
code[2] = 2

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

print(code[0])
