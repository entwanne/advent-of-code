import re
import sys
from itertools import product

def read_input():
    for line in sys.stdin:
        var, value = line.strip().split(' = ')
        if var == 'mask':
            yield 'mask', None, value
        elif (m := re.match(r'mem\[(\d+)\]', var)):
            idx = int(m.group(1))
            value = int(value)
            yield 'mem', idx, value

rows = list(read_input())

# p1

memory = {}
and_mask, or_mask = None, None

for cmd, idx, arg in rows:
    if cmd == 'mask':
        and_mask = int(arg.replace('X', '1'), 2)
        or_mask = int(arg.replace('X', '0'), 2)
    else:
        arg = (arg & and_mask) | or_mask
        memory[idx] = arg

print(sum(v for v in memory.values()))

# p2

memory = {}
masks = []

for cmd, idx, arg in rows:
    if cmd == 'mask':
        masks = []
        mask = list(arg)
        x_pos = [idx for idx, c in enumerate(mask) if c == 'X']
        default = ['1'] * len(mask)
        for m in product('01', repeat=len(x_pos)):
            for idx, c in zip(x_pos, m):
                mask[idx] = default[idx] = c
            or_mask = int(''.join(mask), 2)
            and_mask = int(''.join(default), 2)
            masks.append((or_mask, and_mask))
    else:
        for or_mask, and_mask in masks:
            i = (idx | or_mask) & and_mask
            memory[i] = arg

print(sum(v for v in memory.values()))
