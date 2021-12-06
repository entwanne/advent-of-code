import sys
from collections import Counter

width = 25
height = 6

layers = []

while True:
    layer = sys.stdin.read(width*height).strip()
    if not layer:
        break
    layers.append(layer)


sol = ['2'] * width*height

for layer in layers:
    sol = [x if x != '2' else y for x, y in zip(sol, layer)]

s = ''.join(sol)
while s:
    print(' '.join('X' if c == '1' else ' ' for c in s[:width]))
    s = s[width:]
