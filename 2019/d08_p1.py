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


layer = min(layers, key=lambda l: Counter(l)['0'])
count = Counter(layer)
print(count['1'] * count['2'])
