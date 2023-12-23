import re
import sys

def parse(f):
    for line in f:
        sx, sy, bx, by = map(int, re.findall(r'-?\d+', line))
        yield (sx, sy), (bx, by)


def distance(p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    return abs(x2 - x1) + abs(y2 - y1)


grid = set()
beacons = set()

#Y = 10
Y = 2000000


for sensor, beacon in parse(sys.stdin):
    beacons.add(beacon)
    dist = distance(sensor, beacon)
    sx, sy = sensor

    dy = abs(sy - Y)
    if dy > dist:
        continue
    grid.update((x, Y) for x in range(sx - dist + dy, sx + dist - dy + 1))

print(len(grid - beacons))
