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


sensors = {}

for sensor, beacon in parse(sys.stdin):
    sensors[sensor] = distance(sensor, beacon)

#MAX = 20
MAX = 4000000
nexts = [(0, 0, MAX, MAX)]

while nexts:
    x1, y1, x2, y2 = nexts.pop(0)
    points = {(x1, y1), (x1, y2), (x2, y1), (x2, y2)}

    if not any(
            all(distance(sensor, p) <= dist for p in points)
            for sensor, dist in sensors.items()
    ):
        if len(points) == 1:
            (x, y), = points
            print(x, y)
            print(x * 4000000 + y)
            break

        width, height = x2 - x1, y2 - y1
        xm = x1 + width//2
        ym = y1 + height//2
        new_points = {
            (x1, y1, xm, ym),
            (xm + 1, y1, x2, ym),
            (x1, ym + 1, xm, y2),
            (xm + 1, ym + 1, x2, y2),
        }

        for x1, y1, x2, y2 in new_points:
            if x1 <= x2 and y1 <= y2:
                nexts.append((x1, y1, x2, y2))
