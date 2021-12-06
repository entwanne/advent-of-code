import cmath
import math
import sys
from collections import Counter


asteroids = {
    (x, y)
    for y, line in enumerate(sys.stdin)
    for x, c in enumerate(line)
    if c == '#'
}
width = max(x for x, _ in asteroids)
height = max(y for _, y in asteroids)
density = width*height

def count_asteroids(ox, oy):
    vecs = set()
    for x, y in asteroids:
        vx, vy = x - ox, y - oy
        if (vx, vy) == (0, 0):
            continue
        g = math.gcd(vx, vy)
        vx //= g
        vy //= g
        vecs.add((vx, vy))
    return len(vecs)

origin = max(asteroids, key=lambda a: count_asteroids(*a))

others = {complex(*a): a for a in asteroids if a != origin}
origin = complex(*origin)

polars = {cmath.polar(z - origin): a for z, a in others.items()}
polars = {((math.pi/2 + t) % math.tau, r): a for (r, t), a in polars.items()}

by_rank = {}
counts = Counter()
for (t, r), a in sorted(polars.items()):
    rank = counts[t]
    counts[t] += 1
    by_rank[rank, t] = a

ordered = [a for _, a in sorted(by_rank.items())]
x, y = ordered[199]
print(x * 100 + y)
