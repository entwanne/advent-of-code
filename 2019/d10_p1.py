import sys
from math import gcd


asteroids = {
    (x, y)
    for y, line in enumerate(sys.stdin)
    for x, c in enumerate(line)
    if c == '#'
}

def count_asteroids(ox, oy):
    vecs = set()
    for x, y in asteroids:
        vx, vy = x - ox, y - oy
        if (vx, vy) == (0, 0):
            continue
        g = gcd(vx, vy)
        vx //= g
        vy //= g
        vecs.add((vx, vy))
    return len(vecs)

print(max(count_asteroids(*o) for o in asteroids))
