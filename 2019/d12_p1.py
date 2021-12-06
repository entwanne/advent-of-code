import re
import sys
from itertools import combinations


moons = [
    [int(i) for i in re.findall(r'-?\d+', line)]
    for line in sys.stdin
]
ids = range(len(moons))
velocities = [
    [0, 0, 0]
    for _ in ids
]

for _ in range(1000):
    for i, j in combinations(ids, 2):
        moon1, moon2 = moons[i], moons[j]
        vel1, vel2 = velocities[i], velocities[j]
        for x, (m1, m2) in enumerate(zip(moon1, moon2)):
            if m1 < m2:
                vel1[x] += 1
                vel2[x] -= 1
            elif m1 > m2:
                vel1[x] -= 1
                vel2[x] += 1

    for moon, vel in zip(moons, velocities):
        for x, v in enumerate(vel):
            moon[x] += v


print(sum(
    sum(map(abs, moon)) * sum(map(abs, vel))
    for moon, vel in zip(moons, velocities)
))
