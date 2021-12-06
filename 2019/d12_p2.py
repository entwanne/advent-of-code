import math
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

combs = list(combinations(ids, 2))

states = [set(), set(), set()]
loops = [None] * 3
N = 0

while any(loop is None for loop in loops):
    for x in range(3):
        if loops[x] is not None:
            continue
        state = tuple((moon[x], vel[x]) for moon, vel in zip(moons, velocities))
        if state in states[x]:
            loops[x] = N
        else:
            states[x].add(state)

    for i, j in combs:
        moon1, moon2 = moons[i], moons[j]
        vel1, vel2 = velocities[i], velocities[j]
        for x, (m1, m2) in enumerate(zip(moon1, moon2)):
            if loops[x] is not None:
                continue
            if m1 < m2:
                vel1[x] += 1
                vel2[x] -= 1
            elif m1 > m2:
                vel1[x] -= 1
                vel2[x] += 1

    for moon, vel in zip(moons, velocities):
        for x, v in enumerate(vel):
            if loops[x] is not None:
                continue
            moon[x] += v

    N += 1


print(math.lcm(*loops))
