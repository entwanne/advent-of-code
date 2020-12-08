# Day 1: Report Repair

import sys
from itertools import combinations

values = list(map(int, sys.stdin))

# p1

for a, b in combinations(values, 2):
    if a + b == 2020:
        print(a, b, a*b)
        break

# p2

for a, b, c in combinations(values, 3):
    if a + b + c == 2020:
        print(a, b, c, a*b*c)
        break
