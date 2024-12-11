import sys
from collections import Counter
from d04_p1 import *


count = Counter()
for i, line in enumerate(sys.stdin):
    count[i] += 1
    winning, numbers = parse_game(line)
    score = len(winning & numbers)

    for j in range(i + 1, i + score + 1):
        count[j] += count[i]

print(sum(count.values()))
