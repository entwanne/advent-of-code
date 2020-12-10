import sys
from collections import Counter

numbers = [int(line) for line in sys.stdin]
numbers.sort()

# p1

jolt = 0
diffs = Counter({3: 1})
for n in numbers:
    diffs[n - jolt] += 1
    jolt = n

print(diffs[1] * diffs[3])

# p2

x = numbers.pop()
ways = {x: 1}

numbers.reverse()
numbers.append(0)

for n in numbers:
    ways[n] = ways.get(n+1, 0) + ways.get(n+2, 0) + ways.get(n+3, 0)

print(ways[0])
