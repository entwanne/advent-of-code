import sys
from itertools import combinations

N = 25
numbers = [int(line) for line in sys.stdin]

# p1

def is_valid(n, i):
    preamble = numbers[i-N:i]
    for a, b in combinations(preamble, 2):
        if a + b == n:
            return True
    return False

for i, n in enumerate(numbers[N:], N):
    if not is_valid(n, i):
        invalid = n
        break

print(invalid)

# p2

for i, tot in enumerate(numbers):
    a = b = tot
    for x in numbers[i+1:]:
        tot += x
        a = min(a, x)
        b = max(b, x)
        if tot == invalid:
            print(a, b, a+b)
            break
        elif tot > invalid:
            break
