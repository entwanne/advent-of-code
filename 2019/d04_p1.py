import sys
from collections import Counter


a, b = map(int, sys.stdin.read().split('-'))

def check(n):
    n = [int(c) for c in str(n)]
    return n == sorted(n) and Counter(n).most_common(1)[0][1] > 1

print(sum(1 for p in range(a, b+1) if check(p)))
