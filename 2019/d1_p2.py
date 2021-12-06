import sys

def decompose(n):
    n = n // 3 - 2
    while n > 0:
        yield n
        n = n // 3 - 2


print(sum(sum(decompose(int(line))) for line in sys.stdin))
