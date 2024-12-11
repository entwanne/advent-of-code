import sys
from collections import Counter


def parse_file(f):
    return Counter(map(int, f.read().split()))


def blink(stones):
    new = Counter()

    for x, n in stones.items():
        if x == 0:
            new[1] += n
        elif len(s := str(x)) % 2 == 0:
            p = len(s) // 2
            l, r = s[:p], s[p:]
            new[int(l)] += n
            new[int(r)] += n
        else:
            new[x * 2024] += n

    return new


def blinkn(stones, n):
    for _ in range(n):
        stones = blink(stones)

    return stones


if __name__ == '__main__':
    print(blinkn(parse_file(sys.stdin), 25).total())
