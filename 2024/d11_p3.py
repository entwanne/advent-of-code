import sys

from d11_p1 import Counter, blinkn


def parse_file(f):
    return list(map(int, f.read().split()))


def blink_simple(stone):
    if stone == 0:
        return [1]
    elif len(s := str(stone)) % 2 == 0:
        p = len(s) // 2
        l, r = s[:p], s[p:]
        return [int(l), int(r)]
    else:
        return [stone * 2024]


def blink_total(stones, n):
    for _ in range(n):
        stones = [sub for stone in stones for sub in blink_simple(stone)]
    return stones


def find_at_pos(stones, p, n):
    total = 0

    for i in range(n):
        for stone in stones:
            t = blinkn(Counter([stone]), n - i).total()
            if total + t <= p:
                total += t
            else:
                break
        stones = blink_simple(stone)

    return stones[p - total]


if __name__ == '__main__':
    stones = parse_file(sys.stdin)

    # Checks
    #for n in range(15):
    #    all_stones = blink_total(stones, n)
    #    assert len(all_stones) == blinkn(Counter(stones), n).total()
    #    assert all(stone == find_at_pos(stones, p, n) for p, stone in enumerate(all_stones))

    # Get 100000000th after 100 iterations
    print(blinkn(Counter(stones), 100).total())
    print(find_at_pos(stones, 100000000, 100))
