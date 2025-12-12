import sys


def parse_heights(f):
    return {
        (x, y): int(h)
        for y, line in enumerate(f)
        for x, h in enumerate(line.strip())
    }


def find_trailheads(heights, unique=True):
    starts = [p for p, h in heights.items() if h == 0]
    queue = [(p, p, 0) for p in starts]
    seen = set()

    while queue:
        start, p, h = queue.pop(0)
        if h == 9:
            if not unique or (start, p) not in seen:
                seen.add((start, p))
                yield p
            continue

        x, y = p

        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            np = x + dx, y + dy
            if heights.get(np) == h + 1:
                queue.append((start, np, h + 1))


def score(trailheads):
    return sum(1 for _ in trailheads)


if __name__ == '__main__':
    print(score(find_trailheads(parse_heights(sys.stdin))))
