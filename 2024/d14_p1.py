import math
import re
import sys
from collections import Counter


def parse_file(f):
    for line in f:
        x, y, vx, vy = map(int, re.findall(r'-?\d+', line))
        yield x, y, vx, vy


def parse_robots(f):
    robots = list(parse_file(f))
    width = max(x for x, _, _, _ in robots) + 1
    height = max(y for _, y, _, _ in robots) + 1
    return width, height, robots


def process(width, height, robots, n):
    for _ in range(n):
        robots = [
            ((x + vx) % width, (y + vy) % height, vx, vy)
            for x, y, vx, vy in robots
        ]
    return width, height, robots


def score(width, height, robots):
    scores = Counter()
    px, py = width // 2, height // 2

    for x, y, _, _ in robots:
        if x == px or y == py:
            continue
        scores[x < px, y < py] += 1

    return math.prod(scores.values())


if __name__ == '__main__':
    print(score(*process(*parse_robots(sys.stdin), 100)))
