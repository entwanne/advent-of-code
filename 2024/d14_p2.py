import itertools
import sys

from d14_p1 import parse_robots


def debug(width, height, robots):
    cells = {(x, y) for x, y, _, _ in robots}

    for y in range(height):
        print(''.join('#' if (x, y) in cells else '.' for x in range(width)))


def is_tree(width, height, robots):
    cells = {(x, y) for x, y, _, _ in robots}
    seen = set()
    queue = sorted((x, y, 1) for x, y, _, _ in robots)

    while queue:
        x, y, n = queue.pop(0)
        if (x, y) in seen:
            continue
        if n == 10:
            return True

        if (x, y + 1) in cells:
            queue.append((x, y + 1, n + 1))

    return False


def process(width, height, robots):
    for i in itertools.count(1):
        robots = [
            ((x + vx) % width, (y + vy) % height, vx, vy)
            for x, y, vx, vy in robots
        ]
        if is_tree(width, height, robots):
            debug(width, height, robots)
            return i


if __name__ == '__main__':
    print(process(*parse_robots(sys.stdin)))
