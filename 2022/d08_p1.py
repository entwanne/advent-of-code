import sys


def is_visible(trees, x, y):
    height = trees[x, y]
    for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        px, py = x, y
        while True:
            px += dx
            py += dy
            if (px, py) not in trees:
                return True
            if trees[px, py] >= height:
                break
    return False


trees = {
    (x, y): int(c)
    for y, line in enumerate(sys.stdin)
    for x, c in enumerate(line.strip())
}
print(sum(is_visible(trees, x, y) for x, y in trees))
