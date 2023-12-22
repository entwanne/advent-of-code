import itertools
import sys


def scenic_score(trees, x, y):
    height = trees[x, y]
    score = 1
    for dx, dy in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        px, py = x, y
        for n in itertools.count(1):
            px += dx
            py += dy
            if (px, py) not in trees:
                score *= n - 1
                break
            if trees[px, py] >= height:
                score *= n
                break
    return score


trees = {
    (x, y): int(c)
    for y, line in enumerate(sys.stdin)
    for x, c in enumerate(line.strip())
}
print(max(scenic_score(trees, x, y) for x, y in trees))
