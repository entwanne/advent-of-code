import heapq
import itertools
import sys


def distance(v1, v2):
    x1, y1, z1 = v1
    x2, y2, z2 = v2
    return (x1 - x2)**2 + (y1 - y2)**2 + (z1 - z2)**2


def parse_coords(f):
    for line in f:
        yield tuple(int(x) for x in line.strip().split(','))


def compute_distances(coords):
    distances = []

    for v1, v2 in itertools.combinations(coords, r=2):
        dist = distance(v1, v2)
        heapq.heappush(distances, (dist, frozenset((v1, v2))))

    return distances


def make_groups(coords, n=1000):
    vec_groups = {v: k for k, v in enumerate(coords)}
    groups = {k: {v} for v, k in vec_groups.items()}

    distances = compute_distances(coords)

    for _ in range(n):
        _, (v1, v2) = heapq.heappop(distances)

        k1, k2 = vec_groups[v1], vec_groups[v2]
        if k1 != k2:
            k1, k2 = sorted((k1, k2))
            g2 = groups.pop(k2)

            for v in g2:
                vec_groups[v] = k1

            groups[k1] |= g2

    return groups


def score(groups):
    k1, g1 = max(groups.items(), key=lambda item: len(item[1]))
    del groups[k1]
    k2, g2 = max(groups.items(), key=lambda item: len(item[1]))
    del groups[k2]
    _, g3 = max(groups.items(), key=lambda item: len(item[1]))
    return len(g1) * len(g2) * len(g3)


if __name__ == '__main__':
    coords = list(parse_coords(sys.stdin))
    print(score(make_groups(coords)))
