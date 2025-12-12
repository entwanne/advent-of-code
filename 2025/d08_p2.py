import heapq
import sys

from d08_p1 import parse_coords, compute_distances


def get_last_junction(coords):
    vec_groups = {v: k for k, v in enumerate(coords)}
    groups = {k: {v} for v, k in vec_groups.items()}

    distances = compute_distances(coords)

    while len(groups) > 1:
        _, (v1, v2) = heapq.heappop(distances)

        k1, k2 = vec_groups[v1], vec_groups[v2]
        if k1 != k2:
            k1, k2 = sorted((k1, k2))
            g2 = groups.pop(k2)

            for v in g2:
                vec_groups[v] = k1

            groups[k1] |= g2

    return v1, v2



if __name__ == '__main__':
    coords = list(parse_coords(sys.stdin))
    v1, v2 = get_last_junction(coords)
    print(v1[0] * v2[0])
