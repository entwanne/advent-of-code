import itertools
import sys

"""
After some iterations, (number of new cells reached at step N - number of new cells reached at step N - width) is constant
cells = enlarge_map(cells, width, height)
distances = find_min_distances(start, cells)
print_growth(distances, width)

5000 = 454 * 11 + 6
For 11k+6 diffs, there are constant starting k=4 (n = 4*11 + 6 = 50), new_cells=130, diff=32
=> 5000 = 50 + 450 * 11 -> at step 500, we will reach 130 + 450 * 32 new cells
=> 5000 = 50 + 225 * 2*11 -> at step 500, we will reach 130 + 225 * 64 new cells
cells at 5000 = new cells reached at 5000 + new cells reached at 4998 + ... + new cells reached at 4978 + ... + cells at 50

11k+0 => diff = 20
11k+1 => diff = 25
11k+2 => diff = 30
11k+3 => diff = 30
11k+4 => diff = 32
11k+5 => diff = 34
11k+6 => diff = 32
11k+7 => diff = 30
11k+8 => diff = 32
11k+9 => diff = 34
11k+10 => diff = 25

print(50, sum(1 for _, d in distances.items() if d <= 50 and d % 2 == 0))
All cells reached at step 50: 1594

new cells reached on 2*11k+6 steps after 50 until 5000 (= 225 2*11 stes) = (130+64) + (130 + 2*64) + (130 + 3*64) + ... + (130 + 225 * 64) = 225 * 130 + 64 * (1 + 2 + 3 + ... + 225) = 225 * 130 + 64 * (225*226)/2 = 1656450
but we also need to add new cells discovered on 2*11k, 2*11k+2, 2*11k+4, 2*11k+8, 2*11k+10, 2*11k+12, 2*11k+14, 2*11k+16, 2*11k+18, 2*11k+20
first iter for each (after 50 at 11*4+6): 8:52, 10:54, 12:56, 14:58, 16:60, 18:62, 20:64, 0:66, 2:68, 4:70
At 52 (2*22 +  8), 141 new cells, from 52 to 4980 (226*22+8 ): 224 steps * 64 => 141 + 141+64 + 141+2*64 + ... 141+224*64 = 225 * 141 + 64 * (224*225)/2 = 1644525
At 54 (2*22 + 10), 118 new cells, from 54 to 4982 (226*22+10): 224 steps * 50 => 225 * 118 + 50*(224*225)/2 = 1286550
At 56 (2*22 + 12), 135 new cells, from 56 to 4984 (226*22+12): 224 steps * 50 => 225 * 135 + 50*(224*225)/2 = 1290375
At 58 (2*22 + 14), 157 new cells, from 58 to 4986 (226*22+14): 224 steps * 60 => 225 * 157 + 60*(224*225)/2 = 1547325
At 60 (2*22 + 16), 179 new cells, from 60 to 4988 (226*22+16): 224 steps * 68 => 225 * 179 + 68*(224*225)/2 = 1753875
At 62 (2*22 + 18), 155 new cells, from 62 to 4990 (226*22+18): 224 steps * 60 => 225 * 155 + 60*(224*225)/2 = 1546875
At 64 (2*22 + 20), 186 new cells, from 64 to 4992 (226*22+20): 224 steps * 68 => 225 * 186 + 68*(224*225)/2 = 1755450
At 66 (3*22 +  0), 129 new cells, from 66 to 4994 (227*22   ): 224 steps * 40 => 225 * 129 + 40*(224*225)/2 = 1037025
At 68 (3*22 +  2), 188 new cells, from 68 to 4996 (227*22+2 ): 224 steps * 60 => 225 * 188 + 60*(224*225)/2 = 1554300
At 70 (3*22 +  4), 204 new cells, from 70 to 4998 (227*22+4 ): 224 steps * 64 => 225 * 204 + 64*(224*225)/2 = 1658700

1594 (all cells reached at step 50) + 1656450+1644525+1286550+1290375+1547325+1753875+1546875+1755450+1037025+1554300+1658700 (cells reached after) = 16733044
"""


def parse_map(f):
    cells = {
        pos
        for y, line in enumerate(f)
        for x, char in enumerate(line.strip())
        if (pos := (x, y)) and (char == '.' or (char == 'S' and (start := pos)))
    }
    xmax, ymax = pos
    return start, (xmax + 1, ymax + 1), cells


def enlarge_map(cells, width, height, n=8):
    return {
        (x + mx * width, y + my * height)
        for (x, y) in cells
        for (mx, my) in itertools.product(range(-n, n + 1), repeat=2)
    }


def find_min_distances(start, cells):
    distances = {start: 0}
    queue = [(start, 1)]

    while queue:
        (x, y), dist = queue.pop(0)

        for dx, dy in ((-1, 0), (1, 0), (0, -1), (0, 1)):
            p = x + dx, y + dy
            if p in cells and p not in distances:
                distances[p] = dist
                queue.append((p, dist + 1))

    return distances


def print_distances(distances, width, height):
    xmin = min(x for x, _ in distances)
    xmax = max(x for x, _ in distances)
    ymin = min(y for _, y in distances)
    ymax = max(y for _, y in distances)
    l = len(str(max(distances.values()))) + 1

    for y in range(ymin, ymax + 1):
        if y % height == 0:
            print()
        print(' '.join(
            (' ' * l if x % width == 0 else '') +
            format(distances[x, y], f'{l}')
            if (x, y) in distances
            else '.' * l
            for x in range(xmin, xmax + 1)
        ))


def print_growth(distances, width, m=7):
    for r in range(width):
        print(f'# {width} * k + {r}')

        last = 0

        for i in range(1, m):
            n = i * width + r
            all_count = sum(1 for _, d in distances.items() if d <= n and d % 2 == n % 2)
            new_count = sum(1 for _, d in distances.items() if d == n)
            print(i, n, all_count, new_count, new_count - last)
            last = new_count


def count_new_cells(distances, dist):
    return sum(1 for d in distances.values() if d == dist)


def count_all_cells(distances, dist):
    return sum(1 for d in distances.values() if d <= dist and d % 2 == dist % 2)


if __name__ == '__main__':
    start, (width, height), cells = parse_map(sys.stdin)
    assert width == height

    N = 26501365
    W = width * 2 # we take only 1 step over 2

    cells = enlarge_map(cells, width, height)
    distances = find_min_distances(start, cells)

    # kmin * W + k * W + r == N, 0 <= r < W
    k, r = divmod(N, W)
    kmin = 3
    k -= kmin

    xmin = kmin * W + r
    cells_at_xmin = count_all_cells(distances, xmin)

    all_count = cells_at_xmin
    x = xmin
    p = r
    for i in range(width):
        f = k if i else k+1
        steps = 2 * (count_new_cells(distances, (kmin * 2 - 1) * width + p) - count_new_cells(distances, (kmin * 2 - 2) * width + p))
        c = count_new_cells(distances, x)
        all_count += k * c + steps * f * (f-1) // 2
        p = (p + 2) % W
        x += 2

    print(all_count)
