import re
import sys
from itertools import product

tiles = (group.splitlines() for group in sys.stdin.read().split('\n\n') if group)
tiles = {
    int(re.match(r'Tile (\d+):', tile[0]).group(1)): [l.strip() for l in tile[1:]]
    for tile in tiles
}

n = int(len(tiles) ** 0.5)

# p1

def get_sides(tile):
    left = ''.join(l[0] for l in tile)
    top = tile[0]
    right = ''.join(l[-1] for l in tile)
    bottom = tile[-1]
    return left, top, right, bottom

def get_rotations(sides):
    rotations = {sides: (0, 0)}
    left, top, right, bottom = sides
    rotations[right, top[::-1], left, bottom[::-1]] = (0, 1)
    rotations[left[::-1], bottom, right[::-1], top] = (0, 2)
    for i in range(1, 4):
        sides = left, top, right, bottom = bottom, left[::-1], top, right[::-1]
        rotations[sides] = (i, 0)
        rotations[right, top[::-1], left, bottom[::-1]] = (i, 1)
        rotations[left[::-1], bottom, right[::-1], top] = (i, 2)
    return rotations

tiles_rotations = {
    name: get_rotations(get_sides(tile))
    for name, tile in tiles.items()
}

def find(n, tiles_rotations, i=0, grid=None, rots=None):
    if i >= n**2:
        return grid, rots
    if grid is None:
        grid = {}
    if rots is None:
        rots = {}

    y, x = divmod(i, n)
    _, left_tile = grid.get((x-1, y), (None, None))
    _, top_tile = grid.get((x, y-1), (None, None))

    for name in list(tiles_rotations):
        rotations = tiles_rotations.pop(name)

        for tile, t in rotations.items():
            rots[name] = t
            if left_tile and tile[0] != left_tile[2]:
                continue
            if top_tile and tile[1] != top_tile[3]:
                continue
            grid[x, y] = name, tile
            ret = find(n, tiles_rotations, i=i+1, grid=grid, rots=rots)
            if ret:
                return ret

        tiles_rotations[name] = rotations

sol, rots = find(n, tiles_rotations)
print(sol[0, 0][0] * sol[n-1, 0][0] * sol[n-1, n-1][0] * sol[0, n-1][0])

# p2

def real_rot(tile, rot):
    n, t = rot
    h = len(tile)
    w = len(tile[0])
    for _ in range(n):
        tile = [''.join(tile[h-x-1][y] for x in range(h)) for y in range(w)]
        w, h = h, w
    if t == 1:
        tile = [''.join(tile[y][w-x-1] for x in range(w)) for y in range(h)]
    elif t == 2:
        tile = [''.join(tile[h-y-1][x] for x in range(w)) for y in range(h)]
    return tile


def crop_tile(tile):
    return [l[1:-1] for l in tile[1:-1]]


def print_tile(tile):
    for line in tile:
        print(line)

tiles = {name: crop_tile(real_rot(tile, rots[name])) for name, tile in tiles.items()}

bigtile = []
for y in range(n):
    tileline = None
    for x in range(n):
        name, _ = sol[x, y]
        tile = tiles[name]
        if tileline:
            tileline = [a+b for a, b in zip(tileline, tile)]
        else:
            tileline = tile
    bigtile += tileline

bigtile = [list(l) for l in bigtile]


def parse_pattern(pattern):
    h, w = len(pattern), len(pattern[0])
    return frozenset(
        (x, y)
        for y, line in enumerate(pattern)
        for x, c in enumerate(line)
        if c == '#'
    ), (w, h)

pattern = '''
                  # 
#    ##    ##    ###
 #  #  #  #  #  #   
'''
pattern = [l for l in pattern.splitlines() if l]
patterns = {
    parse_pattern(real_rot(pattern, rot))
    for rot in product(range(4), range(3))
}

th, tw = len(bigtile), len(bigtile[0])

for p, (pw, ph) in patterns:
    for ty in range(th-ph+1):
        for tx in range(tw-pw+1):
            if all(bigtile[ty+py][tx+px] in '#O' for px, py in p):
                for px, py in p:
                    bigtile[ty+py][tx+px] = 'O'

print(sum(1 for line in bigtile for c in line if c == '#'))
