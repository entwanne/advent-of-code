import sys
from itertools import combinations


def parse_map(f):
    antennas = {}
    for y, line in enumerate(f):
        for x, name in enumerate(line.strip()):
            if name != '.':
                antennas.setdefault(name, set()).add((x, y))

    return x + 1, y + 1, antennas


def compute_antinodes(width, height, antennas):
    antinodes = set()

    for name, positions in antennas.items():
        for (x1, y1), (x2, y2) in combinations(positions, 2):
            vx, vy = x2 - x1, y2 - y1
            for nx, ny in ((x1 - vx, y1 - vy), (x2 + vx, y2 + vy)):
                if 0 <= nx < width and 0 <= ny < height:
                    antinodes.add((nx, ny))

    return antinodes


if __name__ == '__main__':
    print(len(compute_antinodes(*parse_map(sys.stdin))))
