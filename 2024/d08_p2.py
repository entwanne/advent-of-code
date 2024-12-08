import sys

from d08_p1 import parse_map, combinations


def compute_antinodes(width, height, antennas):
    antinodes = set()

    for name, positions in antennas.items():
        for (x1, y1), (x2, y2) in combinations(positions, 2):
            vx, vy = x2 - x1, y2 - y1
            queue = [(x1, y1, -vx, -vy), (x2, y2, vx, vy)]
            while queue:
                nx, ny, vx, vy = queue.pop(0)
                if 0 <= nx < width and 0 <= ny < height:
                    antinodes.add((nx, ny))
                    queue.append((nx + vx, ny + vy, vx, vy))

    return antinodes


if __name__ == '__main__':
    print(len(compute_antinodes(*parse_map(sys.stdin))))
