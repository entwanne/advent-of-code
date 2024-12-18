import sys

from d18_p1 import CELLS, best_path_length, parse_blocks


def run(blocks):
    grid = set(CELLS)
    for p in blocks:
        grid.discard(p)
        if best_path_length(grid) is None:
            return p


if __name__ == '__main__':
    print(*run(parse_blocks(sys.stdin)), sep=',')
