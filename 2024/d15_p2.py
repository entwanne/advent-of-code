import sys

from d15_p1 import parse_file, score


class Block:
    def __init__(self, left, right):
        self.left = left
        self.right = right


def double_grid(start, grid):
    cells = set()
    blocks = {}

    for (x, y), c in grid.items():
        if c:
            block = Block(left=(2 * x, y), right=(2 * x + 1, y))
            blocks[2 * x, y] = block
            blocks[2 * x + 1, y] = block
        cells.add((2 * x, y))
        cells.add((2 * x + 1, y))

    x, y = start

    return (x * 2, y), cells, blocks


def find_blocks(cells, blocks, x, y, dx, dy):
    queue = [(x, y)]
    seen = set(queue)

    while queue:
        x, y = queue.pop(0)
        if (x, y) not in cells:
            continue
        if (x, y) not in blocks:
            continue
        block = blocks[x, y]
        for bx, by in (block.left, block.right):
            yield bx, by
            seen.add((bx, by))
            np = (bx + dx, by + dy)
            if np not in seen:
                seen.add(np)
                queue.append(np)


def moves(start, cells, blocks, directions):
    x, y = start

    for dx, dy in directions:
        np = x + dx, y + dy
        iblocks = set(find_blocks(cells, blocks, *np, dx, dy))

        if np in cells and all((bx + dx, by + dy) in cells for bx, by in iblocks):
            x, y = np
            mblocks = {blocks.pop(k) for k in iblocks}
            for block in mblocks:
                block.left = block.left[0] + dx, block.left[1] + dy
                block.right = block.right[0] + dx, block.right[1] + dy
                blocks[block.left] = block
                blocks[block.right] = block

    return grid, blocks


def score(blocks):
    return sum(
        block.left[0] + 100 * block.left[1]
        for block in set(blocks.values())
    )


def debug(cells, blocks, pos=None):
    width = max(x for x, _ in cells) + 1
    height = max(y for _, y in cells) + 1

    print()
    for y in range(height):
        print(''.join(
            '@' if (x, y) == pos
            else '#' if (x, y) not in cells
            else '.' if (x, y) not in blocks
            else '[' if blocks[x, y].left == (x, y)
            else ']'
            for x in range(width)
        ))


if __name__ == '__main__':
    start, grid, directions = parse_file(sys.stdin)
    start, cells, blocks = double_grid(start, grid)
    moves(start, cells, blocks, directions)
    print(score(blocks))
