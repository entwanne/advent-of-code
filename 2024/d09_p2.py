import sys


def parse_file(f):
    blocks = {}
    spaces = set()

    idx = 0
    free = False
    bid = 0

    for n in map(int, f.read().strip()):
        if n:
            if free:
                spaces.add((idx, n))
            else:
                blocks[bid] = (idx, n)
                bid += 1

        idx += n
        free = not free

    return blocks, sorted(spaces)


def compact(blocks, spaces):
    todo = sorted(blocks, reverse=True)[:-1]

    for bid in todo:
        idx, size = blocks[bid]
        try:
            s, space_idx, space_size = next(
                (s, space_idx, space_size)
                for s, (space_idx, space_size) in enumerate(spaces)
                if space_idx < idx and space_size >= size
            )
        except StopIteration:
            continue

        if space_size > size:
            spaces[s] = (space_idx + size, space_size - size)
        else:
            del spaces[s]

        blocks[bid] = (space_idx, size)

    return blocks


def checksum(blocks):
    return sum(
        sum(bid * j for j in range(i, i + n))
        for bid, (i, n) in blocks.items()
    )


if __name__ == '__main__':
    print(checksum(compact(*parse_file(sys.stdin))))
