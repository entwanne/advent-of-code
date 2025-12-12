import heapq
import sys


def parse_file(f):
    blocks = set()
    spaces = set()

    idx = 0
    free = False
    bid = 0

    for n in map(int, f.read().strip()):
        if n:
            if free:
                spaces.add((idx, n))
            else:
                for i in range(n):
                    blocks.add((idx + i, bid))
                bid += 1

        idx += n
        free = not free

    blocks = [(-idx, bid) for (idx, bid) in blocks]
    heapq.heapify(blocks)
    return blocks, sorted(spaces)


def compact(blocks, spaces):
    while spaces:
        _, bid = heapq.heappop(blocks)
        space_idx, space_len = spaces[0]

        if space_len > 1:
            spaces[0] = (space_idx + 1, space_len - 1)
        else:
            del spaces[0]

        heapq.heappush(blocks, (-space_idx, bid))

    if blocks:
        _, bid = heapq.heappop(blocks)
        idx = (blocks[0][0] - 1) if blocks else 0
        heapq.heappush(blocks, (idx, bid))

    return blocks


def checksum(blocks):
    return sum(-i * n for i, n in blocks)


if __name__ == '__main__':
    print(checksum(compact(*parse_file(sys.stdin))))
