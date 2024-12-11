import sys
from functools import cache


def parse(f):
    for line in f:
        blocks, counts = line.split()
        counts = tuple(map(int, counts.split(',')))
        yield blocks, counts


@cache
def count_arrangements(blocks, counts, current=-1):
    if not blocks:
        return 0 if current > 0 or counts else 1
    match blocks[0]:
        case '.':
            return 0 if current > 0 else count_arrangements(blocks[1:], counts)
        case '#':
            if current == 0:
                return 0
            elif current > 0:
                current -= 1
            elif counts:
                current, *counts = counts
                counts = tuple(counts)
                current -= 1
            else:
                return 0
            return count_arrangements(blocks[1:], counts, current)
        case '?':
            return count_arrangements('.' + blocks[1:], counts, current) + count_arrangements('#' + blocks[1:], counts, current)



if __name__ == '__main__':
    print(sum(count_arrangements(blocks, counts) for blocks, counts in parse(sys.stdin)))
