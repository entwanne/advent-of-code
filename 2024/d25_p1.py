import itertools
import sys


def parse_block(f):
    block = {}
    sums = {}

    for y, line in enumerate(f):
        line = line.strip()
        if not line:
            break

        for x, char in enumerate(line):
            block[x, y] = (char == '#')
            sums[x] = sums.get(x, 0) + (char == '#')

    if not block:
        return None

    block_type = 'LOCK' if block[0, 0] else 'KEY'
    sums = [s - 1 for x, s in sorted(sums.items())]
    return block_type, sums


def parse_file(f):
    locks = []
    keys = []

    while block := parse_block(f):
        block_type, sums = block
        (locks if block_type == 'LOCK' else keys).append(sums)

    return locks, keys


def fit(lock, key):
    return all(l + k < 6 for l, k in zip(lock, key))


def all_fits(locks, keys):
    return sum(
        fit(lock, key)
        for lock, key in itertools.product(locks, keys)
    )


if __name__ == '__main__':
    print(all_fits(*parse_file(sys.stdin)))
