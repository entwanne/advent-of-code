import sys
from itertools import batched

from d05_p1 import *


def parse_file(f):
    _, spec = f.readline().split(':')
    seeds = [
        (src, size)
        for src, size in batched(map(int, spec.split()), 2)
    ]
    mappings = parse_mappings(f)
    for mapping in mappings:
        mapping.sort(key=lambda row: row[1])
    return seeds, mappings


def transform(seed, mapping):
    seed_src, seed_size = seed
    output = []
    for dst, src, size in mapping:
        if src + size <= seed_src:
            continue
        if seed_src < src:
            osize = src - seed_src
            output.append((seed_src, osize))
            seed_src = src
            seed_size -= osize
        if seed_size <= 0:
            break
        osize = min(seed_size, src + size - seed_src)
        output.append((dst + seed_src - src, osize))
        seed_src += osize
        seed_size -= osize
        if seed_size <= 0:
            break
    if seed_size > 0:
        output.append((seed_src, seed_size))
    return output


def apply(seeds, mappings):
    for mapping in mappings:
        seeds = [seed for s in seeds for seed in transform(s, mapping)]

    return min(seeds)[0]


if __name__ == '__main__':
    seeds, mappings = parse_file(sys.stdin)
    print(apply(seeds, mappings))
