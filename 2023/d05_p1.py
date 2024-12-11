import sys


def parse_mappings(f):
    mappings = [[]]

    for line in f:
        try:
            dst, src, size = map(int, line.split())
            mappings[-1].append((dst, src, size))
        except ValueError:
            if mappings[-1] != []:
                mappings.append([])
        finally:
            pass

    return mappings


def parse_file(f):
    _, seeds = f.readline().split(':')
    return list(map(int, seeds.split())), parse_mappings(f)


def transform(seed, mapping):
    for dst, src, size in mapping:
        if seed in range(src, src + size):
            return dst + (seed - src)
    return seed


def apply(seeds, mappings):
    for mapping in mappings:
        seeds = [transform(s, mapping) for s in seeds]

    return min(seeds)


if __name__ == '__main__':
    seeds, mappings = parse_file(sys.stdin)
    print(apply(seeds, mappings))
