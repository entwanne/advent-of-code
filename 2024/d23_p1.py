import itertools
import sys


def parse_file(f):
    for line in f:
        a, b = line.strip().split('-')
        yield a, b


def parse_groups(links):
    groups = set()

    computers = set()
    links_set = set()

    for a, b in links:
        computers.update((a, b))
        links_set.add(frozenset((a, b)))

    for a, b, c in itertools.combinations(computers, 3):
        if not any(name.startswith('t') for name in (a, b, c)):
            continue
        if frozenset((a, b)) in links_set and frozenset((a, c)) in links_set and frozenset((b, c)) in links_set:
            groups.add(frozenset((a, b, c)))

    return groups


if __name__ == '__main__':
    print(len(parse_groups(parse_file(sys.stdin))))
