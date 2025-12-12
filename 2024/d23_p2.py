import sys

from d23_p1 import parse_file


def parse_groups(links):
    links_dict = {}
    for a, b in links:
        links_dict.setdefault(a, set()).add(b)
        links_dict.setdefault(b, set()).add(a)

    groups = {}

    for c, c_links in links_dict.items():
        groups[c] = {frozenset({c})}

        for a in c_links:
            if a_groups := groups.get(a):
                for group in a_groups:
                    if all(b in c_links for b in group):
                        groups[c].add(group | {c})

    return {v for g in groups.values() for v in g}


def max_group(groups):
    return max(groups, key=lambda g: len(g))


def format_group(group):
    return ','.join(sorted(group))


if __name__ == '__main__':
    print(format_group(max_group(parse_groups(parse_file(sys.stdin)))))
