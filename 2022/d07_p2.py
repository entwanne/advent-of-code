import sys

from d07_p1 import *


def find_biggest_dirs(node, threshold):
    size = node.total_size()
    if size >= threshold:
        yield (node, size)
    for child in node:
        if isinstance(child, Directory):
            yield from find_biggest_dirs(child, threshold)


if __name__ == '__main__':
    tree = make_tree(parse(sys.stdin))
    to_free = 30000000 - (70000000 - tree.total_size())
    print(min(size for _, size in find_biggest_dirs(tree, to_free)))
