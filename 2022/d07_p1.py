import sys


class File:
    def __init__(self, name, size):
        self.name = name
        self.size = size

    def total_size(self):
        return self.size


class Directory:
    def __init__(self, name, parent=None):
        self.name = name
        self.parent = parent
        self.children = {}
        if parent:
            parent.children[name] = self

    def __iter__(self):
        return iter(self.children.values())

    def __getitem__(self, name):
        return self.children[name]

    def __setitem__(self, name, node):
        self.children[name] = node

    def total_size(self):
        return sum(node.total_size() for node in self)


def parse(f):
    current = None
    output = []

    for line in f:
        if line.startswith('$'):
            if current:
                yield current, output
            _, *current = line.split()
            output = []
        else:
            output.append(line.split())

    if current:
        yield current, output


def make_tree(commands):
    tree = Directory('/')
    node = None

    for cmd, output in commands:
        match cmd:
            case ('cd', '/'):
                node = tree
            case ('cd', '..'):
                node = node.parent
            case ('cd', name):
                node = node[name]
            case ('ls',):
                for line in output:
                    match line:
                        case ('dir', name):
                            Directory(name, node)
                        case(size, name):
                            size = int(size)
                            node[name] = File(name, size)

    return tree


def find_lowest_dirs(node):
    size = node.total_size()
    if size <= 100000:
        yield (node, size)
    for child in node:
        if isinstance(child, Directory):
            yield from find_lowest_dirs(child)


if __name__ == '__main__':
    print(sum(size for _, size in find_lowest_dirs(make_tree(parse(sys.stdin)))))
