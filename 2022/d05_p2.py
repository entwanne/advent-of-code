import re
import sys


def split_line(line):
    while line:
        item, line = line[:4], line[4:]
        yield item.strip(' []')


def parse_stacks(f):
    names = []
    stacks = []

    for line in f:
        line = line.rstrip()
        if not line:
            break

        if '[' in line:
            for i, item in enumerate(split_line(line)):
                # ensure stack
                if i >= len(stacks):
                    stacks.append([])
                if item:
                    stacks[i].append(item)
        else:
            names = line.split()

    return dict(zip(names, stacks))


def parse_moves(f):
    for line in f:
        m = re.match(r'move (\d+) from (\d+) to (\d+)', line)
        n, src, dst = m.groups()
        yield int(n), src, dst


def parse(f):
    return parse_stacks(f), parse_moves(f)


def apply_moves(stacks, moves):
    for n, src, dst in moves:
        items = [stacks[src].pop(0) for _ in range(n)]
        for item in reversed(items):
            stacks[dst].insert(0, item)

    return stacks


def get_tops(stacks):
    return (stack[0] for stack in stacks.values())


print(''.join(get_tops(apply_moves(*parse(sys.stdin)))))
