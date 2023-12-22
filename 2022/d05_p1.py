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
    pass


def parse(f):
    print(parse_stacks(f))


parse(sys.stdin)
