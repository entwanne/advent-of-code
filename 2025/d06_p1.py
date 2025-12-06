import functools
import operator
import sys


def parse(f):
    columns = None

    for line in f:
        values = (int(v) if v.isdecimal() else v for v in line.split())
        if columns is None:
            columns = [[v] for v in values]
        else:
            for col, v in zip(columns, values):
                col.append(v)

    return columns


def operate_column(col):
    op = {'+': operator.add, '*': operator.mul}[col.pop()]
    return functools.reduce(op, col)


if __name__ == '__main__':
    columns = parse(sys.stdin)
    print(sum(operate_column(col) for col in columns))
