import sys

from d06_p1 import operate_column


def parse(f):
    content = []
    for y, line in enumerate(f):
        for x, c in enumerate(line.rstrip('\n')):
            if x >= len(content):
                content.append('')
            content[x] += c.strip()

    op = None
    block = []

    for line in content:
        if not line:
            yield [*block, op]
            op = None
            block = []
        elif not op:
            op = line[-1]
            block.append(int(line[:-1]))
        else:
            block.append(int(line))

    yield [*block, op]


if __name__ == '__main__':
    columns = parse(sys.stdin)
    print(sum(operate_column(col) for col in columns))
