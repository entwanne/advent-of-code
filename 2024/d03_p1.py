import re
import sys


pattern = re.compile(r'mul\((\d{1,3}),(\d{1,3})\)')


def parse_file(f):
    s = f.read()
    for a, b in pattern.findall(s):
        yield int(a), int(b)


if __name__ == '__main__':
    print(sum(a * b for a, b in parse_file(sys.stdin)))
