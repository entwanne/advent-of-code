import re
import sys


pattern = re.compile(r"mul\((\d{1,3}),(\d{1,3})\)|(do|don't)\(\)")


def parse_file(f):
    s = f.read()
    enabled = True
    for m in pattern.findall(s):
        if m == ("", "", "do"):
            enabled = True
        elif m == ("", "", "don't"):
            enabled = False
        elif enabled:
            a, b, _ = m
            yield int(a), int(b)


if __name__ == '__main__':
    print(sum(a * b for a, b in parse_file(sys.stdin)))
