import sys


def hash_string(s):
    h = 0
    for b in s.encode():
        h = ((h + b) * 17) % 256
    return h


def parse_file(f):
    return f.read().strip().split(',')


if __name__ == '__main__':
    print(sum(hash_string(s) for s in parse_file(sys.stdin)))
