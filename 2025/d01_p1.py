import sys

MOD, START = 100, 50

def parse(f):
    for line in f:
        line = line.strip()
        d = {'L': -1, 'R': 1}[line[0]]
        yield d * int(line[1:])


def iterate(f):
    current = START

    for increment in parse(f):
        current = (current + increment) % MOD
        yield current


def compute_password(f):
    return sum(1 for c in iterate(f) if c == 0)


if __name__ == '__main__':
    print(compute_password(sys.stdin))
