import sys


def parse_file(f):
    left = []
    right = []
    for line in f:
        l, r = line.split()
        left.append(int(l))
        right.append(int(r))
    return left, right


def distances(left, right):
    left.sort()
    right.sort()
    return sum(abs(r - l) for l, r in zip(left, right))


if __name__ == '__main__':
    print(distances(*parse_file(sys.stdin)))
