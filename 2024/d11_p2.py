import sys

from d11_p1 import parse_file, blinkn


if __name__ == '__main__':
    print(blinkn(parse_file(sys.stdin), 75).total())
