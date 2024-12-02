import sys

from d23_p1 import CHARS, parse_map, find_longest_path


CHARS['<'] = CHARS['>'] = CHARS['^'] = CHARS['v'] = CHARS['.']


if __name__ == '__main__':
    print(find_longest_path(parse_map(sys.stdin)))
