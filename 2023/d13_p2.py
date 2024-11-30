import sys

from d13_p1 import parse_file, rotate, find_reflection


def find_reflections(pattern, n=1):
    reflections = set()
    for y in range(0, len(pattern) - 1):
        up = pattern[y::-1]
        down = pattern[y+1:]
        if all(up_line == down_line for up_line, down_line in zip(up, down)):
            reflections.add(n * (y + 1))
    return reflections


def _find_new_reflections(pattern, n=1):
    pattern = [list(row) for row in pattern]
    for line in pattern:
        for x, char in enumerate(line):
            if char == '.':
                line[x] = '#'
            else:
                line[x] = '.'
            yield find_reflections(pattern, n=n)
            line[x] = char


def find_new_reflection(pattern):
    rot = rotate(pattern)
    current = find_reflection(pattern) * 100 or find_reflection(rot)
    for p, mul in ((pattern, 100), (rot, 1)):
        for reflections in _find_new_reflections(p, n=mul):
            reflections.discard(current)
            if reflections:
                return reflections.pop()


if __name__ == '__main__':
    patterns = parse_file(sys.stdin)
    print(sum(find_new_reflection(p) for p in patterns))
