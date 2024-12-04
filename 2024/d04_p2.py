import sys

from d04_p1 import parse_file, find_char


def find_cross(chars, string):
    assert len(string) % 2 == 1
    l = len(string) // 2
    middle = string[l]

    queue = {
        frozenset({(x - l * dx1, y - l * dy1, dx1, dy1), (x - l * dx2, y - l * dy2, dx2, dy2)})
        for x, y in find_char(chars, middle)
        for dx1, dy1 in ((-1, -1), (-1, 1), (1, -1), (1, 1))
        for dx2, dy2 in ((-1, -1), (-1, 1), (1, -1), (1, 1))
        if (dx1, dy1) != (dx2, dy2)
    }

    first, *string = string
    queue = [
        ((x1, y1, dx1, dy1), (x2, y2, dx2, dy2))
        for (x1, y1, dx1, dy1), (x2, y2, dx2, dy2) in queue
        if chars.get((x1, y1)) == chars.get((x2, y2)) == first
    ]

    for char in string:
        queue = [
            ((x1 + dx1, y1 + dy1, dx1, dy1), (x2 + dx2, y2 + dy2, dx2, dy2))
            for (x1, y1, dx1, dy1), (x2, y2, dx2, dy2) in queue
            if chars.get((x1 + dx1, y1 + dy1)) == chars.get((x2 + dx2, y2 + dy2)) == char
        ]

    return queue


if __name__ == '__main__':
    print(len(find_cross(parse_file(sys.stdin), 'MAS')))
