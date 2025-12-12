import sys


def parse_file(f):
    return {
        (x, y): char
        for y, line in enumerate(f)
        for x, char in enumerate(line.strip())
    }


def find_char(chars, char):
    return {pos for pos, c in chars.items() if c == char}


def find_string(chars, string):
    first, *string = string

    queue = [
        (x, y, dx, dy)
        for x, y in find_char(chars, first)
        for dx, dy in ((-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0), (1, 1))
    ]

    for char in string:
        queue = [
            (x + dx, y + dy, dx, dy)
            for x, y, dx, dy in queue
            if chars.get((x + dx, y + dy)) == char
        ]

    return queue


if __name__ == '__main__':
    print(len(find_string(parse_file(sys.stdin), 'XMAS')))
