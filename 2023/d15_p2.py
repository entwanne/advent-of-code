import sys

from d15_p1 import hash_string, parse_file


def process(commands):
    boxes = {}

    for cmd in commands:
        if '=' in cmd:
            name, value = cmd.split('=')
            h = hash_string(name)
            boxes.setdefault(h, {})[name] = int(value)
        elif cmd.endswith('-'):
            name = cmd.removesuffix('-')
            h = hash_string(name)
            if box := boxes.get(h):
                box.pop(name, None)
        else:
            raise ValueError

    return boxes


def score(boxes):
    return sum(
        (n + 1) * (i + 1) * value
        for n, box in boxes.items()
        for i, value in enumerate(box.values())
    )


if __name__ == '__main__':
    print(score(process(parse_file(sys.stdin))))
