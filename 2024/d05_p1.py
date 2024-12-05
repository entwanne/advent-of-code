import sys
from itertools import combinations


def parse_rules(f):
    rules = {}

    for line in f:
        line = line.strip()
        if not line:
            break

        p1, p2 = map(int, line.split('|'))
        rules.setdefault(p1, set()).add(p2)

    return rules


def parse_updates(f):
    for line in f:
        yield list(map(int, line.split(',')))


def parse_file(f):
    return parse_rules(f), parse_updates(f)


def check_update(rules, update):
    for p1, p2 in combinations(update, 2):
        if p1 in rules.get(p2, set()):
            return False
    return True


def check_updates(rules, updates):
    for update in updates:
        if check_update(rules, update):
            m = len(update) // 2
            yield update[m]


if __name__ == '__main__':
    print(sum(check_updates(*parse_file(sys.stdin))))
