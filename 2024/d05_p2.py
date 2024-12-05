import sys
from functools import cmp_to_key
from collections import Counter

from d05_p1 import combinations, check_update, parse_file


def sort_update(rules, update):
    counts = Counter()
    for p1, p2 in combinations(update, 2):
        if p2 in rules.get(p1, set()):
            counts[p1] -= 1
            counts[p2] += 1
        elif p1 in rules.get(p2, set()):
            counts[p1] += 1
            counts[p2] -= 1

    update.sort(key=lambda p: counts[p])


def check_updates(rules, updates):
    for update in updates:
        if not check_update(rules, update):
            sort_update(rules, update)
            m = len(update) // 2
            yield update[m]


if __name__ == '__main__':
    print(sum(check_updates(*parse_file(sys.stdin))))
