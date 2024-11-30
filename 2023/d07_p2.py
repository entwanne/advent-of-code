import sys
from collections import Counter

CARDS = {c: i for i, c in enumerate('J23456789TQKA')}


def parse_line(line):
    hand, bid = line.split()
    assert len(hand) == 5
    return [CARDS[c] for c in hand], int(bid)


def parse_file(f):
    return [parse_line(line) for line in f]


def sort_key(row):
    hand, _ = row
    values = [v for v in hand if v]
    if values:
        count = Counter(values)
        (k, _), = count.most_common(1)
        count[k] += hand.count(0)
    else:
        count = {0: 5}
    return sorted(count.values(), reverse=True), hand


data = parse_file(sys.stdin)
data.sort(key=sort_key)
print(sum(rank * bid for rank, (_, bid) in enumerate(data, start=1)))
