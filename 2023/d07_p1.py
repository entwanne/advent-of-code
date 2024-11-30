import sys
from collections import Counter

CARDS = {c: i for i, c in enumerate('23456789TJQKA')}


def parse_line(line):
    hand, bid = line.split()
    assert len(hand) == 5
    return [CARDS[c] for c in hand], int(bid)


def parse_file(f):
    return [parse_line(line) for line in f]


def sort_key(row):
    hand, _ = row
    return sorted(Counter(hand).values(), reverse=True), hand


data = parse_file(sys.stdin)
data.sort(key=sort_key)
print(sum(rank * bid for rank, (_, bid) in enumerate(data, start=1)))
