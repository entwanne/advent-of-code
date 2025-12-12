import sys
from collections import Counter
from itertools import chain, islice

from d22_p1 import parse_file, get_nexts


def get_prices(secret, n=2000):
    previous = None
    for s in chain([secret], islice(get_nexts(secret), 0, n)):
        current = s % 10
        diff = None if previous is None else current - previous
        yield current, diff
        previous = current


def get_sequences(prices):
    last4 = ()
    seen = set()
    for price, diff in prices:
        if diff is not None:
            last4 = (*last4, diff)[-4:]
        if len(last4) < 4:
            continue
        if last4 not in seen:
            seen.add(last4)
            yield last4, price


def get_best_sequence(secrets):
    best_sequences = Counter()

    for secret in secrets:
        prices = get_prices(secret)
        for seq, price in get_sequences(prices):
            best_sequences[seq] += price

    (seq, total), = best_sequences.most_common(1)
    return seq, total


if __name__ == '__main__':
    print(get_best_sequence(parse_file(sys.stdin))[1])
