import sys

from d05_p1 import parse_ranges


def overlap(r1, r2):
    r1, r2 = sorted((r1, r2), key=lambda r: r.start)
    return r1.stop > r2.start


def merge(r1, r2):
    return range(min(r1.start, r2.start), max(r1.stop, r2.stop))


class MultiRange:
    def __init__(self, *ranges):
        self._ranges = []
        self.update(ranges)

    def __len__(self):
        return sum(len(r) for r in self._ranges)

    def update(self, ranges):
        for r in ranges:
            self.add(r)

    def add(self, nr):
        ranges, self._ranges = self._ranges, []

        for r in ranges:
            if overlap(r, nr):
                nr = merge(r, nr)
            else:
                self._ranges.append(r)

        self._ranges.append(nr)


if __name__ == '__main__':
    multi_range = MultiRange()
    multi_range.update(parse_ranges(sys.stdin))
    print(len(multi_range))
