import sys
from collections import Counter

from d07_p1 import parse_map


def count_timelines(height, start, splits):
    assert start[1] == 0
    timelines = {start[0]: 1}

    for y in range(1, height):
        new_timelines = Counter()

        for x, n in timelines.items():
            if (x, y) in splits:
                new_timelines[x - 1] += n
                new_timelines[x + 1] += n
            else:
                new_timelines[x] += n

        timelines = new_timelines

    return(sum(new_timelines.values()))


if __name__ == '__main__':
    print(count_timelines(*parse_map(sys.stdin)))
