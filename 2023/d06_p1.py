import operator
import sys
from functools import reduce


def parse(f):
    times, distances = f
    _, times = times.split(':')
    times = map(int, times.split())
    _, distances = distances.split(':')
    distances = map(int, distances.split())
    return list(zip(times, distances))


def meters(seconds):
    return [i * (seconds - i) for i in range(0, seconds + 1)]


if __name__ == '__main__':
    races = parse(sys.stdin)
    print(reduce(operator.mul, (sum(1 for m in meters(time) if m > distance) for time, distance in races)))
