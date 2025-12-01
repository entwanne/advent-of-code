import sys

from d01_p1 import MOD, START, parse


def compute_password(f):
    current = START
    zeros = 0
    prev = False

    for increment in parse(f):
        if increment >= 0:
            turns, increment = divmod(increment, MOD)
        else:
            turns, increment = divmod(-increment, MOD)
            increment = -increment

        zeros += turns
        current += increment
        if current == 0:
            zeros += 1
        elif current < 0 or current >= MOD:
            zeros += (not prev)
            current %= MOD

        prev = (current == 0)

    return zeros


if __name__ == '__main__':
    print(compute_password(sys.stdin))
