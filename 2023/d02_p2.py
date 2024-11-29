from functools import reduce
import operator

from d02_p1 import *


def minimum_set(game):
    colors = ['red', 'green', 'blue']
    return {
        color: max(set_[color] for set_ in game)
        for color in colors
    }


def power(set_):
    return reduce(operator.mul, set_.values())


if __name__ == '__main__':
    print(sum(power(minimum_set(game)) for game in parse_games(sys.stdin).values()))
