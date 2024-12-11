import sys
from collections import Counter


def parse_cube(c):
    pass


def parse_set(s):
    set_ = Counter()

    for c in s.split(', '):
        n, color = c.split()
        set_[color] = int(n)

    return set_


def parse_game(line):
    header, line = line.split(': ')
    gid = int(header.removeprefix('Game '))
    sets = [parse_set(s) for s in line.split('; ')]
    return gid, sets


def parse_games(f):
    games = {}

    for line in f:
        gid, sets = parse_game(line)
        games[gid] = sets

    return games


def is_possible(game):
    return all(
        set_['red'] <= 12 and set_['green'] <= 13 and set_['blue'] <= 14
        for set_ in game
    )
    return False


if __name__ == '__main__':
    print(sum(gid for gid, game in parse_games(sys.stdin).items() if is_possible(game)))
