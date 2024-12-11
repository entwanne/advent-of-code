import sys


def parse_game(s):
    header, game = s.split(': ')
    winning, numbers = game.split(' | ')
    return set(map(int, winning.split())), set(map(int, numbers.split()))


def game_score(game):
    winning, numbers = game
    pow_ = len(winning & numbers)
    if pow_ == 0:
        return 0
    return 2 ** (pow_ - 1)
            

if __name__ == '__main__':
    print(sum(game_score(parse_game(line)) for line in sys.stdin))
