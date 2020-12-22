import sys

init_player1, init_player2 = (
    [int(c) for c in cards.splitlines()[1:]]
    for cards in sys.stdin.read().split('\n\n')
)

# p1

player1 = list(init_player1)
player2 = list(init_player2)

while player1 and player2:
    card1 = player1.pop(0)
    card2 = player2.pop(0)

    if card1 > card2:
        player1.extend((card1, card2))
    else:
        player2.extend((card2, card1))


def score(player):
    return sum(i*c for i, c in enumerate(reversed(player), 1))

print(score(player1 or player2))

# p2

def game(player1, player2, i=1):
    known = set()

    while player1 and player2:
        key = tuple(player1), tuple(player2)
        if key in known:
            return 1
        known.add(key)

        card1 = player1.pop(0)
        card2 = player2.pop(0)

        if card1 <= len(player1) and card2 <= len(player2):
            winner = game(player1[:card1], player2[:card2])
        else:
            winner = 1 if card1 > card2 else 2

        if winner == 1:
            player1.extend((card1, card2))
        else:
            player2.extend((card2, card1))

    return 1 if player1 else 2

player1, player2 = init_player1, init_player2
game(player1, player2)
print(score(player1 or player2))
