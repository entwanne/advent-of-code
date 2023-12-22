import enum
import sys


class Tool(enum.Enum):
    ROCK = 1
    PAPER = 2
    SCISSORS = 3


win_map = {
    Tool.ROCK: Tool.SCISSORS,
    Tool.PAPER: Tool.ROCK,
    Tool.SCISSORS: Tool.PAPER,
}
lose_map = {t2: t1 for t1, t2 in win_map.items()}

score_map = {(t1, t2): 0 for t1, t2 in win_map.items()} | {(t2, t1): 6 for t1, t2 in win_map.items()} | {(t, t): 3 for t in win_map}

elf_map = {
    'A': Tool.ROCK,
    'B': Tool.PAPER,
    'C': Tool.SCISSORS,
}


def parse(f):
    for line in f:
        elf, player = line.split()
        elf = elf_map[elf]
        match player:
            case 'X':  # lose
                player = win_map[elf]
            case 'Y':  # draw
                player = elf
            case 'Z':  # win
                player = lose_map[elf]
        yield (elf, player)

print(sum(
    player.value + score_map[elf, player]
    for elf, player in parse(sys.stdin)
))
