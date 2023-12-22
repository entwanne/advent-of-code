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

score_map = {(t1, t2): 0 for t1, t2 in win_map.items()} | {(t2, t1): 6 for t1, t2 in win_map.items()} | {(t, t): 3 for t in win_map}

elf_map = {
    'A': Tool.ROCK,
    'B': Tool.PAPER,
    'C': Tool.SCISSORS,
}
player_map = {
    'X': Tool.ROCK,
    'Y': Tool.PAPER,
    'Z': Tool.SCISSORS,
}


def parse(f):
    for line in f:
        elf, player = line.split()
        yield (elf_map[elf], player_map[player])

print(sum(
    player.value + score_map[elf, player]
    for elf, player in parse(sys.stdin)
))
