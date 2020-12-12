import sys

commands = [(line[0], int(line[1:])) for line in sys.stdin]

directions = {
    'N': (+0, -1),
    'E': (+1, +0),
    'S': (+0, +1),
    'W': (-1, +0),
}
turns = {
    'N': {'L': 'W', 'R': 'E'},
    'E': {'L': 'N', 'R': 'S'},
    'S': {'L': 'E', 'R': 'W'},
    'W': {'L': 'S', 'R': 'N'},
}

# p1

x, y, d = 0, 0, 'E'

for cmd, arg in commands:
    if cmd == 'F':
        dx, dy = directions[d]
        x, y = x + arg * dx, y + arg * dy
    elif cmd in directions:
        dx, dy = directions[cmd]
        x, y = x + arg * dx, y + arg * dy
    else: # LR
        for _ in range(arg // 90):
            d = turns[d][cmd]

print(abs(x) + abs(y))

# p2

angles = {
    'L': -1j,
    'R': +1j,
}

x, y = 0, 0
wx, wy = 10, -1

for cmd, arg in commands:
    if cmd == 'F':
        x, y = x + arg * wx, y + arg * wy
    elif cmd in directions:
        dx, dy = directions[cmd]
        wx, wy = wx + arg * dx, wy + arg * dy
    else: # LR
        wz = wx + wy * 1j
        wz *= angles[cmd] ** (arg // 90)
        wx, wy = int(wz.real), int(wz.imag)

print(abs(x) + abs(y))
