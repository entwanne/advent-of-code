import sys

commands = [(line[0], int(line[1:])) for line in sys.stdin]

directions = {
    'N': +0 -1j,
    'E': +1 +0j,
    'S': +0 +1j,
    'W': -1 +0j,
}
angles = {
    'L': -1j,
    'R': +1j,
}

# p1

z, current_dir = 0, directions['E']

for cmd, arg in commands:
    if cmd == 'F':
        z += arg * current_dir
    elif cmd in directions:
        z += arg * directions[cmd]
    else: # LR
        current_dir *= angles[cmd] ** (arg // 90)

print(int(abs(z.real) + abs(z.imag)))

# p2

z, w = 0, 10-1j

for cmd, arg in commands:
    if cmd == 'F':
        z += arg * w
    elif cmd in directions:
        w += arg * directions[cmd]
    else: # LR
        w *= angles[cmd] ** (arg // 90)

print(int(abs(z.real) + abs(z.imag)))
