import sys

x = 1
cycles = [1]

for line in sys.stdin:
    match line.split():
        case ('noop',):
            cycles.append(x)
        case ('addx', dx):
            dx = int(dx)
            cycles.append(x)
            cycles.append(x)
            x += dx


print(sum(
    i * x
    for i, x in list(enumerate(cycles))[20::40]
))
