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

for i, x in enumerate(cycles):
    print('#' if i%40 - 1 in {x-1, x, x+1} else '.', end='')
    if i % 40 == 0:
        print()
