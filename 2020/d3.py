import sys

grid = [line.strip() for line in sys.stdin]

# p1

count = 0
x = 0
for line in grid[1:]:
    x += 3
    if line[x % len(line)] == '#':
        count += 1

print(count)

# p2

def cross(dx, dy):
    count = 0
    x = y = 0
    for line in grid[dy::dy]:
        x += dx
        if line[x % len(line)] == '#':
            count += 1

    return count

a = cross(1, 1)
b = cross(3, 1)
c = cross(5, 1)
d = cross(7, 1)
e = cross(1, 2)

print(a, b, c, d, e, a*b*c*d*e)
