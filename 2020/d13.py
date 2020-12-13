import sys
from itertools import count

t = int(sys.stdin.readline())
bus = [None if b == 'x' else int(b) for b in sys.stdin.readline().split(',')]

# p1

def get_wait(t, b):
    return b - (t-1)%b - 1

waits = [(get_wait(t, b), b) for b in bus if b is not None]
w, b = min(waits)
print(w * b)

# p2

req = [
    (b, i)
    for i, b in enumerate(bus)
    if b is not None
]

(step, _), *req = req
start = 0

while req:
    first = True
    (b, i), *req = req
    for t in count(start, step):
        if (t + i) % b == 0:
            if first:
                start = t
                first = False
            else:
                step = t - start
                break

print(start)
