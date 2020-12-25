import sys
from itertools import count

pkeys = map(int, sys.stdin.read().split())

def handshake_loop(sub):
    v = 1
    for loop in count(1):
        v = (v * sub) % 20201227
        yield loop, v

def find_loop(sub, value):
    for loop, v in handshake_loop(sub):
        if v == value:
            return loop

def handshake(sub, loop):
    for l, v in handshake_loop(sub):
        if l == loop:
            return v

pkey1, pkey2 = sorted(pkeys)

loop = find_loop(7, pkey1)
print(handshake(pkey2, loop))
