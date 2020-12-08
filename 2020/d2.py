# Day 2: Password Philosophy

import sys

def parse():
    for line in sys.stdin:
        line = line.rstrip()
        line, password = line.split(': ', 1)
        r, letter = line.split()
        a, b = map(int, r.split('-'))
        yield a, b, letter, password

# p1

def p1():
    count = 0
    for a, b, letter, password in parse():
        if a <= password.count(letter) <= b:
            count += 1
    print(count)

# p1

def p2():
    count = 0
    for a, b, letter, password in parse():
        c = (password[a-1] == letter) + (password[b-1] == letter)
        if c == 1:
            count += 1
    print(count)
