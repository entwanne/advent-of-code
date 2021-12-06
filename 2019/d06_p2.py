import sys


parents = {}


def ancestors(k):
    while k in parents:
        k = parents[k]
        yield k


for line in sys.stdin:
    left, right = line.strip().split(')')
    parents[right] = left


you_acs = list(ancestors('YOU'))
san_acs = list(ancestors('SAN'))

while you_acs[-1] == san_acs[-1]:
    you_acs.pop()
    san_acs.pop()

print(len(you_acs) + len(san_acs))
