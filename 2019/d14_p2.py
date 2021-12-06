import sys
from collections import Counter
from math import ceil


def parse_res(res):
    n, res = res.split()
    return res, int(n)


need_graph = {}
store = Counter({'ORE': 1_000_000_000_000})

for line in sys.stdin:
    needs, res = line.strip().split(' => ')
    res, n = parse_res(res)
    needs = (parse_res(need) for need in needs.split(', '))
    needs = {r: n for r, n in needs}
    need_graph[res] = n, needs


def get(res, n=1):
    if res in need_graph:
        pn, needs = need_graph[res]

        while store[res] < n:
            for need, nn in needs.items():
                if get(need, nn) != nn:
                    break
            else:
                store[res] += pn
                continue
            break

    n = min(n, store[res])
    store[res] -= n
    return n


def count(res):
    n = 0
    while get(res, 1) == 1:
        n += 1
        if n % 1000 == 0:
            print(n, store)
    print(n, store)
    return n


print(count('FUEL'))
