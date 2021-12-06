import sys
from collections import Counter
from math import ceil


def parse_res(res):
    n, res = res.split()
    return res, int(n)


need_graph = {}
store = Counter()
ores = Counter()

for line in sys.stdin:
    needs, res = line.strip().split(' => ')
    res, n = parse_res(res)
    needs = (parse_res(need) for need in needs.split(', '))
    needs = {r: n for r, n in needs}
    need_graph[res] = n, needs


def get(res, n=1):
    if res not in need_graph:
        ores[res] += n
        return

    pn, needs = need_graph[res]

    while store[res] < n:
        for need, nn in needs.items():
            get(need, nn)
        store[res] += pn

    store[res] -= n


get('FUEL')
print(ores['ORE'])
