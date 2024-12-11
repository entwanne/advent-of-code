import copy
import sys

from d22_p1 import parse_bricks, fall_bricks


def get_supports(supported_by):
    supports = {}
    for bid, sup in supported_by.items():
        supports.setdefault(bid, set())
        for sbid in sup:
            supports.setdefault(sbid, set()).add(bid)
    return supports


def count_fall(supported_by, supports, bid):
    supported_by = copy.deepcopy(supported_by)
    supports = copy.deepcopy(supports)
    queue = [bid]

    count = -1

    while queue:
        bid = queue.pop(0)
        count += 1
        for cid in supports[bid]:
            supported_by[cid].discard(bid)
            if not supported_by[cid]:
                queue.append(cid)

    return count


def count_falls(supported_by, supports):
    return sum(count_fall(supported_by, supports, bid) for bid in supports)


if __name__ == '__main__':
    bricks = parse_bricks(sys.stdin)
    supported_by = fall_bricks(bricks)
    supports = get_supports(supported_by)
    print(count_falls(supported_by, supports))
