import sys


def mix(a, b):
    return a ^ b


def prune(a):
    return a % 16777216


def get_next(secret):
    secret = prune(mix(secret, secret * 64))
    secret = prune(mix(secret, secret // 32))
    secret = prune(mix(secret, secret * 2048))
    return secret


def get_nexts(secret):
    while True:
        secret = get_next(secret)
        yield secret


def iterate(s, n=2000):
    for s, _ in zip(get_nexts(s), range(n)):
        pass
    return s


def parse_file(f):
    return map(int, f)


if __name__ == '__main__':
    print(sum(iterate(i) for i in parse_file(sys.stdin)))
