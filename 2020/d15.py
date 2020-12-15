import sys

numbers = [int(n) for n in sys.stdin.read().split(',')]


def find_nth(nth):
    memory = {n: (i, None) for i, n in enumerate(numbers)}
    a, b = memory[numbers[-1]]

    for i in range(len(numbers), nth):
        if b is None:
            last = 0
        else:
            last = a - b
        a, _ = memory.get(last, (None, None))
        memory[last] = a, b = i, a

    return last


print(find_nth(2020))
print(find_nth(30000000))
