import sys

numbers = [int(n) for n in sys.stdin.read().split(',')]


def find_nth(nth):
    memory = {n: i for i, n in enumerate(numbers)}
    last = numbers[-1]
    a = len(numbers) - 1

    for i in range(len(numbers), nth):
        b = memory.get(last, a)
        memory[last] = a
        last = a - b
        a = i

    return last


print(find_nth(2020))
print(find_nth(30000000))
