import sys

numbers = [int(n) for n in sys.stdin.read().split(',')]


def find_nth(nth):
    memory = [-1] * max(nth, *numbers)
    for i, n in enumerate(numbers):
        memory[n] = i

    last = numbers[-1]
    a = len(numbers) - 1

    for i in range(len(numbers), nth):
        b = memory[last]
        if b < 0:
            b = a
        memory[last] = a
        last = a - b
        a = i

    return last


print(find_nth(2020))
print(find_nth(30000000))
