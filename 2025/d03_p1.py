import sys


def parse_banks(f):
    for line in f:
        yield [int(x) for x in line.strip()]


def bank_max_joltage(bank):
    first_digit = max(bank[:-1])
    idx = bank.index(first_digit)
    second_digit = max(bank[idx+1:])
    return first_digit * 10 + second_digit


if __name__ == '__main__':
    print(sum(bank_max_joltage(bank) for bank in parse_banks(sys.stdin)))
