import sys

from d03_p1 import parse_banks


def bank_max_joltage(bank, digits_count=12):
    digits = []
    first_idx = 0
    last_idx = len(bank) - digits_count + 1

    for _ in range(digits_count):
        b = bank[first_idx:last_idx]
        digit = max(b)
        digits.append(digit)
        first_idx += b.index(digit) + 1
        last_idx += 1

    return int(''.join(map(str, digits)))


if __name__ == '__main__':
    print(sum(bank_max_joltage(bank) for bank in parse_banks(sys.stdin)))
