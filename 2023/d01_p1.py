import sys

total = 0

for line in sys.stdin:
    first_digit = next(c for c in line if c.isdigit())
    last_digit = next(c for c in reversed(line) if c.isdigit())
    total += int(first_digit + last_digit)

print(total)
