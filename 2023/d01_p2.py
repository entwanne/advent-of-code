import re
import sys

DIGITS = {
    'one': 1,
    'two': 2,
    'three': 3,
    'four': 4,
    'five': 5,
    'six': 6,
    'seven': 7,
    'eight': 8,
    'nine': 9,
    
}

pattern = re.compile(rf'\d|{'|'.join(DIGITS)}')
last_pattern = re.compile(rf'(?s:.*)({pattern.pattern})')

total = 0

for line in sys.stdin:
    first_digit = pattern.search(line)[0]
    first_digit = int(first_digit) if first_digit.isdigit() else DIGITS[first_digit]

    last_digit = last_pattern.search(line)[1]
    last_digit = int(last_digit) if last_digit.isdigit() else DIGITS[last_digit]

    total += first_digit * 10 + last_digit

print(total)
