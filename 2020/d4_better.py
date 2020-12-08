import re
import sys

def parse_passport(content):
    fields = content.split()
    return dict(f.split(':') for f in fields)


def parse_passports():
    content = sys.stdin.read()
    return (parse_passport(p) for p in content.split('\n\n'))

def date_validator(start, end):
    return lambda v: len(v) == 4 and start <= int(v) <= end

def validate_height(v):
    if not (m := re.match(r'(\d+)(cm|in)$', p['hgt'])):
        return
    height, unit = m.groups()
    if unit == 'cm':
        return 150 <= int(height) <= 193
    else:
        return 59 <= int(height) <= 76

validators = {
    'byr': date_validator(1920, 2002),
    'iyr': date_validator(2010, 2020),
    'eyr': date_validator(2020, 2030),
    'hgt': validate_height,
    'hcl': lambda v: re.match(r'#[0-9a-f]{6}$', v),
    'ecl': lambda v: v in 'amb blu brn gry grn hzl oth'.split(),
    'pid': lambda v: len(v) == 9 and v.isdigit(),
}
keys = set(validators)

count = 0
for p in parse_passports():
    if not set(p) >= keys:
        continue
    if all(validator(p[key]) for key, validator in validators.items()):
        count += 1

print(count)
