import re
import sys

def parse_passport(content):
    fields = content.split()
    return dict(f.split(':') for f in fields)


def parse_passports():
    content = sys.stdin.read()
    return (parse_passport(p) for p in content.split('\n\n'))


def p1():
    count = 0
    for p in parse_passports():
        if set(p) >= {'byr', 'iyr', 'eyr', 'hgt', 'hcl', 'ecl', 'pid'}:
            count += 1
    print(count)


def p2():
    count = 0
    for p in parse_passports():
        if not set(p) >= {'byr', 'iyr', 'eyr', 'hgt', 'hcl', 'ecl', 'pid'}:
            continue

        if len(p['byr']) != 4 or not (1920 <= int(p['byr']) <= 2002):
            continue
        if len(p['iyr']) != 4 or not (2010 <= int(p['iyr']) <= 2020):
            continue
        if len(p['eyr']) != 4 or not (2020 <= int(p['eyr']) <= 2030):
            continue

        if not (m := re.match(r'(\d+)(cm|in)$', p['hgt'])):
            continue
        if m.group(2) == 'cm' and not (150 <= int(m.group(1)) <= 193):
            continue
        if m.group(2) == 'in' and not (59 <= int(m.group(1)) <= 76):
            continue

        if not re.match(r'#[0-9a-f]{6}$', p['hcl']):
            continue

        if p['ecl'] not in 'amb blu brn gry grn hzl oth'.split():
            continue

        if len(p['pid']) != 9 or not p['pid'].isdigit():
            continue

        count += 1
    print(count)

p2()
