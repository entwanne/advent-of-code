print(sum(1 if set(p) >= {'byr', 'iyr', 'eyr', 'hgt', 'hcl', 'ecl', 'pid'} and len(p['byr']) == 4 and 1920 <= int(p['byr']) <= 2002 and len(p['iyr']) == 4 and 2010 <= int(p['iyr']) <= 2020 and len(p['eyr']) == 4 and 2020 <= int(p['eyr']) <= 2030 and (m := __import__('re').match(r'(\d+)(cm|in)$', p['hgt'])) and (m.group(2) == 'cm' and 150 <= int(m.group(1)) <= 193 or m.group(2) == 'in' and 59 <= int(m.group(1)) <= 76) and __import__('re').match(r'#[0-9a-f]{6}$', p['hcl']) and p['ecl'] in 'amb blu brn gry grn hzl oth'.split() and len(p['pid']) == 9 and p['pid'].isdigit() else 0 for p in (dict(f.split(':') for f in p.split()) for p in __import__('sys').stdin.read().split('\n\n'))))