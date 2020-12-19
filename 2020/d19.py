import sys
from collections import namedtuple


rules, entries = sys.stdin.read().split('\n\n')

TextRule = namedtuple('TextRule', ('text',))
CallRule = namedtuple('CallRule', ('name',))
AndRule = namedtuple('AndRule', ('rules',))
OrRule = namedtuple('OrRule', ('rules',))

def parse_simple_rule(s):
    if s.startswith('"') and s.endswith('"'):
        return TextRule(s[1:-1])
    return CallRule(s)

def parse_and_rule(s):
    subrules = [parse_simple_rule(r) for r in s.split()]
    if len(subrules) == 1:
        return subrules[0]
    else:
        return AndRule(subrules)

def parse_rule(s):
    subrules = [parse_and_rule(r) for r in s.split(' | ')]
    if len(subrules) == 1:
        return subrules[0]
    else:
        return OrRule(subrules)

def _match(s, rule, rules):
    if not s:
        return False, ''

    if isinstance(rule, OrRule):
        for sub in rule.rules:
            ret, s2 = _match(s, sub, rules)
            if ret:
                return True, s2
        return False, s
    if isinstance(rule, AndRule):
        for sub in rule.rules:
            ret, s = _match(s, sub, rules)
            if not ret:
                return False, s
        return True, s
    if isinstance(rule, CallRule):
        return _match(s, rules[rule.name], rules)

    if s.startswith(rule.text):
        return True, s[len(rule.text):]
    return False, s


def match(s, rule, rules):
    ret, s = _match(s, rule, rules)
    return ret and not s

rules = dict(rule.strip().split(': ') for rule in rules.splitlines())
rules = {name: parse_rule(r) for name, r in rules.items()}

entries = [line.strip() for line in entries.splitlines()]

# p1

print(sum(1 for l in entries if match(l, rules['0'], rules)))

# p2

def _match(s, rule, rules):
    s = {v for v in s if v}
    if not s:
        return False, s

    if isinstance(rule, OrRule):
        ok = set()
        for sub in rule.rules:
            ret, s2 = _match(s, sub, rules)
            if ret:
                ok |= s2
        if ok:
            return True, ok
        return False, s
    if isinstance(rule, AndRule):
        for sub in rule.rules:
            ret, s = _match(s, sub, rules)
            if not ret:
                return False, s
        return True, s
    if isinstance(rule, CallRule):
        return _match(s, rules[rule.name], rules)

    ok = {v[len(rule.text):] for v in s if v.startswith(rule.text)}
    if ok:
        return True, ok
    return False, ok

def match(s, rule, rules):
    ret, s = _match({s}, rule, rules)
    return ret and not all(s)

rules['8'] = parse_rule('42 | 42 8')
rules['11'] = parse_rule('42 31 | 42 11 31')

print(sum(1 for l in entries if match(l, rules['0'], rules)))
