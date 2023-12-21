import sys
from collections import namedtuple
from functools import partial


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


handlers = {}


def register(t):
    return partial(handlers.__setitem__, t)


@register(TextRule)
def _match_text(s, rule, rules):
    if s.startswith(rule.text):
        return True, s[len(rule.text):]
    return False, s


@register(CallRule)
def _match_call(s, rule, rules):
    return _match(s, rules[rule.name], rules)


@register(AndRule)
def _match_and(s, rule, rules):
    for sub in rule.rules:
        ret, s = _match(s, sub, rules)
        if not ret:
            return False, s
    return True, s


@register(OrRule)
def _match_or(s, rule, rules):
    for sub in rule.rules:
        ret, s2 = _match(s, sub, rules)
        if ret:
            return True, s2
    return False, s


def _match(s, rule, rules):
    if not s:
        return False, ''

    handler = handlers[type(rule)]
    return handler(s, rule, rules)


def match(s, rule, rules):
    ret, s = _match(s, rule, rules)
    return ret and not s


rules = dict(rule.strip().split(': ') for rule in rules.splitlines())
rules = {name: parse_rule(r) for name, r in rules.items()}

entries = [line.strip() for line in entries.splitlines()]

# p1

print(sum(1 for l in entries if match(l, rules['0'], rules)))

# p2

@register(TextRule)
def _match_text(s, rule, rules):
    ok = {v[len(rule.text):] for v in s if v.startswith(rule.text)}
    if ok:
        return True, ok
    return False, ok


@register(OrRule)
def _match_or(s, rule, rules):
    ok = set()
    for sub in rule.rules:
        ret, s2 = _match(s, sub, rules)
        if ret:
            ok |= s2
    if ok:
        return True, ok
    return False, s


_old_match = _match


def _match(s, rule, rules):
    s = {v for v in s if v}
    return _old_match(s, rule, rules)


def match(s, rule, rules):
    ret, s = _match({s}, rule, rules)
    return ret and not all(s)


rules['8'] = parse_rule('42 | 42 8')
rules['11'] = parse_rule('42 31 | 42 11 31')

print(sum(1 for l in entries if match(l, rules['0'], rules)))
