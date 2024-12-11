import sys


class Rule:
    def __init__(self, output, condition=None):
        self.output = output
        self.condition = condition

    def apply(self, data):
        if self.condition is None or self.condition(data):
            return self.output


def parse_rule(r):
    if ':' not in r:
        return Rule(output=r)
    cond, output = r.split(':')
    if '<' in cond:
        name, value = cond.split('<')
        value = int(value)
        cond = lambda data: data[name] < value
    else:
        name, value = cond.split('>')
        value = int(value)
        cond = lambda data: data[name] > value
    return Rule(output, cond)


def parse_workflows(f):
    for line in f:
        line = line.strip()
        if not line:
            break
        name, rules = line.split('{')
        rules = rules.removesuffix('}')
        rules = [parse_rule(r) for r in rules.split(',')]
        yield name, rules


def parse_inputs(f):
    for line in f:
        line = line.strip()
        yield eval(f'dict({line[1:-1]})')


def parse_file(f):
    return dict(parse_workflows(f)), list(parse_inputs(f))


def apply(workflows, data):
    wname = 'in'
    while wname not in {'A', 'R'}:
        for rule in workflows[wname]:
            output = rule.apply(data)
            if output is not None:
                wname = output
                break
    return wname == 'A'


if __name__ == '__main__':
    workflows, inputs = parse_file(sys.stdin)
    print(sum(v for data in inputs if apply(workflows, data) for v in data.values()))
