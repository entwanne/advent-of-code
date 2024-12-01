import math
import sys


class Variable:
    def __init__(self, name, start=1, stop=4000):
        self.name = name
        self.range = range(start, stop + 1)

    def __repr__(self):
        return f'<{self.name}:{self.range.start}:{self.range.stop - 1}>'

    def __len__(self):
        return len(self.range)

    def apply(self, op, value):
        match op:
            case '<':
                self.range = range(self.range.start, min(self.range.stop, value))
            case '>':
                self.range = range(max(self.range.start, value + 1), self.range.stop)


def parse_rule(r):
    if ':' not in r:
        return (r, None)
    cond, output = r.split(':')
    if '<' in cond:
        name, value = cond.split('<')
        value = int(value)
        cond = ('<', name, int(value))
    else:
        name, value = cond.split('>')
        cond = ('>', name, int(value))
    return (output, cond)


def parse_workflows(f):
    for line in f:
        line = line.strip()
        if not line:
            break
        name, rules = line.split('{')
        rules = rules.removesuffix('}')
        rules = [parse_rule(r) for r in rules.split(',')]
        yield name, rules


def find_solutions(workflows, name='in'):
    if name == 'A':
        return [[]]
    elif name == 'R':
        return []

    rules = workflows[name]
    conditions = []
    solutions = []

    for output, condition in rules:
        for sol in find_solutions(workflows, output):
            solutions.append(conditions + [condition] + sol if condition else conditions + sol)
        if condition:
            op, name, value = condition
            if op == '<':
                rev_op = '>'
                value -= 1
            else:
                rev_op = '<'
                value += 1
            conditions.append((rev_op, name, value))

    return solutions


def count_solutions(workflows):
    solutions = find_solutions(workflows)
    total = 0

    for sol in solutions:
        data = {name: Variable(name) for name in 'xmas'}

        for op, name, value in sol:
            data[name].apply(op, value)

        total += math.prod(len(v) for v in data.values())

    return total


if __name__ == '__main__':
    print(count_solutions(dict(parse_workflows(sys.stdin))))
