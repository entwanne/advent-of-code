import operator
import sys


OPS = {
    'AND': operator.and_,
    'OR': operator.or_,
    'XOR': operator.xor,
}


def parse_vars(f):
    variables = {}

    for line in f:
        line = line.strip()
        if not line:
            break

        name, value = line.split(': ')
        variables[name] = int(value)

    return variables


def parse_commands(f):
    for line in f:
        left, op, right, _, output = line.split()
        yield (OPS[op], left, right, output)


def parse_file(f):
    return parse_vars(f), list(parse_commands(f))


def compute(variables, commands):
    while commands:
        todel = []
        for i, (op, left, right, output) in enumerate(commands):
            if left in variables and right in variables:
                variables[output] = op(variables[left], variables[right])
                todel.append(i)

        for i in reversed(todel):
            del commands[i]

    return variables


def get_bits(variables, name):
    return [
        bit
        for _, bit in sorted(((k, v) for k, v in variables.items() if k.startswith(name)), reverse=True)
    ]


def get_var(variables, name):
    return int(''.join(map(str, get_bits(variables, name))), 2)


if __name__ == '__main__':
    print(get_var(compute(*parse_file(sys.stdin)), 'z'))
