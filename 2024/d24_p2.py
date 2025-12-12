# pip install z3

import itertools
import random
import sys

import z3

from d24_p1 import parse_file, get_bits

NBITS = 46
#NBITS = 6


def eval_expr(expr):
    if isinstance(expr, Expr):
        return expr.eval()
    return expr


class Expr:
    def eval(self):
        raise NotImplementedError


class Var(Expr):
    def __init__(self, name):
        self.name = name
        self.expr = None

    def eval(self):
        return self.expr.eval()

    def set(self, expr):
        self.expr = expr

    def swap(self, other):
        assert isinstance(self, Var)
        self.expr, other.expr = other.expr, self.expr

    def __repr__(self):
        return f'<Var:{self.name}>'


class BinOp(Expr):
    def __init__(self, op, left, right):
        self.op = op
        self.left = left
        self.right = right

    def eval(self):
        return self.op(eval_expr(self.left), eval_expr(self.right))

    def __repr__(self):
        return f'({self.left!r} {self.op.__name__} {self.right!r})'


def compute(context, commands):
    context.update({
        name: Var(name)
        for _, _, _, name in commands
    })
    for op, left, right, output in commands:
        context[output].set(BinOp(op, context[left], context[right]))
    return context


def get_var(variables, name):
    result = 0
    bits = get_bits(variables, name)
    for bit in bits:
        result = (result << 1) + bit

    return result


def set_var(variables, name, value):
    for k in variables:
        if k[0] == name:
            n = int(k[1:])
            variables[k] = (value >> n) & 1


def prove(formula):
    # z3.prove is not suitable because it always returns None
    solver = z3.Solver()
    solver.add(~formula)
    return solver.check() == z3.unsat


def graphviz_export(commands):
    output = []
    output.append('digraph {')

    for op, left, right, out in commands:
        op = op.__name__
        node = f'{op}_{left}_{right}_{out}'
        output.append(f'{node} [label={op}, shape=box]')
        output.append(f'{left} -> {node}')
        output.append(f'{right} -> {node}')
        output.append(f'{node} -> {out}')

    output.append('}')

    return '\n'.join(output)


if __name__ == '__main__':
    variables, commands = parse_file(sys.stdin)

    with open('/tmp/d24.dot', 'w') as f:
        print(graphviz_export(commands), file=f)

    x, y = z3.BitVecs('x y', NBITS)
    set_var(variables, 'x', x)
    set_var(variables, 'y', y)

    context = compute(variables, commands)

    last = 0

    for i in range(NBITS):
        zi = eval_expr(context[f'z{i:02}'])
        current = last + context.get(f'x{i:02}', 0) + context.get(f'y{i:02}', 0)
        result = prove(zi == current & 1)
        print(i, result)
        if not result:
            break
        last = current >> 1
