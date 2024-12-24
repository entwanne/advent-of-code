# pip install z3

import itertools
import random
import sys

import z3

from d24_p1 import parse_file, get_bits

NBITS = 45
#NBITS = 6
sys.setrecursionlimit(30000)


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


def _solve_rec(variables, commands, swaps, done):
    if not swaps:
        variables = dict(variables)
        variables = compute(variables, commands)
        if prove(get_var(variables, 'z') == get_var(variables, 'x') & get_var(variables, 'y')):
            return done
        else:
            return None

    (output1, output2), *swaps = swaps
    r = solve_rec(variables, commands[:], swaps, done)
    if r is not None:
        return r
    elif output1 not in done and output2 not in done:
        swap = {
            output1: output2,
            output2: output1,
        }
        done = done | swap
        commands = [
            (op, left, right, swap.get(output, output))
            for op, left, right, output in commands
        ]
        return solve_rec(variables, commands, swaps, done)


def _solve(variables, commands):
    outputs = {cmd[-1] for cmd in commands}
    swaps = list(itertools.combinations(outputs, 2))
    return solve_rec(variables, commands, swaps, {})


def solve_rec(context, swaps, done):
    #print(len(swaps))
    print(len(swaps))
    if not swaps:
        #try:
        c = {k: eval_expr(v) for k, v in context.items()}
        #except:
        #    return None
        #x = eval_expr(get_var(context, 'x'))
        #y = eval_expr(get_var(context, 'y'))
        #z = eval_expr(get_var(context, 'z'))
        x = get_var(c, 'x')
        y = get_var(c, 'y')
        z = get_var(c, 'z')
        #return done if prove(z == x & y) else None
        return done if prove(z == x + y) else None
    if len(done) > 8:
        return None

    (output1, output2), *swaps = swaps
    r = solve_rec(context, swaps, done)
    if r is not None:
        return r
    elif output1 not in done and output2 not in done:
        swap = {
            output1: output2,
            output2: output1,
        }
        done = done | swap
        #context = context.copy()
        context[output1].swap(context[output2])
        try:
            return solve_rec(context, swaps, done)
        finally:
            context[output1].swap(context[output2])


def solve(context, dependencies, outputs):
    #swaps = list(itertools.combinations(outputs, 2))
    swaps = [
        (o1, o2)
        for o1, o2 in itertools.combinations(outputs, 2)
        # avoid cycles
        if o2 not in dependencies.get(o1, ()) and o1 not in dependencies.get(o2, ())
    ]
    print(len(swaps))
    return solve_rec(context, swaps, {})


def find_dependencies(context, expr):
    if isinstance(expr, Var):
        return {expr.name} | find_dependencies(context, expr.expr)
    elif isinstance(expr, BinOp):
        return find_dependencies(context, expr.left) | find_dependencies(context, expr.right)
    else:
        return set()


if __name__ == '__main__':
    variables, commands = parse_file(sys.stdin)

    x, y = z3.BitVecs('x y', NBITS)
    set_var(variables, 'x', x)
    set_var(variables, 'y', y)

    '''
    print(solve(variables, commands))
    '''
    context = compute(variables, commands)
    outputs = {cmd[-1] for cmd in commands}
    dependencies = {}
    for output in outputs:
        dependencies[output] = find_dependencies(context, context[output].expr)

    outputs = {o for o in outputs if o.startswith('z') or any(o in deps for k, deps in dependencies.items() if k.startswith('z'))}

    #ctx = {name: eval_expr(var) for name, var in ctx.items()}
    #z = get_var(ctx, 'z')
    #print(z)
    #print(prove(z == x & y))
    #print(solve(context, dependencies, outputs))
    last = 0
    ok_deps = set()
    for i in range(NBITS):
        zi = eval_expr(context[f'z{i:02}'])
        #print(k, zi, prove(zi == context[f'x{i:02}'] & context[f'y{i:02}']))
        current = last + context.get(f'x{i:02}', 0) + context.get(f'y{i:02}', 0)
        result = prove(zi == current & 1)
        print(i, prove(zi == current & 1))
        if result:
            ok_deps.update(dependencies[f'z{i:02}'])
        else:
            test_outputs = dependencies[f'z{i:02}'] #- ok_deps
            test_outputs |= {zzz for zzz in context if zzz.startswith('z') and int(zzz[1:]) >= i}
            print(test_outputs)
            swaps = [
                (o1, o2)
                for o1, o2 in itertools.combinations(test_outputs, 2)
                # avoid cycles
                if o2 not in dependencies.get(o1, ()) and o1 not in dependencies.get(o2, ())
            ]
            print(swaps)
            for o1, o2 in swaps:
                context[o1].swap(context[o2])
                nzi = eval_expr(context[f'z{i:02}'])
                #print(nzi)
                print(prove(nzi == current & 1))
                context[o1].swap(context[o2])
            break
        last = current >> 1
