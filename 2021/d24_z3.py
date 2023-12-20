import itertools
import math
import sys

import z3

solver = z3.Optimize()

registers = {
    'w': 0,
    'x': 0,
    'y': 0,
    'z': 0,
}
inputq = []


class IntArg:
    def __init__(self, value):
        self.value = value

    def get(self):
        return self.value

    def __repr__(self):
        return repr(self.value)


class VarArg:
    def __init__(self, name):
        self.name = name

    def get(self):
        return registers[self.name]

    def set(self, value):
        registers[self.name] = value

    def __repr__(self):
        return self.name


def parse(f):
    for line in f:
        cmd, *args = line.split()
        args = (VarArg(arg) if arg in 'wxyz' else IntArg(int(arg)) for arg in args)
        yield (cmd, *args)


print('parse')
for cmd in parse(sys.stdin):
    match cmd:
        case ('inp', v):
            inp = z3.Int(f'v{len(inputq)}')
            solver.add(1 <= inp, inp <= 9)
            inputq.append(inp)
            v.set(inp)
        case ('eql', a, b):
            a.set(z3.If(a.get() == b.get(), 1, 0))
        case ('add', a, b):
            a.set(a.get() + b.get())
        case ('mul', a, b):
            a.set(a.get() * b.get())
        case ('div', a, b):
            solver.add(b.get() != 0)
            if isinstance(a.get(), int) and isinstance(b.get(), int):
                result = a.get() / b.get()
                result = math.floor(result) if result >= 0 else math.ceil(result)
                a.set(result)
            else:
                a.set(a.get() / b.get())
        case ('mod', a, b):
            solver.add(a.get() >= 0)
            solver.add(b.get() > 0)
            a.set(a.get() % b.get())

print('constraints')
solver.add(registers['z'] == 0)

result = 0
for q in inputq:
    result = result * 10 + q
solver.maximize(result)

print('check')
print(solver.check())

print('model')
print(solver.model())
