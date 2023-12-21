import itertools
import operator
import sys


class Value:
    def __add__(self, rhs):
        return OpValue(operator.add, self, rhs)

    def __radd__(self, lhs):
        return OpValue(operator.add, lhs, self)

    def __sub__(self, rhs):
        return OpValue(operator.sub, self, rhs)

    def __rsub__(self, lhs):
        return OpValue(operator.sub, lhs, self)

    def __values__(self):
        raise NotImplementedError

    def restrict(self, values):
        raise NotImplementedError


class OpValue(Value):
    def __init__(self, op, lhs, rhs):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        return repr((self.op.__name__, self.lhs, self.rhs))

    def __values__(self):
        return {
            self.op(*args)
            for args in itertools.product(self.lhs.__values__(), self.rhs.__values__())
        }

    def restrict(self, values):
        change = True
        # only work with operator.sub currently
        while change:
            change = False

            lvalues = self.lhs.__values__()
            rvalues = self.rhs.__values__()
            if None not in lvalues:
                self.rhs.restrict({lv - v for v in values for lv in lvalues})
                if self.rhs.__values__() != rvalues:
                    change = True

            lvalues = self.lhs.__values__()
            rvalues = self.rhs.__values__()
            if None not in rvalues:
                self.lhs.restrict({v + rv for v in values for rv in rvalues})
                if self.lhs.__values__() != lvalues:
                    change = True


class SetValue(Value):
    def __init__(self, *values):
        if values:
            self.values = set(values)
        else:
            self.values = {None}

    def __repr__(self):
        if None in self.values:
            return 'int'
        return repr(self.values)

    def __values__(self):
        if None in self.values:
            return {None}
        return self.values

    def restrict(self, values):
        print(self.values, values)
        if None in self.values:
            self.values.clear()
            self.values.update(values)
        else:
            self.values.intersection_update(values)
        print('->', self.values)
        if not self.values:
            raise ValueError


class IntValue(SetValue):
    def __init__(self, value):
        super().__init__(value)


class IntArg:
    def __init__(self, value):
        self.value = IntValue(value)

    def get(self):
        return self.value

    def set(self, value):
        raise ValueError

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
        return f'<{self.name}={self.get()!r}>'


def parse(f):
    for line in f:
        cmd, *args = line.split()
        args = [VarArg(arg) if arg in 'wxyz' else IntArg(int(arg)) for arg in args]
        yield (cmd, *args)


commands = list(parse(sys.stdin))

registers = {
    'w': SetValue(),
    'x': SetValue(),
    'y': SetValue(),
    'z': IntValue(0),
}
print(registers)

for cmd in reversed(commands):
    print(cmd)
    match cmd:
        case ('add', a, b):
            #v = registers[a.name]
            v1 = a.get()
            #op = OpValue(operator.add, v, b)
            #print('add', v, a, b)
            op = v1 - b.get()
            #print(op)
            #print(op.__values__())
            a.set(op)
        case ('eql', a, b):
            #print('eql', a, b)
            v1 = a.get()
            #print('before', v1.__values__())
            v1.restrict({0, 1})
            #print('after', v1.__values__())
            # Set new variable
            if v1.__values__ == {0}:
                # if == 0, retrict a.values <-> b.values
                a.set(b.get())
            else:
                a.set(SetValue())
