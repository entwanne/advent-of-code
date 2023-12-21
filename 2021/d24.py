import itertools
import sys


class Value:
    def __add__(self, rhs):
        #return OpValue(operator.add, self, rhs)
        pass

    def __radd__(self, lhs):
        #return OpValue(operator.add, lhs, self)
        pass

    def __sub__(self, rhs):
        return SubOpValue(self, rhs)

    def __rsub__(self, lhs):
        return SubOpValue(lhs, self)

    def __floordiv__(self, rhs):
        return DivOpValue(self, rhs)

    def __rfloordiv__(self, lhs):
        return DivOpValue(lhs, self)

    def __values__(self):
        raise NotImplementedError

    def restrict(self, values):
        raise NotImplementedError


class _BinOpValue(Value):
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs

    def __repr__(self):
        lhs = repr(self.lhs)
        if ' ' in lhs:
            lhs = f'({lhs})'
        rhs = repr(self.rhs)
        if ' ' in rhs:
            rhs = f'({rhs})'
        return f'{lhs} {self.symbol} {rhs}'

    def __values__(self):
        return {
            self.op(lhs, rhs)
            for lhs, rhs in itertools.product(self.lhs.__values__(), self.rhs.__values__())
        }

    def restrict(self, values):
        change = True
        # only work with operator.sub currently
        while change:
            change = False

            lvalues = self.lhs.__values__()
            rvalues = self.rhs.__values__()
            if None not in lvalues:
                self.rhs.restrict({self.op(lv, v) for v in values for lv in lvalues})
                if self.rhs.__values__() != rvalues:
                    change = True

            lvalues = self.lhs.__values__()
            rvalues = self.rhs.__values__()
            if None not in rvalues:
                self.lhs.restrict({self.rev_op(v, rv) for v in values for rv in rvalues})
                if self.lhs.__values__() != lvalues:
                    change = True


class SubOpValue(_BinOpValue):
    symbol = '-'

    @staticmethod
    def op(lhs, rhs):
        return lhs - rhs

    @staticmethod
    def rev_op(lhs, rhs):
        return lhs + rhs


class DivOpValue(_BinOpValue):
    symbol = '/'

    @staticmethod
    def op(lhs, rhs):
        return lhs // rhs

    @staticmethod
    def rev_op(lhs, rhs):
        return lhs * rhs


class SetValue(Value):
    _id_seq = itertools.count(1)

    def __init__(self, *values):
        self.id = f'v{next(self._id_seq)}'
        if values:
            self.values = set(values)
        else:
            self.values = {None}

    def __repr__(self):
        if None in self.values:
            return f'{self.id}=int'
        return f'{self.id}={self.values!r}'

    def __values__(self):
        if None in self.values:
            return {None}
        return self.values

    def restrict(self, values):
        if None in self.values:
            self.values.clear()
            self.values.update(values)
        else:
            self.values.intersection_update(values)
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
queue = []

print(registers)
print(queue)

for cmd in reversed(commands):
    print('---')
    print(cmd)
    match cmd:
        case ('add', a, b):
            v1 = a.get()
            op = v1 - b.get()
            a.set(op)
        case ('mul', a, b):
            v1 = a.get()
            if b.get().__values__() == {0}:
                v1.restrict({0})
                a.set(SetValue())
            else:
                op = v1 // b.get()
                a.set(op)
        case ('eql', a, b):
            v1 = a.get()
            v1.restrict({0, 1})
            # Set new variable
            if v1.__values__() == {1}:
                a.set(b.get())
            else:
                a.set(SetValue())
        case ('inp', a):
            v = a.get()
            v.restrict(range(1, 10))
            queue.append(v)
            a.set(SetValue())
    print(registers)
    print(queue)
