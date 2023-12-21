import itertools
import operator
import sys


class Value:
    #def __add__(self, rhs):
    #    #return OpValue(operator.add, self, rhs)
    #    pass

    #def __radd__(self, lhs):
    #    #return OpValue(operator.add, lhs, self)
    #    pass

    #def __sub__(self, rhs):
    #    return SubOpValue(self, rhs)

    #def __rsub__(self, lhs):
    #    return SubOpValue(lhs, self)

    #def __floordiv__(self, rhs):
    #    return DivOpValue(self, rhs)

    #def __rfloordiv__(self, lhs):
    #    return DivOpValue(lhs, self)

    def __values__(self):
        raise NotImplementedError

    def restrict(self, values):
        raise NotImplementedError


'''
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
'''


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
        lhs_ok = set()
        rhs_ok = set()
        for lhs, rhs in itertools.product(self.lhs.__values__(), self.rhs.__values__()):
            if self.op(lhs, rhs) in values:
                lhs_ok.add(lhs)
                rhs_ok.add(rhs)
        self.lhs.restrict(lhs_ok)
        self.rhs.restrict(rhs_ok)

        '''
        lhs_values = self.lhs.__values__()
        rhs_values = self.rhs.__values__()

        changes = True
        while changes:
            changes = False
            lhs_ok = set()
            rhs_ok = set()

            for lhs, rhs in itertools.product(lhs_values, rhs_values):
                if self.op(lhs, rhs) in values:
                    lhs_ok.add(lhs)
                    rhs_ok.add(rhs)

            if lhs_ok != lhs_values:
                self.lhs.restrict(lhs_ok)
                lhs_values = lhs_ok
                changes = True
            if rhs_ok != rhs_values:
                self.rhs.restrict(rhs_ok)
                rhs_values = rhs_ok
                changes = True
        '''


class AddOpValue(_BinOpValue):
    symbol = '+'
    op = operator.add


class MulOpValue(_BinOpValue):
    symbol = '*'
    op = operator.mul


class EqualValue(_BinOpValue):
    symbol = '=='
    op = operator.eq

    def restrict(self, values):
        values = values & {0, 1}
        if values == {1}:
            self.lhs.restrict(self.rhs.__values__())
            self.rhs.restrict(self.lhs.__values__())


class SetValue(Value):
    _id_seq = itertools.count(1)

    def __init__(self, *values):
        self.id = f'v{next(self._id_seq)}'
        assert values
        self.values = set(values)

    def __repr__(self):
        return f'{self.id}={self.values!r}'

    def __values__(self):
        return self.values

    def restrict(self, values):
        self.values.intersection_update(values)
        assert self.values


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
        return f'<{self.name}>'


def parse(f):
    for line in f:
        cmd, *args = line.split()
        args = [VarArg(arg) if arg in 'wxyz' else IntArg(int(arg)) for arg in args]
        yield (cmd, *args)


inputs = []
registers = {
    'w': IntValue(0),
    'x': IntValue(0),
    'y': IntValue(0),
    'z': IntValue(0),
}

for cmd in parse(sys.stdin):
    match cmd:
        case ('inp', v):
            new = SetValue(*range(1, 10))
            inputs.append(new)
            v.set(new)
        case ('add', v1, v2):
            v1.set(AddOpValue(v1.get(), v2.get()))
        case ('mul', v1, v2):
            #if v2.get().__values__() == {0}:
            if isinstance(v2, IntArg) and v2.get().__values__() == {0}:
                v1.set(IntValue(0))
            else:
                v1.set(MulOpValue(v1.get(), v2.get()))
        case ('eql', v1, v2):
            v1.set(EqualValue(v1.get(), v2.get()))
    print(cmd)


#print(registers)
#print({name: v.__values__() for name, v in registers.items()})
#print(inputs)
for _ in range(2):
    registers['z'].restrict({0})
#print(registers)
print({name: v.__values__() for name, v in registers.items()})
print(inputs)
