import sys


def literal(registers, arg):
    return arg


def combo(registers, arg):
    match arg:
        case 0 | 1 | 2 | 3:
            return arg
        case 4:
            return registers['A']
        case 5:
            return registers['B']
        case 6:
            return registers['C']
        case _:
            raise ValueError


def div(name):
    def inner(registers, value, output):
        registers[name] = registers['A'] >> value

    return inner


def bxl(registers, value, output):
    b = registers['B']
    registers['B'] ^= value


def bst(registers, value, output):
    registers['B'] = value & 0b111


def jnz(registers, value, output):
    if registers['A'] == 0:
        return
    return value


def bxc(registers, _value, output):
    bxl(registers, registers['C'], output)


def out(registers, value, output):
    output.append(value & 0b111)


OPCODES = {
    0: (div('A'), combo),
    1: (bxl, literal),
    2: (bst, combo),
    3: (jnz, literal),
    4: (bxc, None),
    5: (out, combo),
    6: (div('B'), combo),
    7: (div('C'), combo),
}


def parse_registers(f):
    registers = {}

    for line in f:
        line = line.strip()
        if not line.startswith('Register'):
            break

        _, name, value = line.split()
        name = name.removesuffix(':')
        registers[name] = int(value)

    return registers


def parse_program(f):
    registers = parse_registers(f)
    line = f.read().strip()
    assert line.startswith('Program:')
    _, data = line.split()
    data = list(map(int, data.split(',')))
    return registers, data


def run(registers, data):
    output = []
    pc = 0

    while 0 <= pc < len(data) - 1:
        opcode, arg = data[pc], data[pc + 1]
        op, argf = OPCODES[opcode]
        if argf is None:
            value = None
        else:
            value = argf(registers, arg)

        ret = op(registers, value, output)
        if ret is None:
            pc += 2
        else:
            pc = ret

    return output


if __name__ == '__main__':
    output = run(*parse_program(sys.stdin))
    print(','.join(map(str, output)))
