# pip install z3-solver
import sys

import z3

from d17_p1 import OPCODES, literal, parse_program, run


def jnz(registers, value, output):
    if not isinstance(registers['A'], int):
        return True, value
    elif registers['A'] == 0:
        return
    return False, value


OPCODES[3] = jnz, literal


def run(solver, var, registers, data, pc=0, output=None):
    if output is None:
        output = []

    while 0 <= pc < len(data) - 1:
        opcode, arg = data[pc], data[pc + 1]
        op, argf = OPCODES[opcode]
        if argf is None:
            value = None
        else:
            value = argf(registers, arg)

        l = len(output)
        ret = op(registers, value, output)

        # Check last output value
        if len(output) > l:
            if len(output) > len(data):
                return 0
            solver.add(output[l] == data[l])
            if solver.check() != z3.sat:
                return 0

        if ret is None:
            pc += 2
        else:
            multi, ret = ret
            if multi:
                # In case of variable jump
                # Solve branch in case of jump
                solver.push()
                solver.add(registers['A'] != 0)
                a = run(solver, var, registers.copy(), data, ret, list(output))
                solver.pop()
                # Solve in case on no brunch
                solver.add(registers['A'] == 0)
                b = run(solver, var, registers, data, pc + 2, output)
                # Return minimum solution between both branches
                if a and b:
                    return min(a, b)
                else:
                    return a or b
            else:
                pc = ret

    if len(output) == len(data) and solver.check() == z3.sat:
        m = solver.model()
        return m[var].as_long()
    return 0


def solve(registers, data):
    solver = z3.Solver()

    var = z3.BitVec('A', 64)
    registers['A'] = var

    result = None

    # Continue until we find the best solution
    while True:
        solver.push()
        r = run(solver, var, registers.copy(), data)
        solver.pop()
        if not r:
            break
        if result is None or r < result:
            result = r
            solver.add(var < r)

    return result


if __name__ == '__main__':
    print(solve(*parse_program(sys.stdin)))
