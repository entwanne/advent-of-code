import operator
import sys


lines = [line.strip().replace(' ', '') for line in sys.stdin]


def eval_expr(s, operators):
    level = 0
    min_level = None
    op_pos = None
    op_func = None
    op_prio = None

    for i, c in enumerate(s):
        if c == '(':
            level += 1
        elif c == ')':
            level -= 1
        else:
            if min_level is None or level < min_level:
                min_level = level

            if c in operators:
                f, p = operators[c]
                p = level, p
                if op_prio is None or p <= op_prio:
                    op_pos, op_func, op_prio = i, f, p

    if min_level:
        s = s[min_level:-min_level]

    if op_pos is not None:
        op_pos -= min_level
        s1 = s[:op_pos]
        s2 = s[op_pos+1:]
        return op_func(eval_expr(s1, operators), eval_expr(s2, operators))

    return int(s)


operators = {
    '+': (operator.add, 1),
    '*': (operator.mul, 1),
}
print(sum(eval_expr(s, operators) for s in lines))


operators = {
    '+': (operator.add, 2),
    '*': (operator.mul, 1),
}
print(sum(eval_expr(s, operators) for s in lines))
