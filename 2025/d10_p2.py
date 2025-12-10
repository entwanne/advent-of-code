import sys

import z3

from d10_p1 import parse_lights


def min_buttons(expected_jolts, buttons):
    s = z3.Optimize()

    jolts = [0] * len(expected_jolts)
    presses = [z3.Int(f'p{i}') for i, _ in enumerate(buttons, start=1)]

    for p in presses:
        s.add(p >= 0)

    for p, button in zip(presses, buttons):
        for idx in button:
            jolts[idx] += p

    for actual, expected in zip(jolts, expected_jolts):
        s.add(actual == expected)

    result_expr = sum(p for p in presses)
    s.minimize(result_expr)

    assert s.check() == z3.sat
    return s.model().evaluate(result_expr).as_long()


if __name__ == '__main__':
    print(sum(min_buttons(expected, buttons) for _, buttons, expected in parse_lights(sys.stdin)))
