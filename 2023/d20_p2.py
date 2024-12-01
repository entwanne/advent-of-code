# pip install z3-solver
import itertools
import math
import sys

from d20_p1 import ConjunctionModule, parse_modules, parse_specs, run_cycle


def get_callback(mod, i, results):
    def callback(output, sender, signal):
        if output == mod and signal == 'high':
            results[sender] = i

    return callback


def count_cycles(modules):
    mod, = modules['rx'].inputs
    assert isinstance(mod, ConjunctionModule)

    results = {}
    for i in itertools.count(1):
        run_cycle(modules, get_callback(mod, i, results))

        if all(i in results for i in mod.inputs):
            break

    return math.lcm(*results.values())



if __name__ == '__main__':
    print(count_cycles(parse_modules(parse_specs(sys.stdin))))
