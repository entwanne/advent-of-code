import sys
from functools import cached_property


QUEUE = []


class Module:
    def __init__(self, name):
        self.name = name
        self.outputs = []
        self.inputs = []

    def __repr__(self):
        outputs = [o.name for o in self.outputs]
        inputs = [i.name for i in self.inputs]
        return f'<{type(self).__name__}:{self.name} outputs={outputs!r} inputs={inputs!r}>'

    def send(self, sender, signal):
        for output in self.outputs:
            #print(f'{self.name} -{signal}-> {output.name}')
            QUEUE.append((output, self, signal))


class FlipFlopModule(Module):
    def __init__(self, name):
        super().__init__(name)
        self.enabled = False

    def send(self, sender, signal):
        if signal == 'low':
            self.enabled = not self.enabled
            super().send(sender, 'high' if self.enabled else 'low')


class ConjunctionModule(Module):
    def __init__(self, name):
        super().__init__(name)

    @cached_property
    def memory(self):
        return {mod: 'low' for mod in self.inputs}

    def send(self, sender, signal):
        self.memory[sender] = signal
        signal = 'low' if set(self.memory.values()) == {'high'} else 'high'
        super().send(sender, signal)


def parse_specs(f):
    for line in f:
        name, args = line.strip().split(' -> ')
        if name.startswith('%'):
            mod_cls = FlipFlopModule
            name = name.removeprefix('%')
        elif name.startswith('&'):
            mod_cls = ConjunctionModule
            name = name.removeprefix('&')
        else:
            mod_cls = Module
        yield mod_cls, name, args.split(', ')


def parse_modules(specs):
    modules = {}
    links = []

    for mod_cls, name, outputs in specs:
        modules[name] = mod_cls(name)
        links.extend((name, out) for out in outputs)

    for in_name, out_name in links:
        if out_name not in modules:
            modules[out_name] = Module(out_name)
        modules[in_name].outputs.append(modules[out_name])
        modules[out_name].inputs.append(modules[in_name])

    return modules


def run_cycle(modules, callback=None):
    high = low = 0
    QUEUE.append((modules['broadcaster'], None, 'low'))

    while QUEUE:
        output, sender, signal = QUEUE.pop(0)
        if signal == 'high':
            high += 1
        else:
            low += 1
        if callback:
            callback(output, sender, signal)
        output.send(sender, signal)

    return high, low


def debug(output, sender, signal):
    print(f'{sender.name if sender else 'button'} -{signal}-> {output.name}')


if __name__ == '__main__':
    modules = parse_modules(parse_specs(sys.stdin))
    high = low = 0
    for _ in range(1000):
        # h, l = run_cycle(modules, debug)
        h, l = run_cycle(modules)
        high += h
        low += l
    print(high * low)
