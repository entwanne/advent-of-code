import sys
from functools import cache

from d11_p1 import parse_graph


class Graph:
    def __init__(self, graph):
        self.graph = graph
        self.colors = {}

    @cache
    def count_ways_to(self, start, end, color=None):
        if start == end:
            return 1

        ways = sum(self.count_ways_to(node, end, color=color) for node in self.graph.get(start, ()))
        if color and ways:
            self.colors.setdefault(start, color)

        return ways

    def get_dot(self):
        def _iter():
            yield 'digraph {'
            for node, color in self.colors.items():
                yield f'{node} [style=filled,fillcolor={color}]'
            for node, children in self.graph.items():
                for child in children:
                    yield f'{node} -> {child}'
            yield '}'

        return '\n'.join(_iter())


if __name__ == '__main__':
    graph = Graph(parse_graph(sys.stdin))
    graph.colors['svr'] = graph.colors['out'] = 'lightgreen'
    graph.colors['you'] = 'lightgreen'
    graph.colors['fft'] = 'red'
    graph.colors['dac'] = 'blue'

    print(
        graph.count_ways_to('svr', 'dac') * graph.count_ways_to('dac', 'fft') * graph.count_ways_to('fft', 'out')
        + graph.count_ways_to('svr', 'fft', color='green') * graph.count_ways_to('fft', 'dac', color='orange') * graph.count_ways_to('dac', 'out', color='purple'),
        file=sys.stderr,
    )
    print(graph.get_dot())
