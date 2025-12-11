import sys
from functools import cache

from d11_p1 import parse_graph


class Graph:
    def __init__(self, graph):
        self.graph = graph

    @cache
    def count_ways_to(self, start, end):
        if start == end:
            return 1
        return sum(self.count_ways_to(node, end) for node in self.graph.get(start, ()))


if __name__ == '__main__':
    graph = Graph(parse_graph(sys.stdin))
    print(
        graph.count_ways_to('svr', 'dac') * graph.count_ways_to('dac', 'fft') * graph.count_ways_to('fft', 'out')
        + graph.count_ways_to('svr', 'fft') * graph.count_ways_to('fft', 'dac') * graph.count_ways_to('dac', 'out')
    )
