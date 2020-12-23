import sys

class Node:
    def __init__(self, value):
        self.value = value
        self.next = self.prev = None


class Deque:
    def __init__(self, values):
        cache = self.cache = {}

        prev = None
        for v in values:
            node = Node(v)
            cache[v] = node
            if prev is None:
                first = node
            else:
                prev.next = node
                node.prev = prev
            prev = node

        prev.next = first
        first.prev = prev

        self.current = first

    def popnext(self):
        node = self.current.next
        self.current.next = node.next
        node.next.prev = self.current

        node.next = node.prev = None
        del self.cache[node.value]
        return node

    def insertnext(self, node):
        node.next = self.current.next
        node.prev = self.current
        self.current.next = node
        node.next.prev = node
        self.cache[node.value] = node

    def jumpto(self, value):
        self.current = self.cache[value]

    def __iter__(self):
        current = self.current
        yield current
        current = current.next
        while current is not self.current:
            yield current
            current = current.next


def game(cups, iterations, max_value):
    for _ in range(iterations):
        pick = [cups.popnext() for _ in range(3)]
        pick_values = {c.value for c in pick}

        dest = cups.current.value - 1
        if dest <= 0:
            dest = max_value
        while dest in pick_values:
            dest -= 1
            if dest <= 0:
                dest = max_value

        old = cups.current
        cups.jumpto(dest)

        for node in reversed(pick):
            cups.insertnext(node)

        cups.current = old.next

    cups.jumpto(1)
    return cups


init = [int(x) for x in sys.stdin.read().strip()]

# p1

max_value = max(init)
cups = game(Deque(init), 100, max_value)
print(''.join(str(c.value) for c in cups)[1:])

# p2

cups = list(init)
cups += list(range(max_value+1, 1000001))
cups = Deque(cups)

cups = game(cups, 10000000, 1000000)
print(cups.current.next.value*cups.current.next.next.value)
