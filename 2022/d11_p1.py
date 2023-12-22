import operator
import re
import sys

pattern = re.compile(
    '''Monkey\ (?P<id>\d+):
  Starting\ items: (?P<items>.+)
  Operation: new = (?P<lhs>.+) (?P<op>.) (?P<rhs>.+)
  Test: divisible by (?P<div>\d+)
    If true: throw to monkey (?P<id_true>\d+)
    If false: throw to monkey (?P<id_false>\d+)''',
)
operations = {
    '+': operator.add,
    '*': operator.mul,
}

def parse(f):
    content = f.read()

    for block in pattern.finditer(content):
        yield {
            'id': int(block['id']),
            'op': block['op'],
            'lhs': int(block['lhs']) if block['lhs'].isdigit() else block['lhs'],
            'rhs': int(block['rhs']) if block['rhs'].isdigit() else block['rhs'],
            'div': int(block['div']),
            'id_true': int(block['id_true']),
            'id_false': int(block['id_false']),
            'items': [int(item) for item in block['items'].split(', ')],
        }


monkeys = list(parse(sys.stdin))
queues = {}

for monkey in monkeys:
    queues[monkey['id']] = monkey.pop('items')

counts = {m['id']: 0 for m in monkeys}

for n in range(20):
    for monkey in monkeys:
        queue = queues[monkey['id']]
        while queue:
            item = queue.pop(0)
            counts[monkey['id']] += 1
            lhs = item if monkey['lhs'] == 'old' else monkey['lhs']
            rhs = item if monkey['rhs'] == 'old' else monkey['rhs']
            result = operations[monkey['op']](lhs, rhs) // 3
            next_id = monkey['id_true'] if result % monkey['div'] == 0 else monkey['id_false']
            queues[next_id].append(result)


print(operator.mul(*sorted(counts.values())[-2:]))
