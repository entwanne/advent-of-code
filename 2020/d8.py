import sys

commands = []
for line in sys.stdin:
    cmd, arg = line.split()
    arg = int(arg)
    commands.append((cmd, arg))

# p1

acc = 0
i = 0
visited = set()

while True:
    if i in visited:
        break
    visited.add(i)
    cmd, arg = commands[i]
    if cmd == 'acc':
        acc += arg
        i += 1
    elif cmd == 'jmp':
        i += arg
    else:
        i += 1

print(acc)

# p2

def execution(i=0, acc=0, visited=set(), edit=True):
    if i >= len(commands):
        print(acc)
        return
    if i in visited:
        return

    cmd, arg = commands[i]

    if cmd == 'acc':
        return execution(i+1, acc+arg, visited, edit=edit)

    if cmd == 'nop':
        execution(i+1, acc, visited, edit=edit)
    elif edit:
        execution(i+1, acc, visited, edit=False)

    visited = set(visited)
    visited.add(i)
    if cmd == 'jmp':
        execution(i+arg, acc, visited, edit=edit)
    elif edit:
        execution(i+arg, acc, visited, edit=False)

execution()
