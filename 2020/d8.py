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
        return True
    if i in visited:
        return False

    cmd, arg = commands[i]
    visited.add(i)

    if cmd == 'acc':
        return execution(i+1, acc+arg, visited, edit=edit)

    if cmd == 'nop':
        ret = execution(i+1, acc, visited, edit=edit)
        if ret:
            return True
        elif edit:
            return execution(i+arg, acc, visited, edit=False)
        return False

    if cmd == 'jmp':
        ret = execution(i+arg, acc, visited, edit=edit)
        if ret:
            return True
        elif edit:
            return execution(i+1, acc, visited, edit=False)
        return False

execution()
