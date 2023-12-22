import sys


def parse_elf(it):
    for line in it:
        if not line.strip():
            break

        yield int(line)


def parse(f):
    it = iter(f)
    while x := sum(parse_elf(it)):
        yield x


#print(max(parse(sys.stdin)))
print(sum(sorted(parse(sys.stdin))[-3:]))
