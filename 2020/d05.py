import sys


ROWS = 128
COLS = 8

def binary_search(a, b, code):
    for x in code:
        amp = b - a
        diff = (amp // 2) + 1
        if x:
            b -= diff
        else:
            a += diff
    assert a == b
    return a


def get_seat(code):
    row_code, col_code = code[:7], code[7:]
    row = binary_search(0, ROWS-1, (c == 'F' for c in row_code))
    col = binary_search(0, COLS-1, (c == 'L' for c in col_code))
    return row, col


def get_seat_id(code):
    #row, col = get_seat(code)
    #return row * COLS + col
    code = code.translate(str.maketrans('FBLR', '0101'))
    return int(code, 2)


def p1():
    print(max(get_seat_id(line.strip()) for line in sys.stdin))


def all_seats():
    for r in range(ROWS):
        for c in range(COLS):
            yield r * COLS + c


def p2():
    seats = set(all_seats())
    for line in sys.stdin:
        seat = get_seat_id(line.strip())
        seats.remove(seat)
    for s in seats:
        if (s-1) not in seats and (s+1) not in seats:
            print(s)
