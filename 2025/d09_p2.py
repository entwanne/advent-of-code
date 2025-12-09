import itertools
import sys

from d09_p1 import parse_map, area


def fill_line(cells, p1, p2):
    x1, y1 = p1
    x2, y2 = p2

    if x1 == x2:
        for y in range(min(y1, y2) + 1, max(y1, y2)):
            cells.add((x1, y))
    elif y1 == y1:
        for x in range(min(x1, x2) + 1, max(x1, x2)):
            cells.add((x, y1))
    else:
        assert False


def parse_grid(f):
    corners = set()
    cells = set()
    last = first = None

    for p in parse_map(f):
        p = tuple(p)

        if first is None:
            first = p

        if last is not None:
            fill_line(cells, p, last)

        corners.add(p)
        cells.add(p)
        last = p

    fill_line(cells, first, last)

    return corners, cells
    #return corners


def valid_area(cells, p1, p2):
    x1, y1 = p1
    x2, y2 = p2
    x1, x2 = sorted((x1, x2))
    y1, y2 = sorted((y1, y2))
    return not any((x, y) in cells for x in range(x1+1, x2) for y in range(y1+1, y2))


#def find_largest_area(corners, cells):
#    return max(area(p1, p2) for p1, p2 in itertools.combinations(corners, 2) if valid_area(cells, p1, p2))


def largest_area(corners, cells, xmax, ymax):
    # Itérer sur les rectangles s'élargissant vers la droite et le bas à partir de p
    # s'arrêter (pour une direction) dès qu'on rencontre un autre coin
    #x1, y1 = p
    queue = [(x, y, x, y, True, True) for x, y in corners]
    max_area = 0
    print(len(queue))

    #print(p)
    areas = {}

    while queue:
        x1, y1, x2, y2, expand_x, expand_y = queue.pop(0)
        #print(x1, y1, max_area)
        #print(p, width, height)

        #print((x1, y1), (x2, y2), (expand_x, expand_y))

        """
        if (x1+width, y1+height) in grid:
            max_area = max(max_area, (width+1)*(height+1))

        expand_x = expand_x and not any((x1+width, y2) in grid for y2 in range(y1+1, y1+height-1))
        expand_y = expand_y and not any((x2, y1+height) in grid for x2 in range(x1+1, x1+width-1))
        """

        area = (x2 - x1 + 1) * (y2 - y1 + 1)
        if area < areas.get((x2, y2), 0):
            continue
        areas[x2, y2] = area

        if (x2, y2) in corners:
            max_area = max(max_area, area)
            print('->', max_area)

        if x2 >= xmax:
            expand_x = False
        if y2 >= ymax:
            expand_y = False

        #print((expand_x, expand_y))

        #print('y', list(range(y1+1, y2+1)))
        #print('x', list(range(x1+1, x2+1)))

        if expand_x:
            #expand_x = all((x2, y) not in grid for y in range(y1 + 1, y2))
            #expand_x = all((x2, y) not in grid for y in range(y1 + 1, y2 + 1))
            expand_x = all((x2, y) not in cells for y in range(y1+1, y2))

        if expand_y:
            #expand_y = all((x, y2) not in grid for x in range(x1 + 1, x2))
            expand_y = all((x, y2) not in cells for x in range(x1+1, x2))

        #print((expand_x, expand_y))

        #if expand_x and expand_y and (x1+width, y1+height) not in grid:
        #if expand_x and expand_y and ((x2, y2) == (x1, y1) or (x2, y2) not in grid):
        if expand_x and expand_y and (x2 == x1 or y2 == y1 or (x2, y2) not in cells):
            queue.append((x1, y1, x2 + 1, y2 + 1, True, True))
        elif expand_x:
            queue.append((x1, y1, x2 + 1, y2, True, False))
        elif expand_y:
            queue.append((x1, y1, x2, y2 + 1, False, True))

    #print(p, max_area)
    return max_area


def find_largest_area(corners, cells):
    xmax = max(x for x, _ in corners)
    ymax = max(y for _, y in corners)
    #return largest_area(corners, cells, xmax, ymax, (2, 3))
    #return max(largest_area(corners, cells, xmax, ymax, p) for p in corners)
    return largest_area(corners, cells, xmax, ymax)


if __name__ == '__main__':
    print(find_largest_area(*parse_grid(sys.stdin)))
