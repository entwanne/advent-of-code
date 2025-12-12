import sys
from functools import cache


@cache
def bounds(shape):
    xmin = min(x for x, _ in shape)
    xmax = max(x for x, _ in shape)
    ymin = min(y for _, y in shape)
    ymax = max(y for _, y in shape)
    return xmin, xmax, ymin, ymax


@cache
def xflip(shape):
    xmax = max(x for x, _ in shape)
    return frozenset((xmax - x, y) for x, y in shape)


@cache
def rotate(shape):
    ymax = max(y for _, y in shape)
    return frozenset((ymax - y, x) for (x, y) in shape)


@cache
def translate(shape, dx, dy):
    return frozenset((x + dx, y + dy) for (x, y) in shape)


def all_permutations(shape):
    shapes = set()

    for _ in range(4):
        shapes.add(shape)
        shapes.add(xflip(shape))
        shape = rotate(shape)

    return frozenset(shapes)


def parse_shape(block):
    key, *lines = block.splitlines()
    key = int(key.removesuffix(':'))
    shape = frozenset(
        (x, y)
        for y, line in enumerate(lines)
        for x, char in enumerate(line)
        if char == '#'
    )
    return key, all_permutations(shape)


def parse_region(line):
    dims, shape_counts = line.split(': ')
    width, height = map(int, dims.split('x'))
    shape = frozenset((x, y) for y in range(height) for x in range(width))
    return shape, {idx: count for idx, count in enumerate(map(int, shape_counts.split())) if count}


def parse_file(f):
    *shapes, regions = f.read().split('\n\n')

    shapes = dict(parse_shape(b) for b in shapes)
    regions = [parse_region(line) for line in regions.splitlines()]

    return shapes, regions


def all_positions(region_shape, shape):
    _, xmax, _, ymax = bounds(region_shape)
    return {
        tshape
        for y in range(ymax + 1)
        for x in range(xmax + 1)
        if (tshape := translate(shape, x, y)) & region_shape == tshape
    }


def can_fit(region, shapes):
    region_shape, shape_counts = region
    '''
    print(width, height)
    print(dump_shape(region_shape))
    #print(shapes[0])
    for p in all_positions(region_shape, next(iter(shapes[0]))):
        print()
        print(dump_shape(region_shape - p))
    return False
    '''
    '''
    #print('='*100)
    queue = [(region_shape, shape_counts)]
    while queue:
        #print(len(queue))
        region_shape, shape_counts = queue.pop(0)
        if sum(shape_counts.values()) == 0:
            return True
        shape_key = next(key for key, count in shape_counts.items() if count)
        for shape in shapes[shape_key]:
            for tshape in all_positions(region_shape, shape):
                tcounts = dict(shape_counts)
                tcounts[shape_key] -= 1
                queue.append((region_shape - tshape, tcounts))
        
    return False
    '''
    print(_can_fit(
        region_shape,
        tuple(shapes[key] for key in sorted(shapes)),
        frozenset(shape_counts.items()),
    ))
    return _can_fit(
        region_shape,
        tuple(shapes[key] for key in sorted(shapes)),
        frozenset(shape_counts.items()),
    )

@cache
def _can_fit(region_shape, shapes, shape_counts):
    shape_counts = dict(shape_counts)
    if not shape_counts:
        return True
    shape_key = next(key for key, count in shape_counts.items() if count)
    for shape in shapes[shape_key]:
        for tshape in all_positions(region_shape, shape):
            tcounts = dict(shape_counts)
            tcounts[shape_key] -= 1
            tcounts = frozenset((k, c) for k, c in tcounts.items() if c)
            #queue.append((region_shape - tshape, tcounts))
            if _can_fit(region_shape - tshape, shapes, tcounts):
                return True
    return False


def dump_shape(shape):
    xmin, xmax, ymin, ymax = bounds(shape)
    return '\n'.join(
        ' '.join('.#'[(x, y) in shape] for x in range(xmin, xmax + 1))
        for y in range(ymin, ymax + 1)
    )


if __name__ == '__main__':
    shapes, regions = parse_file(sys.stdin)
    '''
    for key, shapeset in shapes.items():
        for shape in shapeset:
            print()
            print(key)
            print(dump_shape(shape))
    print(regions)
    '''
    print(sum(can_fit(region, shapes) for region in regions))
