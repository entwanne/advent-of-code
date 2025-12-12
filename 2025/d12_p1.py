import sys


def parse_shape(block):
    key, *lines = block.splitlines()
    return (len(lines[0]), len(lines))


def parse_region(line):
    dims, shape_counts = line.split(': ')
    width, height = map(int, dims.split('x'))
    return (width, height), sum(map(int, shape_counts.split()))


def parse_file(f):
    *shapes, regions = f.read().split('\n\n')
    shape, = {parse_shape(block) for block in shapes}
    regions = [parse_region(line) for line in regions.splitlines()]
    return shape, regions


def can_fit(region_shape, shape_count, shape):
    rwidth, rheight = region_shape
    swidth, sheight = shape
    width = rwidth // swidth
    height = rheight // sheight
    return (width * height) >= shape_count


if __name__ == '__main__':
    shape, regions = parse_file(sys.stdin)
    print(sum(can_fit(*region, shape) for region in regions))
