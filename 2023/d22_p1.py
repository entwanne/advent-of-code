import sys
import itertools
from dataclasses import dataclass


@dataclass
class Cube:
    x: int
    y: int
    z: int


@dataclass
class Brick:
    id: int
    min: Cube
    max: Cube

    @property
    def xmin(self):
        return self.min.x

    @property
    def xmax(self):
        return self.max.x

    @property
    def ymin(self):
        return self.min.y

    @property
    def ymax(self):
        return self.max.y

    @property
    def zmin(self):
        return self.min.z

    @property
    def zmax(self):
        return self.max.z

    def square_coords(self):
        return itertools.product(
            range(self.xmin, self.xmax+1),
            range(self.ymin, self.ymax+1),
        )

    def cube_coords(self):
        return itertools.product(
            range(self.xmin, self.xmax+1),
            range(self.ymin, self.ymax+1),
            range(self.zmin, self.zmax+1),
        )

    def lower(self):
        self.min.z -= 1
        self.max.z -= 1


def parse_cube(s):
    x, y, z = map(int, s.split(','))
    return Cube(x, y, z)


def parse_brick(s, _id_seq=itertools.count(1)):
    c1, c2 = list(map(parse_cube, s.split('~')))
    x1, x2 = sorted((c1.x, c2.x))
    y1, y2 = sorted((c1.y, c2.y))
    z1, z2 = sorted((c1.z, c2.z))
    return Brick(next(_id_seq), min=Cube(x1, y1, z1), max=Cube(x2, y2, z2))


def parse_bricks(f):
    bricks = [parse_brick(line.strip()) for line in f]
    bricks.sort(key=lambda b: b.zmin)
    return bricks


def fall_brick(brick, world, supported_by):
    while brick.zmin > 1:
        z = brick.zmin - 1
        underbricks = {
            bid
            for x, y in brick.square_coords()
            if (bid := world.get((x, y, z)))
        }
        if underbricks:
            for bid in underbricks:
                supported_by[brick.id].add(bid)
            break

        brick.lower()

    for p in brick.cube_coords():
        world[p] = brick.id


def fall_bricks(bricks):
    world = {}
    supported_by = {}

    for brick in bricks:
        supported_by[brick.id] = set()
        fall_brick(brick, world, supported_by)

    return supported_by


def removable_bricks(supported_by):
    bricks = supported_by.keys()
    needed = set.union(*(
        sb
        for sb in supported_by.values()
        if len(sb) == 1
    ))
    return bricks - needed


if __name__ == '__main__':
    bricks = parse_bricks(sys.stdin)
    supported_by = fall_bricks(bricks)
    print(len(removable_bricks(supported_by)))
