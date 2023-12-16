import copy
from dataclasses import dataclass

@dataclass
class Cell:
    name: str

    @property
    def energy(self):
        return {
            'A': 1,
            'B': 10,
            'C': 100,
            'D': 1000,
        }[self.name]


room_doors = {
    'A': 2,
    'B': 4,
    'C': 6,
    'D': 8,
}
game = {
    'hallway': [None] * 11,
    'rooms': {
        'A': [
            Cell(name='B'),
            Cell(name='A'),
        ],
        'B': [
            Cell(name='C'),
            Cell(name='D'),
        ],
        'C': [
            Cell(name='B'),
            Cell(name='C'),
        ],
        'D': [
            Cell(name='D'),
            Cell(name='A'),
        ],
    },
}


def print_game(game):
    print(''.join(
        '.' if c is None else c.name
        for c in game['hallway']
    ))
    def room_char(c, i):
        room = game['rooms'][c]
        if i >= len(room):
            return ' '
        if not room[i]:
            return '.'
        return room[i].name
    def print_rooms(i):
        print(f'  {room_char("A", i)} {room_char("B", i)} {room_char("C", i)} {room_char("D", i)}  ')
    print_rooms(0)
    print_rooms(1)


def clean_rooms(game):
    for name, room in game['rooms'].items():
        while room and room[-1] and room[-1].name == name:
            room.pop()


def list_available_hallway(game, i, energy):
    hallway = game['hallway']
    yield i, 0

    nexts = []
    if 0 < i < len(hallway):
        nexts.append((i-1, -1, energy))
    if 0 <= i < len(hallway) -1:
        nexts.append((i+1, 1, energy))

    while nexts:
        i, d, cost = nexts.pop(0)
        if hallway[i] is not None:
            continue
        yield i, cost
        cost += energy
        if 0 <= i+d < len(hallway):
            nexts.append((i+d, d, cost))


def list_available(game, place, i):
    name = place[i].name
    energy = place[i].energy

    if place is game['hallway']:
        door_cost = next((cost for j, cost in list_available_hallway(game, i, energy) if j == room_doors[name]), None)
        if door_cost is None:
            return
        room = game['rooms'][name]
        if all(c is None for c in room):
            yield (name, len(room) - 1, door_cost + len(room) * energy)
        return

    if any(place[j] is not None for j in range(i)):
        return
    door_name = next(dn for dn, r in game['rooms'].items() if r is place)
    door = room_doors[door_name]
    door_cost = (i+1) * energy

    target_door = room_doors[name]
    target_room = game['rooms'][name]
    availables = set(list_available_hallway(game, door, energy))
    if any(j == target_door for j, _ in availables) and all(c is None for c in target_room):
        move_cost = next(c for j, c in availables if j == target_door)
        yield (name, len(target_room)-1, door_cost + move_cost + len(target_room)*energy)
        return

    for j, cost in availables:
        if j not in room_doors.values():
            yield 'hallway', j, cost + door_cost


def next_moves(game):
    hallway = game['hallway']
    for i, c in enumerate(hallway):
        if c is not None:
            for place, j, cost in list_available(game, hallway, i):
                yield ('hallway', i), (place, j), cost

    for name, room in game['rooms'].items():
        for i, c in enumerate(room):
            if c is not None:
                for place, j, cost in list_available(game, room, i):
                    yield (name, i), (place, j), cost


def game_key(game):
    return frozenset({
        ('h', i, cell.name)
        for i, cell in enumerate(game['hallway'])
        if cell is not None
    } | {
        (name, i, cell.name)
        for name, room in game['rooms'].items()
        for i, cell in enumerate(room)
        if cell is not None
    })


def find(game):
    nexts = {0: [game]}
    seen = set()

    while nexts:
        cost = min(nexts)
        queue = nexts[cost]

        game = queue.pop()
        if not queue:
            del nexts[cost]

        clean_rooms(game)
        key = game_key(game)
        if key in seen:
            continue
        seen.add(key)

        if all(r == [] for r in game['rooms'].values()):
            return cost

        moves = set(next_moves(game))
        if not moves:
            continue

        for move in moves:
            g = copy.deepcopy(game)
            (place1, i), (place2, j), c = move
            place1 = g['hallway'] if place1 == 'hallway' else g['rooms'][place1]
            place2 = g['hallway'] if place2 == 'hallway' else g['rooms'][place2]
            place2[j] = place1[i]
            place1[i] = None
            nexts.setdefault(cost + c, []).append(g)


print(find(game))
