import heapq
import sys


def parse_lights(f):
    for line in f:
        lights, *buttons, joltage = line.split()
        lights = tuple(c == '#' for c in lights.strip('[]'))
        buttons = tuple(tuple(map(int, b.strip('()').split(','))) for b in buttons)
        joltage = tuple(map(int, joltage.strip('{}').split(',')))
        yield lights, buttons, joltage


def apply_button(lights, button):
    lights = list(lights)
    for idx in button:
        lights[idx] = not lights[idx]
    return tuple(lights)


def min_buttons(expected_lights, buttons):
    start_lights = (False,) * len(expected_lights)
    queue = [(0, start_lights, [])]
    seen = {start_lights: 0}

    while queue:
        n, lights, path = heapq.heappop(queue)
        if lights == expected_lights:
            return n

        for b in buttons:
            blights = apply_button(lights, b)
            if n + 1 < seen.get(blights, float('inf')):
                seen[blights] = n + 1
                heapq.heappush(queue, (n + 1, blights, (*path, b)))


if __name__ == '__main__':
    print(sum(min_buttons(expected, buttons) for expected, buttons, _ in parse_lights(sys.stdin)))
