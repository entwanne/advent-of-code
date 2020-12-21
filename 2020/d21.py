import itertools
import re
import sys


meals = []

for line in sys.stdin:
    m = re.match(r'^([^(]+) \(contains ([^)]+)\)$', line)
    food, allergens = m.groups()
    food = set(food.split())
    allergens = set(allergens.split(', '))
    meals.append((food, allergens))

all_allergens = set.union(*(a for _, a in meals))
all_food = set.union(*(f for f, _ in meals))

# p1

known_algns = {algn: set(all_food) for algn in all_allergens}

for food, algns in meals:
    for algn in algns:
        known_algns[algn] &= food

all_known_food = set.union(*known_algns.values())

print(sum(
    1 for food, _ in meals
    for ing in food
    if ing not in all_known_food
))

# p2

real_algns = {}

while known_algns:
    algn, food = min(known_algns.items(), key=lambda x: len(x[1]))
    del known_algns[algn]
    ing, = food
    real_algns[algn] = ing
    for food in known_algns.values():
        food.discard(ing)

print(','.join(ing for _, ing in sorted(real_algns.items())))
