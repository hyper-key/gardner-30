"""Independent known-answer benchmark for the six-vertex circle."""
from collections import Counter
from itertools import permutations


def distances(path):
    pairs = zip(path, path[1:])
    return [min(abs(x - y), 6 - abs(x - y)) for x, y in pairs]


def valid(path, counts):
    return sorted(path) == list(range(6)) and Counter(distances(path)) == counts


def main():
    path = [0, 3, 1, 2, 4, 5]
    duplicate = [0, 3, 1, 2, 0, 1]
    counts = Counter({1: 2, 2: 2, 3: 1})
    if distances(path) != [3, 2, 1, 2, 1] or not valid(path, counts):
        raise ValueError("The known path should pass.")
    if distances(duplicate) != distances(path) or valid(duplicate, counts):
        raise ValueError("The repeated-vertex path should fail despite matching distances.")
    if distances([0, 5]) != [1] or Counter(distances(path + path[:1])) == counts:
        raise ValueError("Check wraparound and the difference between paths and cycles.")

    realized = set()
    for p in permutations(range(6)):
        histogram = Counter(distances(p))
        realized.add(tuple(histogram[k] for k in (1, 2, 3)))
    profiles = {(a, b, 5 - a - b) for a in range(6) for b in range(6 - a)}
    if not realized <= profiles or len(realized) != 17 or (0, 5, 0) in realized:
        raise ValueError("Unexpected result from exhaustive enumeration.")
    print("720 permutations checked; 17 of 21 count profiles realized.")
    print("Witness, repeated vertex, wraparound, closing edge, and parity controls passed.")


if __name__ == "__main__":
    main()
