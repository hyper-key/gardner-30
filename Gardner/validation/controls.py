from check import audit


def board(n, points):
    return {"n": n, "queens": points}


for name, n, points, why in [
    ("row", 4, [[0,0],[0,2],[0,3]], "triple"),
    ("column", 4, [[0,3],[2,3],[3,3]], "triple"),
    ("down diagonal", 4, [[0,0],[2,2],[3,3]], "triple"),
    ("up diagonal", 4, [[3,0],[1,2],[0,3]], "triple"),
    ("duplicate", 4, [[1,2],[1,2]], "duplicate"),
    ("negative", 4, [[-1,1]], "out-of-board"),
    ("upper edge", 4, [[4,1]], "out-of-board"),
    ("Boolean coordinate", 4, [[True,1]], "integer")]:
    try:
        audit(board(n, points))
    except ValueError as err:
        assert why in str(err)
        print(name, str(err))
    else:
        raise AssertionError(name)

# The center queen dominates every square in the usual chess sense.
single = audit(board(3, [[1,1]]))
assert len(single["addable"]) == 8
print("ordinary domination accepts the lone center; all eight empty squares allow insertion")
# Every row and column has a pair, yet a long diagonal has a triple.
try:
    audit(board(4, [[0,0],[0,1],[1,1],[1,2],[2,2],[2,3],[3,3],[3,0]]))
except ValueError as err:
    assert "triple" in str(err)
else:
    raise AssertionError("ignored diagonal capacity")

# Figure 4 of Cooper et al. has an isolated queen at its upper right.
isolated = [[0,3],[1,0],[1,1],[2,0],[2,2],[3,1],[3,2]]
assert audit(board(4, isolated))["maximal"]
assert audit(board(1, [[0,0]]))["maximal"]
# This three-point line has slope 2. It is legal under the four directions.
assert not audit(board(5, [[0,0],[1,2],[2,4]]))["maximal"]
print("occupied-square exception, singleton board and arbitrary-slope controls pass")
