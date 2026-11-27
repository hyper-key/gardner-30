"""Two independent computations: symbolic coefficients and grid differences."""
from itertools import combinations_with_replacement, product
from math import comb, factorial, prod
from random import Random


def top(exponents, target=29):
    a,b,d,s = exponents
    k = target-a
    return sum((-1)**(d-i)*comb(d,i)*comb(s,k-i)
               for i in range(d+1) if 0 <= k-i <= s)


def finite_difference(roots):
    # All arguments are centered even-board coordinates 2i-29.
    def val(t, offsets):
        return prod(t-u for u in offsets)
    lookups = [{v:val(v, offsets) for v in range(-58,59)} for offsets in roots]
    weights = [(-1)**(29-i)*comb(29,i) for i in range(30)]
    value = 0
    for i,j in product(range(30), repeat=2):
        x,y = 2*i-29,2*j-29
        value += weights[i]*weights[j]*prod(table[t] for table,t in
                                            zip(lookups,(x,y,x-y,x+y)))
    return divmod(value, (2**29*factorial(29))**2)


def direct_coefficients():
    rng = Random(301976)
    for i,j in combinations_with_replacement(range(4),2):
        caps = [15]*4
        caps[i] -= 1
        caps[j] -= 1
        value = top(caps)
        roots = [[rng.randint(-40,40) for _ in range(c)] for c in caps]
        assert finite_difference(roots) == (value,0)
        print("pair",i,j,"exponents",caps,"coefficient",value)
    for i in range(4):
        caps = [15]*4
        caps[i] -= 1
        roots = [[rng.randint(-40,40) for _ in range(c)] for c in caps]
        coeff = 0
        for j in range(4):
            reduced = caps.copy()
            reduced[j] -= 1
            coeff -= sum(roots[j])*top(reduced)
        assert finite_difference(roots) == (coeff,0)
        print("degree-59 centered difference identity",i,"verified on fixture")

    for case in range(4):
        xs, ys = (rng.sample(range(-29,30,2),15) for _ in range(2))
        a,b = sum(xs),sum(ys)
        ds = rng.sample(range(-58,59,2),14)
        ss = rng.sample(range(-58,59,2),14)
        ds.append(a-b-sum(ds))
        ss.append(a+b-sum(ss))
        predicted = (6435*(sum(x*x for x in xs)-sum(y*y for y in ys))
                     -27027*(a*a-b*b))//2
        assert finite_difference([xs,ys,ds,ss]) == (predicted,0)
    print("all-four-paired degree-60 identity verified on four shifted products")


if __name__ == "__main__":
    direct_coefficients()
