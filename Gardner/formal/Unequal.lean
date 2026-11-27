import Std
namespace Gardner.UnequalSpan

-- If x right-hand endpoint lines are differences, 15−x are sums.
-- At the left endpoint those two multiplicities exchange.
theorem endpoint_balance (U V lo e x : Int)
    (allRows : V + U = 435)
    (endpoints : 2*V = 2*U + (15-2*x)*(lo+e) + (2*x-15)*lo) :
    870 - 4*U = (15-2*x)*e := by grind

theorem possible_long_span (U e x : Int) (size : 14 < e ∧ e ≤ 29)
    (balance : 870-4*U = (15-2*x)*e) : e=18 ∨ e=22 ∨ e=26 := by
  have spread : e=15 ∨ e=16 ∨ e=17 ∨ e=18 ∨ e=19 ∨ e=20 ∨ e=21 ∨ e=22 ∨
      e=23 ∨ e=24 ∨ e=25 ∨ e=26 ∨ e=27 ∨ e=28 ∨ e=29 := by omega
  rcases spread with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega

-- For an empty target at column lo+t, any diagonal which intersects an
-- endpoint target has to reach its row by one of these four literal shifts.
theorem endpoint_shift (r z c lo t e : Int) (hcol : c=lo ∨ c=lo+e)
    (diag : r-(lo+t)=z-c ∨ r+(lo+t)=z+c) :
    z=r+t ∨ z=r-t ∨ z=r+(e-t) ∨ z=r-(e-t) := by omega

#print axioms endpoint_balance
#print axioms possible_long_span
#print axioms endpoint_shift
end Gardner.UnequalSpan
