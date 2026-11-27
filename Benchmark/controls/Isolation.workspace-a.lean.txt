import Mathlib.Data.Nat.Basic

example (n : Nat) : n + 0 = n := by
  exact False.elim (by assumption)
