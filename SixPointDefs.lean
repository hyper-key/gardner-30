import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fin.VecNotation

namespace SixPoint

/-- A position-indexed sequence of exactly six bounded vertices. -/
abbrev Path := Fin 6 → Fin 6

/-- Circular distance, including the wrap from 5 to 0. -/
def distance (x y : Fin 6) : Nat :=
  min (Nat.dist x.val y.val) (6 - Nat.dist x.val y.val)

/-- A six-vertex permutation: distinctness plus the bounded Path type. -/
def valid (p : Path) : Prop := Function.Injective p

instance (p : Path) : Decidable (valid p) :=
  inferInstanceAs (Decidable (∀ a b : Fin 6, p a = p b → a = b))

/-- Exactly five consecutive pairs; the closing edge is excluded. -/
def lengths (p : Path) : List Nat :=
  (List.finRange 5).map (fun i => distance (p i.castSucc) (p i.succ))

def witness : Path := ![0, 3, 1, 2, 4, 5]
def repeated : Path := ![0, 3, 1, 2, 0, 1]
def target : List Nat := [3, 2, 1, 2, 1]

end SixPoint
