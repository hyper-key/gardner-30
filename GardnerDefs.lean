import Std

namespace Gardner

abbrev Square := Nat × Nat
inductive Dir where | row | col | sum | diff deriving DecidableEq

def key (n : Nat) (d : Dir) (p : Square) : Nat :=
  match d with
  | .row  => p.1
  | .col  => p.2
  | .sum  => p.1 + p.2
  | .diff => p.1 + (n - 1 - p.2)

def onBoard (n : Nat) (p : Square) : Prop := p.1 < n ∧ p.2 < n

instance (n : Nat) (p : Square) : Decidable (onBoard n p) := by
  unfold onBoard; infer_instance

instance (P : Dir → Prop) [DecidablePred P] : Decidable (∀ d, P d) :=
  decidable_of_iff (P .row ∧ P .col ∧ P .sum ∧ P .diff) ⟨
    fun ⟨h₁,h₂,h₃,h₄⟩ d => by cases d <;> assumption,
    fun h => ⟨h _,h _,h _,h _⟩⟩

def occupancy (n : Nat) (q : List Square) (d : Dir) (k : Nat) :=
  (q.map (key n d)).count k

-- Every nonempty line occurs among the lines through the entries of q.
def Valid (n : Nat) (q : List Square) : Prop :=
  q.Nodup ∧ (∀ p ∈ q, onBoard n p) ∧
  ∀ p ∈ q, ∀ d, occupancy n q d (key n d p) ≤ 2

instance (n : Nat) (q : List Square) : Decidable (Valid n q) := by
  unfold Valid; infer_instance

-- Maximality is the literal single-square addition test.
def Good (n : Nat) (q : List Square) : Prop :=
  Valid n q ∧ ∀ p, onBoard n p → p ∉ q → ¬ Valid n (p :: q)

def SaturatedAt (n : Nat) (q : List Square) (p : Square) : Prop :=
  ∃ d, occupancy n q d (key n d p) = 2

end Gardner
