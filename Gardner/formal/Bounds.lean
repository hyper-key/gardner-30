import Gardner.formal.Perimeter
namespace Gardner

def Feasible30 (k : Nat) : Prop := ∃ q : List Square, q.length = k ∧ Good 30 q

private theorem some_feasible30 : ∃ k, Feasible30 k := ⟨31,upper31⟩

noncomputable def minimum30 : Nat := by
  classical
  exact Nat.find some_feasible30

theorem minimum30_attained : Feasible30 minimum30 := by
  classical
  exact Nat.find_spec some_feasible30

theorem minimum30_le_of_feasible {k : Nat} (h : Feasible30 k) : minimum30 ≤ k := by
  classical
  exact Nat.find_min' some_feasible30 h

theorem minimum30_cases : minimum30 = 30 ∨ minimum30 = 31 := by
  obtain ⟨q,hq,hg⟩ := minimum30_attained
  have hl := Perimeter.lower30 q hg
  have hu := minimum30_le_of_feasible (show Feasible30 31 from upper31)
  omega

theorem minimum30_iff : minimum30 = 30 ↔ Feasible30 30 := by
  constructor
  · intro h; exact h ▸ minimum30_attained
  · intro h
    have a := minimum30_le_of_feasible h
    have b := minimum30_cases
    omega

#print axioms minimum30_cases
#print axioms minimum30_iff
end Gardner
