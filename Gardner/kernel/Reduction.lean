import Gardner.kernel.Reflection
import Gardner.kernel.AxisMoments
import Gardner.kernel.Frames

namespace Gardner.Kernel
open Bridge

def EqualSpans (rows cols : Finset Nat) : Prop :=
  ∃ lr hr lc hc, lr ∈ rows ∧ hr ∈ rows ∧ lc ∈ cols ∧ hc ∈ cols ∧
    (∀ r ∈ rows, lr ≤ r ∧ r ≤ hr) ∧
    (∀ c ∈ cols, lc ≤ c ∧ c ≤ hc) ∧ hr-lr = hc-lc

/-- Necessary conditions derived from literal maximality. A global exclusion
of this type is still required for an unconditional lower bound of 31. -/
structure NecessaryProfile where
  queens : List Square
  good : Good 30 queens
  length : queens.length = 30
  rows_paired : (fullKeys queens .row).card = 15
  cols_paired : (fullKeys queens .col).card = 15
  diff_paired : (fullKeys queens .diff).card = 15
  sum_cases : (fullKeys queens .sum).card = 13 ∨
    (fullKeys queens .sum).card = 14 ∨ (fullKeys queens .sum).card = 15
  balanced : (fullKeys queens .sum).card < 15 →
    (coverRoots queens .row 15).sum = (coverRoots queens .col 15).sum
  equal_spans : (fullKeys queens .sum).card < 15 →
    EqualSpans (Finset.range 30 \ fullKeys queens .row)
      (Finset.range 30 \ fullKeys queens .col)
  moments : (fullKeys queens .sum).card = 15 →
    21*(coverRoots queens .row 15).sum^2 -
      5*((coverRoots queens .row 15).map (fun x => x^2)).sum =
    21*(coverRoots queens .col 15).sum^2 -
      5*((coverRoots queens .col 15).map (fun y => y^2)).sum

theorem reduce30 (q : List Square) (hg : Good 30 q) (len : q.length = 30) :
    Nonempty NecessaryProfile := by
  obtain ⟨t,good,length,diff⟩ := orient_complete_difference hg len
  let P := coverOfGood good length
  have counts := diagonal_count_cases P
  have sum_cases : (fullKeys t .sum).card = 13 ∨
      (fullKeys t .sum).card = 14 ∨ (fullKeys t .sum).card = 15 := by
    change ((fullKeys t .diff).card = 15 ∧ (fullKeys t .sum).card = 13) ∨
      ((fullKeys t .diff).card = 15 ∧ (fullKeys t .sum).card = 14) ∨
      ((fullKeys t .diff).card = 15 ∧ (fullKeys t .sum).card = 15) ∨
      ((fullKeys t .diff).card = 14 ∧ (fullKeys t .sum).card = 15) ∨
      ((fullKeys t .diff).card = 13 ∧ (fullKeys t .sum).card = 15) at counts
    omega
  refine ⟨⟨t,good,length,paired_rows30 good length,paired_columns30 good length,
    diff,sum_cases,?_,?_,?_⟩⟩
  · intro deficient
    exact deficient_sum_axis_balance good length diff (by omega)
  · intro deficient
    have fewer : P.differences.card+P.sums.card < 30 := by
      change (fullKeys t .diff).card+(fullKeys t .sum).card < 30
      omega
    exact equal_spans_of_fewer_than_30 P fewer
  · intro complete
    exact fully_paired_axis_moment good length diff complete

/-- The exact remaining global obligation is explicit. This conditional
interface does not assert that all reduced profiles have been excluded. -/
theorem lower31_of_profile_exclusion (excluded : ¬ Nonempty NecessaryProfile)
    (q : List Square) (hg : Good 30 q) : 31 ≤ q.length := by
  have lower := Perimeter.lower30 q hg
  by_contra small
  have length : q.length = 30 := by omega
  exact excluded (reduce30 q hg length)

#print axioms reduce30
#print axioms lower31_of_profile_exclusion
end Gardner.Kernel
