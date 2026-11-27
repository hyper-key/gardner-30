import Std

namespace Gardner.Marginal

def differences (q : List (Int × Int)) : List Int :=
  q.map fun p => p.1 - p.2

def sums (q : List (Int × Int)) : List Int :=
  q.map fun p => p.1 + p.2

def squareSum (keys : List Int) : Int :=
  (keys.map (fun k => k^2)).sum

private theorem sum_perm {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ ih jh => exact ih.trans jh

private theorem expand_moments (q : List (Int × Int)) :
    (differences q).sum = (q.map Prod.fst).sum - (q.map Prod.snd).sum ∧
    (sums q).sum = (q.map Prod.fst).sum + (q.map Prod.snd).sum ∧
    squareSum (differences q) + squareSum (sums q) =
      2 * (squareSum (q.map Prod.fst) + squareSum (q.map Prod.snd)) := by
  induction q with
  | nil => decide
  | cons p q ih =>
    rcases ih with ⟨hd, hs, h2⟩
    have hp : (p.1 - p.2)^2 + (p.1 + p.2)^2 = 2 * (p.1^2 + p.2^2) := by
      grind
    simp only [differences, sums, squareSum, List.map_cons, List.sum_cons] at *
    exact ⟨by omega, by omega, by omega⟩

/-- These are the three identities used when filling a diagonal cover.
The active lists are arbitrary integer coordinates. Their ordering is irrelevant. -/
theorem paired_moments (q : List (Int × Int)) (rows cols : List Int)
    (hr : (q.map Prod.fst).Perm (rows ++ rows))
    (hc : (q.map Prod.snd).Perm (cols ++ cols)) :
    (differences q).sum = 2 * (rows.sum - cols.sum) ∧
    (sums q).sum = 2 * (rows.sum + cols.sum) ∧
    squareSum (differences q) + squareSum (sums q) =
      4 * (squareSum rows + squareSum cols) := by
  obtain ⟨hd, hs, h2⟩ := expand_moments q
  have r := sum_perm hr
  have c := sum_perm hc
  have rr := sum_perm (hr.map (fun x : Int => x^2))
  have cc := sum_perm (hc.map (fun x : Int => x^2))
  simp only [List.sum_append, List.map_append] at r c rr cc
  unfold squareSum at h2 ⊢
  exact ⟨by omega, by omega, by omega⟩

/-- Soundness of a terminal incompatibility test. The two predicates can be
supersets of the realizable marginal second moments. Their construction and
coverage of a particular search branch are separate obligations. -/
theorem incompatible_moment_sets (rows cols : List Int)
    (possibleD possibleS : Int → Prop)
    (gap : ∀ d s, possibleD d → possibleS s →
      d + s ≠ 4 * (squareSum rows + squareSum cols)) :
    ¬ ∃ q : List (Int × Int),
      (q.map Prod.fst).Perm (rows ++ rows) ∧
      (q.map Prod.snd).Perm (cols ++ cols) ∧
      possibleD (squareSum (differences q)) ∧ possibleS (squareSum (sums q)) := by
  rintro ⟨q, hr, hc, hd, hs⟩
  exact gap _ _ hd hs (paired_moments q rows cols hr hc).2.2

#print axioms paired_moments
#print axioms incompatible_moment_sets

end Gardner.Marginal
