import Gardner.formal.GridFunctional

namespace Gardner.Grid30

-- Direct evaluation of the actual homogeneous term on all 900 weighted points.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem fully_paired_top : functional (topForm 15 15 15 15) = 0 := by decide

private theorem weighted_congr_on (s : List (Int × Int)) (f g : Int → Int)
    (h : ∀ p ∈ s, f p.1 = g p.1) : weighted s f = weighted s g := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    simp only [weighted, h p (by simp), ih (fun t ht => h t (by simp [ht]))]

private theorem weighted_neg (s : List (Int × Int)) (f : Int → Int) :
    weighted s (fun x => -f x) = -weighted s f := by
  induction s with
  | nil => rfl
  | cons p s ih => simp only [weighted,ih]; grind

-- Only the sum of the top form and remainder vanishes pointwise.
theorem fully_paired_remainder (ts : List Term) (degree : ∀ t ∈ ts, t.a+t.b ≤ 59)
    (vanishes : ∀ i j : Fin 30, evalTerms ts (coord i) (coord j) +
      topForm 15 15 15 15 (coord i) (coord j) = 0) : coefficient ts = 0 := by
  let T := topForm 15 15 15 15
  have h : functional (evalTerms ts) = functional (fun x y => -T x y) := by
    apply weighted_congr_on
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    apply weighted_congr_on
    intro p hp
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    have eq : evalTerms ts (coord i) (coord j) + T (coord i) (coord j) = 0 :=
      vanishes ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩
    change evalTerms ts (coord i) (coord j) = -T (coord i) (coord j)
    omega
  have neg : functional (fun x y => -T x y) = -functional T := by
    unfold functional
    simp only [weighted_neg]
  rw [extracts_coefficient ts degree, neg, show functional T = 0 from fully_paired_top] at h
  exact (Int.mul_eq_zero.mp (by simpa using h)).resolve_left (by decide : scale^2 ≠ 0)

-- Choosing two distinct positions of a single family contributes their product.
def pairSum : List Int → Int
  | [] => 0
  | x :: xs => x*xs.sum + pairSum xs

theorem pair_sum_formula (xs : List Int) :
    2*pairSum xs = xs.sum^2 - (xs.map (fun x => x^2)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [pairSum,List.map_cons,List.sum_cons]; grind

-- The nonzero two-omission entries of the verified 58-degree table.
theorem full_omissions (A B D S A₂ B₂ eX eY : Int) (hD : D=A-B) (hS : S=A+B)
    (hX : 2*eX=A^2-A₂) (hY : 2*eY=B^2-B₂)
    (hTerms : -6435*eX + 6435*eY - 3432*A*D - 3432*A*S
      - 3432*B*D + 3432*B*S - 3432*D*S = 0) :
    21*A^2 - 5*A₂ = 21*B^2 - 5*B₂ := by
  grind

#print axioms fully_paired_top
#print axioms fully_paired_remainder
#print axioms pair_sum_formula
#print axioms full_omissions
end Gardner.Grid30
