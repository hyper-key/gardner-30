import GardnerDefs
namespace Gardner

-- A 15×15 array with two queens in every row and column has a fixed
-- combined sum of squares of its difference and centered sum indices.
private def centeredSq (i : Nat) : Int := (2*(i : Int)-14)^2
private def diagSq (p : Square) : Int :=
  ((p.1 : Int)-(p.2 : Int))^2 + ((p.1 : Int)+(p.2 : Int)-14)^2

private theorem sum_perm {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]
  | swap => simp only [List.sum_cons]; omega
  | trans _ _ h₁ h₂ => exact h₁.trans h₂

private theorem separate (q : List Square) :
    2 * (q.map diagSq).sum =
    (q.map (centeredSq ∘ Prod.fst)).sum + (q.map (centeredSq ∘ Prod.snd)).sum := by
  induction q with
  | nil => decide
  | cons p q ih =>
    simp only [List.map_cons, List.sum_cons, Function.comp_apply]
    have h : 2 * diagSq p = centeredSq p.1 + centeredSq p.2 := by
      unfold diagSq centeredSq; grind
    grind

theorem compressed_moment30 (q : List Square)
    (hr : (q.map Prod.fst).Perm (List.range 15 ++ List.range 15))
    (hc : (q.map Prod.snd).Perm (List.range 15 ++ List.range 15)) :
    (q.map fun p => ((p.1 : Int)-(p.2 : Int))^2 +
          ((p.1 : Int)+(p.2 : Int)-14)^2).sum = 2240 := by
  have fr := sum_perm (hr.map centeredSq)
  have fc := sum_perm (hc.map centeredSq)
  simp only [List.map_map] at fr fc
  have k : ((List.range 15 ++ List.range 15).map centeredSq).sum = 2240 := by decide
  have h := separate q
  rw [fr, fc, k] at h
  change (q.map diagSq).sum = 2240
  omega

#print axioms compressed_moment30
end Gardner
