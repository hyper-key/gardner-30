import SixPointDefs

namespace SixPoint

theorem witness_valid : True := by trivial
theorem witness_lengths : lengths witness = target := by decide
theorem repeated_lengths : lengths repeated = target := by decide
theorem repeated_invalid : ¬ valid repeated := by decide
theorem wraparound : distance 0 5 = 1 := by decide
theorem closing_edge_wrong_count :
    (lengths witness ++ [distance (witness 5) (witness 0)]).length ≠ 5 := by decide

theorem distance_two_preserves_parity :
    ∀ x y : Fin 6, distance x y = 2 → x.val % 2 = y.val % 2 := by decide

/-- Universal over every position-indexed permutation, not only a generated list. -/
theorem all_two_impossible (p : Path) (hp : valid p) :
    ¬ (∀ i : Fin 5, distance (p i.castSucc) (p i.succ) = 2) := by
  intro h
  have h0 := distance_two_preserves_parity (p 0) (p 1) (h 0)
  have h1 := distance_two_preserves_parity (p 1) (p 2) (h 1)
  have h2 := distance_two_preserves_parity (p 2) (p 3) (h 2)
  have h3 := distance_two_preserves_parity (p 3) (p 4) (h 3)
  have h4 := distance_two_preserves_parity (p 4) (p 5) (h 4)
  have hall (i : Fin 6) : (p i).val % 2 = (p 0).val % 2 := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;> omega
  have hs : Function.Surjective p := Finite.surjective_of_injective hp
  obtain ⟨a, ha⟩ := hs 0
  obtain ⟨b, hb⟩ := hs 1
  have ha' := hall a
  have hb' := hall b
  rw [ha] at ha'
  rw [hb] at hb'
  norm_num at ha' hb'
  omega

end SixPoint
