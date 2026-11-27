import SixPointDefs

namespace SixPoint

theorem witness_valid : valid witness := by sorry
theorem witness_lengths : lengths witness = target := by sorry
theorem repeated_lengths : lengths repeated = target := by sorry
theorem repeated_invalid : ¬ valid repeated := by sorry
theorem wraparound : distance 0 5 = 1 := by sorry
theorem closing_edge_wrong_count :
    (lengths witness ++ [distance (witness 5) (witness 0)]).length ≠ 5 := by sorry
theorem distance_two_preserves_parity :
    ∀ x y : Fin 6, distance x y = 2 → x.val % 2 = y.val % 2 := by sorry
theorem all_two_impossible (p : Path) (hp : valid p) :
    ¬ (∀ i : Fin 5, distance (p i.castSucc) (p i.succ) = 2) := by sorry

end SixPoint
