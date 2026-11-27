import Gardner.formal.Perimeter
import Gardner.formal.AffineProducts

namespace Gardner.Bridge

/-- The equality case of the perimeter bound supplies a completely paired
family, so a size-30 maximal placement has no isolated queens. -/
theorem no_isolated30 {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    ∀ p ∈ q, SaturatedAt 30 q p := by
  obtain ⟨d, hd⟩ := Perimeter.complete_family30 q hg len
  have complete : (fullKeys q d).card = 15 := hd
  have pairs := complete_pairs len d complete
  intro p hp
  refine ⟨d, ?_⟩
  have member : key 30 d p ∈ (fullKeys q d).toList := by
    have h := pairs.mem_iff.mp (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simpa only [List.mem_append, or_self] using h
  exact (Finset.mem_filter.mp (Finset.mem_toList.mp member)).2

/-- The coarse saturation restrictions now follow from the literal board
predicate, without a separate no-isolation assumption. -/
theorem saturation30 {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    14 ≤ (fullKeys q .row).card ∧ 14 ≤ (fullKeys q .col).card ∧
    ((fullKeys q .diff).card = 15 ∨ (fullKeys q .sum).card = 15) ∧
    (((fullKeys q .row).card = 14 ∨ (fullKeys q .col).card = 14) →
      (fullKeys q .diff).card = 15 ∧ (fullKeys q .sum).card = 15) :=
  coarse_saturation hg len (no_isolated30 hg len)

#print axioms no_isolated30
#print axioms saturation30
end Gardner.Bridge
