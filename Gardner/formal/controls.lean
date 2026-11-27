import GardnerSolution
namespace Gardner

example : ¬ Valid 4 [(0,0),(0,1),(0,3)] := by decide
example : ¬ Valid 4 [(0,0),(1,0),(3,0)] := by decide
example : ¬ Valid 4 [(0,3),(1,2),(3,0)] := by decide
example : ¬ Valid 4 [(0,0),(2,2),(3,3)] := by decide
example : ¬ Valid 4 [(1,2),(1,2)] := by decide
example : ¬ Valid 4 [(4,0)] := by decide
example : ¬ Valid 4 [(0,4)] := by decide
example : Valid 4 [(0,0)] := by decide
example : ¬ Good 4 [(0,0)] := by
  intro h
  exact h.2 (1,1) (by decide) (by decide) (by decide)

-- Requiring pair coverage at occupied squares would reject this good placement.
private def isolatedExample : List Square := [(0,0),(1,2),(1,3),(2,1),(2,3),(3,1),(3,2)]
example : Good 4 isolatedExample := by
  refine ⟨by decide, ?_⟩
  intro p hp he
  let small : ∀ r c : Fin 4, (r.val,c.val) ∈ isolatedExample ∨
      ¬ Valid 4 ((r.val,c.val) :: isolatedExample) := by decide
  exact (small ⟨p.1,hp.1⟩ ⟨p.2,hp.2⟩).resolve_left he
example : ¬ SaturatedAt 4 isolatedExample (0,0) := by
  rintro ⟨d, h⟩
  cases d <;> contradiction
end Gardner
