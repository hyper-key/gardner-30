import GardnerData
namespace Gardner
-- Drop precisely maximality, while retaining the board, line caps and size.
set_option maxRecDepth 10000 in
theorem upper31 : ∃ q : List Square, q.length = 31 ∧ Valid 30 q :=
  ⟨witness,rfl,by decide⟩
end Gardner
