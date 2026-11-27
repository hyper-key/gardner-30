import GardnerDefs
namespace Gardner

theorem diff_key_iff {n : Nat} {p s : Square} (hp : onBoard n p) (hs : onBoard n s) :
    key n .diff p = key n .diff s ↔ p.1 + s.2 = s.1 + p.2 := by sorry

theorem add_fails_iff {n : Nat} {q : List Square} {p : Square}
    (hq : Valid n q) (hp : onBoard n p) (he : p ∉ q) :
    ¬ Valid n (p :: q) ↔ SaturatedAt n q p := by sorry

theorem upper31 : ∃ q : List Square, q.length = 31 ∧ Good 30 q := by sorry

end Gardner
