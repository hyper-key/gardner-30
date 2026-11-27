import Std
namespace Gardner

private theorem square_upper (x : Int) (h : -14 ≤ x ∧ x ≤ 14) : x^2 ≤ 196 := by
  have := Int.mul_nonneg (a := x+14) (b := 14-x) (by omega) (by omega)
  grind

private theorem consecutive (x : Int) : 0 ≤ (x+6)*(x+7) := by
  by_cases h : -6 ≤ x
  · exact Int.mul_nonneg (by omega) (by omega)
  · exact Int.mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)

private theorem upper22 (x : Int) (h : 0 ≤ x ∧ x ≤ 22) : x^2 ≤ 22*x := by
  have := Int.mul_nonneg (a := x) (b := 22-x) h.1 (by omega)
  grind

private theorem large_entry (x a b c : Int) (hx : 23 ≤ x)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : x+a+b+c=30) (hq : x^2+a^2+b^2+c^2=674) : False := by
  have hab := Int.mul_nonneg ha hb
  have hbc := Int.mul_nonneg hb hc
  have hac := Int.mul_nonneg ha hc
  have ub : a^2+b^2+c^2 ≤ (a+b+c)^2 := by grind
  have lb : 0 ≤ a^2+b^2+c^2 := by
    have := Int.sq_nonneg a; have := Int.sq_nonneg b; have := Int.sq_nonneg c; omega
  by_cases hh : 26 ≤ x
  · have := Int.mul_nonneg (a:=x-26) (b:=x+26) (by omega) (by omega)
    grind
  · have := show x = 23 ∨ x = 24 ∨ x = 25 by omega
    have ss : a+b+c = 30-x := by omega
    rw [ss] at ub
    rcases this with rfl | rfl | rfl <;> simp only [Int.reduceSub, Int.reducePow] at * <;> omega

private theorem no674 (a b c d : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hs : a+b+c+d=30) (hq : a^2+b^2+c^2+d^2=674) : False := by
  by_cases h₁ : 23 ≤ a
  · exact large_entry a b c d h₁ hb hc hd hs hq
  by_cases h₂ : 23 ≤ b
  · exact large_entry b a c d h₂ ha hc hd (by omega) (by grind)
  by_cases h₃ : 23 ≤ c
  · exact large_entry c a b d h₃ ha hb hd (by omega) (by grind)
  by_cases h₄ : 23 ≤ d
  · exact large_entry d a b c h₄ ha hb hc (by omega) (by grind)
  have h1 := upper22 a ⟨ha,by omega⟩
  have h2 := upper22 b ⟨hb,by omega⟩
  have h3 := upper22 c ⟨hc,by omega⟩
  have h4 := upper22 d ⟨hd,by omega⟩
  omega

-- Seven target values are hypotheses. How any geometric subcase implies those
-- hypotheses must be justified separately.
theorem seven_moment_tail (a b c d : Int)
    (ha : -14 ≤ a ∧ a ≤ 14) (hb : -14 ≤ b ∧ b ≤ 14)
    (hc : -14 ≤ c ∧ c ≤ 14) (hd : -14 ≤ d ∧ d ≤ 14)
    (hs : a+b+c+d = -26)
    (hq : a^2+b^2+c^2+d^2 ∈ ([-1062,170,954,1290,1178,618,-390] : List Int)) :
    a^2+b^2+c^2+d^2 = 170 ∧ (a = -7 ∨ b = -7 ∨ c = -7 ∨ d = -7) ∧
    ∀ t ∈ [a,b,c,d], t = -7 ∨ t = -6 := by
  have h1 := square_upper a ha
  have h2 := square_upper b hb
  have h3 := square_upper c hc
  have h4 := square_upper d hd
  have lb : 0 ≤ a^2+b^2+c^2+d^2 := by
    have := Int.sq_nonneg a; have := Int.sq_nonneg b; have := Int.sq_nonneg c
    have := Int.sq_nonneg d; omega
  have he : a^2+b^2+c^2+d^2 ≠ 618 := by
    intro h
    apply no674 (a+14) (b+14) (c+14) (d+14) (by omega) (by omega) (by omega) (by omega)
    · omega
    · grind
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  have eq : a^2+b^2+c^2+d^2=170 := by omega
  have hA := consecutive a
  have hB := consecutive b
  have hC := consecutive c
  have hD := consecutive d
  have zz : (a+6)*(a+7)+(b+6)*(b+7)+(c+6)*(c+7)+(d+6)*(d+7)=0 := by grind
  have rt (t : Int) (ht : (t+6)*(t+7)=0) : t = -7 ∨ t = -6 := by
    have h := Int.mul_eq_zero.mp ht
    omega
  have ra := rt a (by omega)
  have rb := rt b (by omega)
  have rc := rt c (by omega)
  have rd := rt d (by omega)
  refine ⟨eq, by omega, ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> assumption

#print axioms seven_moment_tail
end Gardner
