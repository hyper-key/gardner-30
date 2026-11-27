import Mathlib.Tactic.Ring

namespace Gardner.Kernel.MomentCuts

structure Problem where
  dkeys : List Int
  skeys : List Int
  dleft : Nat
  sleft : Nat
  dsum : Int
  ssum : Int
  squares : Int

def squareSum (xs : List Int) : Int := (xs.map (fun x => x^2)).sum

/-- A deliberately relaxed residual model: arbitrary multiplicities are
allowed. Every actual residual list is still represented. -/
structure Realizes (p : Problem) (ds ss : List Int) : Prop where
  d_domain : ∀ k ∈ ds, k ∈ p.dkeys
  s_domain : ∀ k ∈ ss, k ∈ p.skeys
  d_length : ds.length = p.dleft
  s_length : ss.length = p.sleft
  d_first : ds.sum = p.dsum
  s_first : ss.sum = p.ssum
  second : squareSum ds+squareSum ss = p.squares

structure Cut where
  quadratic : Int
  dlinear : Int
  dconstant : Int
  slinear : Int
  sconstant : Int

def ValidCut (p : Problem) (c : Cut) : Prop :=
  (∀ k ∈ p.dkeys, 0 ≤ c.quadratic*k^2+c.dlinear*k+c.dconstant) ∧
  (∀ k ∈ p.skeys, 0 ≤ c.quadratic*k^2+c.slinear*k+c.sconstant) ∧
  c.quadratic*p.squares+c.dlinear*p.dsum+c.dconstant*(p.dleft:Int)+
    c.slinear*p.ssum+c.sconstant*(p.sleft:Int) < 0

instance (p : Problem) (c : Cut) : Decidable (ValidCut p c) := by
  unfold ValidCut
  infer_instance

private theorem sum_nonnegative (a b c : Int) (xs : List Int)
    (h : ∀ k ∈ xs, 0 ≤ a*k^2+b*k+c) :
    0 ≤ a*squareSum xs+b*xs.sum+c*(xs.length:Int) := by
  induction xs with
  | nil => simp [squareSum]
  | cons k xs ih =>
    have head := h k (by simp)
    have tail := ih (fun t ht => h t (by simp [ht]))
    calc
      0 ≤ (a*k^2+b*k+c)+(a*squareSum xs+b*xs.sum+c*(xs.length:Int)) := add_nonneg head tail
      _ = _ := by
        simp only [squareSum,List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
        ring

theorem cut_sound (p : Problem) (c : Cut) (valid : ValidCut p c)
    (ds ss : List Int) (model : Realizes p ds ss) : False := by
  have d := sum_nonnegative c.quadratic c.dlinear c.dconstant ds
    (fun k hk => valid.1 k (model.d_domain k hk))
  have s := sum_nonnegative c.quadratic c.slinear c.sconstant ss
    (fun k hk => valid.2.1 k (model.s_domain k hk))
  have nonnegative : 0 ≤ c.quadratic*p.squares+c.dlinear*p.dsum+c.dconstant*(p.dleft:Int)+
      c.slinear*p.ssum+c.sconstant*(p.sleft:Int) := by
    rw [← model.second,← model.d_first,← model.s_first,← model.d_length,← model.s_length]
    calc
      0 ≤ (c.quadratic*squareSum ds+c.dlinear*ds.sum+c.dconstant*(ds.length:Int))+
          (c.quadratic*squareSum ss+c.slinear*ss.sum+c.sconstant*(ss.length:Int)) := add_nonneg d s
      _ = _ := by ring
  exact (not_lt_of_ge nonnegative) valid.2.2

inductive Proof where
  | cut (certificate : Cut)
  | splitD (next : Int → Proof)
  | splitS (next : Int → Proof)

def afterD (p : Problem) (k : Int) : Problem :=
  {p with dleft := p.dleft-1, dsum := p.dsum-k, squares := p.squares-k^2}

def afterS (p : Problem) (k : Int) : Problem :=
  {p with sleft := p.sleft-1, ssum := p.ssum-k, squares := p.squares-k^2}

/-- Fuel bounds only certificate depth. Each split checks every allowed key;
it makes no assumption on how the certificate was generated. -/
def check : Nat → Problem → Proof → Bool
  | _, p, .cut c => decide (ValidCut p c)
  | 0, _, .splitD _ => false
  | 0, _, .splitS _ => false
  | fuel+1, p, .splitD next => decide (0 < p.dleft) &&
      p.dkeys.all (fun k => check fuel (afterD p k) (next k))
  | fuel+1, p, .splitS next => decide (0 < p.sleft) &&
      p.skeys.all (fun k => check fuel (afterS p k) (next k))

theorem check_sound (fuel : Nat) (p : Problem) (proof : Proof) (accepted : check fuel p proof = true)
    (ds ss : List Int) (model : Realizes p ds ss) : False := by
  induction fuel generalizing p proof ds ss with
  | zero =>
    cases proof with
    | cut c => exact cut_sound p c (of_decide_eq_true accepted) ds ss model
    | splitD next => simp [check] at accepted
    | splitS next => simp [check] at accepted
  | succ fuel ih =>
    cases proof with
    | cut c => exact cut_sound p c (of_decide_eq_true accepted) ds ss model
    | splitD next =>
      have parts : decide (0 < p.dleft) = true ∧
          p.dkeys.all (fun k => check fuel (afterD p k) (next k)) = true := by
        simpa only [check,Bool.and_eq_true] using accepted
      have pos : 0 < p.dleft := of_decide_eq_true parts.1
      cases ds with
      | nil => have := model.d_length; simp at this; omega
      | cons k rest =>
        have member := model.d_domain k (by simp)
        have branch := List.all_eq_true.mp parts.2 k member
        apply ih (afterD p k) (next k) branch rest ss
        refine ⟨?_,model.s_domain,?_,model.s_length,?_,model.s_first,?_⟩
        · intro t ht; exact model.d_domain t (by simp [ht])
        · have := model.d_length; simp only [List.length_cons,afterD] at *; omega
        · have := model.d_first; simp only [List.sum_cons,afterD] at *; omega
        · have := model.second
          simp only [squareSum,List.map_cons,List.sum_cons,afterD] at *
          omega
    | splitS next =>
      have parts : decide (0 < p.sleft) = true ∧
          p.skeys.all (fun k => check fuel (afterS p k) (next k)) = true := by
        simpa only [check,Bool.and_eq_true] using accepted
      have pos : 0 < p.sleft := of_decide_eq_true parts.1
      cases ss with
      | nil => have := model.s_length; simp at this; omega
      | cons k rest =>
        have member := model.s_domain k (by simp)
        have branch := List.all_eq_true.mp parts.2 k member
        apply ih (afterS p k) (next k) branch ds rest
        refine ⟨model.d_domain,?_,model.d_length,?_,model.d_first,?_,?_⟩
        · intro t ht; exact model.s_domain t (by simp [ht])
        · have := model.s_length; simp only [List.length_cons,afterS] at *; omega
        · have := model.s_first; simp only [List.sum_cons,afterS] at *; omega
        · have := model.second
          simp only [squareSum,List.map_cons,List.sum_cons,afterS] at *
          omega

#print axioms check_sound
end Gardner.Kernel.MomentCuts
