import Std
namespace Gardner.Grid30

-- Coordinates are twice the usual centered coordinates of the board.
def coord (i : Nat) : Int := 2*(i : Int)-29
def weights : List Int := [-1, 29, -406, 3654, -23751, 118755, -475020, 1560780, -4292145, 10015005, -20030010, 34597290, -51895935, 67863915, -77558760, 77558760, -67863915, 51895935, -34597290, 20030010, -10015005, 4292145, -1560780, 475020, -118755, 23751, -3654, 406, -29, 1]
def weight (i : Nat) : Int := weights[i]?.getD 0
def grid : List (Int × Int) := (List.range 30).map fun i => (coord i, weight i)

-- The initial value and recurrence uniquely specify (-1)^(29-i) * choose(29,i).
theorem signed_weights : weight 0 = -1 ∧ ∀ i : Fin 29,
  ((i.val : Int)+1)*weight (i.val+1) = - (29-(i.val : Int))*weight i.val := by decide

def weighted : List (Int × Int) → (Int → Int) → Int
  | [], _ => 0
  | (x,w)::s, f => w*f x + weighted s f

def moment (k : Nat) := weighted grid (fun x => x^k)
def scale : Int := 4746884825265972078944013665697792000000
def functional (f : Int → Int → Int) := weighted grid (fun x => weighted grid (f x))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem signed_moments : ∀ k : Fin 31, moment k.val = (if k.val = 29 then scale else 0) := by decide

private theorem scalar_left (s : List (Int × Int)) (k : Int) (f : Int → Int) :
    weighted s (fun x => k*f x) = k*weighted s f := by
  induction s with
  | nil => simp [weighted]
  | cons p s ih => simp only [weighted,ih]; grind

private theorem scalar_right (s : List (Int × Int)) (k : Int) (f : Int → Int) :
    weighted s (fun x => f x*k) = weighted s f*k := by
  simp only [Int.mul_comm _ k]; rw [scalar_left]

private theorem additive (s : List (Int × Int)) (f g : Int → Int) :
    weighted s (fun x => f x + g x) = weighted s f + weighted s g := by
  induction s with
  | nil => rfl
  | cons p s ih => simp only [weighted,ih]; grind

theorem monomial (a b : Nat) : functional (fun x y => x^a*y^b) = moment a * moment b := by
  unfold functional moment
  simp only [scalar_left,scalar_right]

theorem coefficient_monomial {a b : Nat} (h : a+b ≤ 59) :
    functional (fun x y => x^a*y^b) = if a=29 ∧ b=29 then scale^2 else 0 := by
  rw [monomial]
  by_cases ha : a < 29
  · have m := signed_moments ⟨a,by omega⟩
    have hm : moment a = 0 := by simpa [show a ≠ 29 by omega] using m
    simp [hm,show a ≠ 29 by omega]
  by_cases hb : b < 29
  · have m := signed_moments ⟨b,by omega⟩
    have hm : moment b = 0 := by simpa [show b ≠ 29 by omega] using m
    simp [hm,show b ≠ 29 by omega]
  have h₁ := signed_moments ⟨a,by omega⟩
  have h₂ := signed_moments ⟨b,by omega⟩
  change moment a = _ at h₁
  change moment b = _ at h₂
  rw [h₁,h₂]
  by_cases e : a=29 <;> by_cases f : b=29 <;> simp [e,f,Int.pow_succ]


private theorem weighted_zero_on (s : List (Int × Int)) (f : Int → Int)
    (h : ∀ p ∈ s, f p.1 = 0) : weighted s f = 0 := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    have h₁ := h p (by simp)
    have h₂ := ih (fun a ha => h a (by simp [ha]))
    simp only [weighted,h₁,h₂,Int.mul_zero,Int.add_zero]

private theorem function_add (f g : Int → Int → Int) :
    functional (fun x y => f x y + g x y) = functional f + functional g := by
  unfold functional
  simp only [additive]

private theorem function_scale (k : Int) (f : Int → Int → Int) :
    functional (fun x y => k * f x y) = k * functional f := by
  unfold functional
  simp only [scalar_left]

private theorem function_zero_on (f : Int → Int → Int)
    (h : ∀ i j : Fin 30, f (coord i) (coord j) = 0) : functional f = 0 := by
  apply weighted_zero_on
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  apply weighted_zero_on
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact h ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩

structure Term where
  coeff : Int
  a : Nat
  b : Nat

def evalTerms : List Term → Int → Int → Int
  | [], _, _ => 0
  | t::ts, x, y => t.coeff * (x^t.a*y^t.b) + evalTerms ts x y

def coefficient : List Term → Int
  | [] => 0
  | t :: ts => (if t.a=29 ∧ t.b=29 then t.coeff else 0) + coefficient ts

theorem extracts_coefficient (ts : List Term) (degree : ∀ t ∈ ts, t.a+t.b ≤ 59) :
    functional (evalTerms ts) = scale^2 * coefficient ts := by
  induction ts with
  | nil =>
    have h : functional (evalTerms []) = 0 := function_zero_on _ (by intros; rfl)
    simp [h,coefficient]
  | cons t ts ih =>
    have ht := degree t (by simp)
    have hs := ih (fun s h => degree s (by simp [h]))
    change functional (fun x y => t.coeff * (x^t.a*y^t.b) + evalTerms ts x y) = _
    rw [function_add, function_scale, coefficient_monomial ht, hs]
    rw [show coefficient (t :: ts) = (if t.a=29 ∧ t.b=29 then t.coeff else 0) + coefficient ts from rfl]
    split <;> grind

theorem central_coefficient_zero (ts : List Term)
    (degree : ∀ t ∈ ts, t.a+t.b ≤ 59)
    (vanishes : ∀ i j : Fin 30, evalTerms ts (coord i) (coord j) = 0) :
    coefficient ts = 0 := by
  have h := function_zero_on _ vanishes
  rw [extracts_coefficient ts degree] at h
  exact (Int.mul_eq_zero.mp h).resolve_left (by decide)


theorem singleton_pair_centered {A u v : Int} (relation : 31*A+8*(u+v)=0)
    (bounds : -58 ≤ u+v ∧ u+v ≤ 58) (parity : (u+v)%2=0) : A=0 ∧ u+v=0 := by
  omega


def topForm (a b d s : Nat) (x y : Int) := x^a*y^b*(x-y)^d*(x+y)^s

def quotaTable : List (Nat × Nat × Nat × Nat × Int) :=
  [(13,15,15,15,-6435), (14,14,15,15,0), (14,15,14,15,-3432),
   (14,15,15,14,-3432), (15,13,15,15,6435), (15,14,14,15,-3432),
   (15,14,15,14,3432), (15,15,13,15,0), (15,15,14,14,-3432),
   (15,15,15,13,0)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem top_form_table : ∀ z ∈ quotaTable,
    functional (topForm z.1 z.2.1 z.2.2.1 z.2.2.2.1) = scale^2*z.2.2.2.2 := by decide

#print axioms top_form_table
#print axioms singleton_pair_centered
#print axioms signed_weights
#print axioms signed_moments
#print axioms coefficient_monomial
#print axioms central_coefficient_zero
end Gardner.Grid30
