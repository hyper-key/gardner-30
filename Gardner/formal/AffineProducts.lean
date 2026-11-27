import Gardner.formal.StructureBridge
namespace Gardner.Grid30

structure Affine where
  X : Int
  Y : Int
  C : Int

-- keep = false means taking only the homogeneous degree-one part of each factor.
def affineProd (keep : Bool) : List Affine → Int → Int → Int
  | [], _, _ => 1
  | l::ls, x, y => (l.X*x + l.Y*y + (if keep then l.C else 0)) * affineProd keep ls x y

def weightedProd (keep : Bool) (ls : List Affine) (a b : Nat) :=
  functional (fun x y => x^a*y^b*affineProd keep ls x y)

private theorem weighted_linear_three (s : List (Int × Int)) (A B C : Int) (f g h : Int → Int) :
    weighted s (fun x => A*f x+B*g x+C*h x) =
      A*weighted s f+B*weighted s g+C*weighted s h := by
  induction s with
  | nil => simp [weighted]
  | cons p s ih => simp only [weighted,ih]; grind

private theorem functional_linear_three (A B C : Int) (f g h : Int → Int → Int) :
    functional (fun x y => A*f x y+B*g x y+C*h x y) =
      A*functional f+B*functional g+C*functional h := by
  simp only [functional, weighted_linear_three]

theorem weighted_cons (keep : Bool) (l : Affine) (ls : List Affine) (a b : Nat) :
    weightedProd keep (l::ls) a b = l.X * weightedProd keep ls (a+1) b +
      l.Y * weightedProd keep ls a (b+1) + (if keep then l.C else 0)* weightedProd keep ls a b := by
  unfold weightedProd
  rw [← functional_linear_three]
  congr 1
  funext x y
  simp only [affineProd,Int.pow_succ]
  grind

theorem vanish_low (keep : Bool) (ls : List Affine) (a b : Nat) (degree : a+b+ls.length < 58) :
    weightedProd keep ls a b = 0 := by
  induction ls generalizing a b with
  | nil =>
    have v := coefficient_monomial (a:=a) (b:=b) (by simpa using (show a+b+[].length ≤ 59 by omega))
    have h : ¬(a=29 ∧ b=29) := by simp at degree; omega
    simpa [weightedProd, affineProd, h] using v
  | cons l ls ih =>
    simp only [List.length_cons] at degree
    rw [weighted_cons, ih (a+1) b (by omega), ih a (b+1) (by omega), ih a b (by omega)]
    simp

-- For all integer slopes and intercepts, the top homogeneous part gives the
-- complete functional as long as the total degree is at most 58.
theorem intercept_independent (ls : List Affine) (a b : Nat) (degree : a+b+ls.length ≤ 58) :
    weightedProd true ls a b = weightedProd false ls a b := by
  induction ls generalizing a b with
  | nil => rfl
  | cons l ls ih =>
    simp only [List.length_cons] at degree
    rw [weighted_cons,weighted_cons,ih (a+1) b (by omega),ih a (b+1) (by omega),
      vanish_low true ls a b (by omega)]
    simp


def groupLines (A B : Int) (roots : List Int) : List Affine :=
  roots.map fun k => ⟨A,B,-k⟩

def chessLines (xs ys ds ss : List Int) :=
  groupLines 1 0 xs ++ groupLines 0 1 ys ++ groupLines 1 (-1) ds ++ groupLines 1 1 ss

private theorem prod_append (k : Bool) (f g : List Affine) (x y : Int) :
    affineProd k (f++g) x y = affineProd k f x y * affineProd k g x y := by
  induction f with
  | nil => simp [affineProd]
  | cons l ls ih => simp [affineProd, ih, Int.mul_assoc]

private theorem group_homog (A B : Int) (ks : List Int) (x y : Int) :
    affineProd false (groupLines A B ks) x y = (A*x+B*y)^ks.length := by
  induction ks with
  | nil => simp [affineProd,groupLines]
  | cons t ts ih =>
    simp only [groupLines,List.map_cons,affineProd, Bool.false_eq_true, ite_false,Int.add_zero,
      List.length_cons,Int.pow_succ]
    change (A*x+B*y)*affineProd false (groupLines A B ts) x y = _
    rw [ih,Int.mul_comm]

private theorem chess_top (xs ys ds ss : List Int) (x y : Int) :
    affineProd false (chessLines xs ys ds ss) x y = topForm xs.length ys.length ds.length ss.length x y := by
  simp only [chessLines,prod_append,group_homog,topForm]
  simp [Int.sub_eq_add_neg]

private theorem weighted_zero_at (s : List (Int × Int)) (f : Int → Int) (h : ∀ p ∈ s, f p.1=0) :
    weighted s f = 0 := by
  induction s with
  | nil => rfl
  | cons z s ih =>
    simp only [weighted, h z (by simp), ih (fun p hp => h p (by simp [hp])),Int.mul_zero,Int.add_zero]

private theorem zero_on_grid (f : Int → Int → Int) (h : ∀ i j : Fin 30, f (coord i) (coord j)=0) :
    functional f = 0 := by
  apply weighted_zero_at
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  apply weighted_zero_at
  intro p hp
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
  exact h ⟨i,List.mem_range.mp hi⟩ ⟨j,List.mem_range.mp hj⟩


-- This recurrence sums the terms taking the constant part of one factor.
-- Remaining factors in the constant branch are purely homogeneous.
def oneConstant : List Affine → Nat → Nat → Int
  | [], _, _ => 0
  | l :: ls, a, b => l.X * oneConstant ls (a+1) b +
      l.Y * oneConstant ls a (b+1) + l.C*weightedProd false ls a b

theorem one_constant_at_59 (ls : List Affine) (a b : Nat) (deg : a+b+ls.length ≤ 59) :
    weightedProd true ls a b = weightedProd false ls a b + oneConstant ls a b := by
  induction ls generalizing a b with
  | nil => simp [weightedProd,affineProd,oneConstant]
  | cons l ls ih =>
    simp only [List.length_cons] at deg
    rw [weighted_cons,weighted_cons,ih (a+1) b (by omega),ih a (b+1) (by omega),
        intercept_independent ls a b (by omega)]
    simp only [oneConstant,ite_true,Bool.false_eq_true,ite_false]
    grind


-- Degree 60 additionally permits exactly two constant-factor choices.
def twoConstants : List Affine → Nat → Nat → Int
  | [], _, _ => 0
  | l :: ls, a, b => l.X * twoConstants ls (a+1) b +
      l.Y * twoConstants ls a (b+1) + l.C*oneConstant ls a b

theorem two_constants_at_60 (ls : List Affine) (a b : Nat) (deg : a+b+ls.length ≤ 60) :
    weightedProd true ls a b = weightedProd false ls a b + oneConstant ls a b +
      twoConstants ls a b := by
  induction ls generalizing a b with
  | nil => simp [weightedProd,affineProd,oneConstant,twoConstants]
  | cons l ls ih =>
    simp only [List.length_cons] at deg
    rw [weighted_cons,weighted_cons,ih (a+1) b (by omega),ih a (b+1) (by omega),
        one_constant_at_59 ls a b (by omega)]
    simp only [twoConstants,oneConstant,ite_true,Bool.false_eq_true,ite_false]
    grind

-- Applies directly to arbitrary lists of intercepts, including repeated
-- factors inserted to pad a line cover to any one of the nonzero quotas.
theorem no_cover_at_quota (xs ys ds ss : List Int) (k : Int)
    (ht : (xs.length,ys.length,ds.length,ss.length,k) ∈ quotaTable) (hk : k≠0) :
    ¬ ∀ i j : Fin 30, affineProd true (chessLines xs ys ds ss) (coord i) (coord j)=0 := by
  intro cover
  have tableSum : ∀ z ∈ quotaTable, z.1+z.2.1+z.2.2.1+z.2.2.2.1=58 := by decide
  have total := tableSum _ ht
  have deg : (chessLines xs ys ds ss).length ≤ 58 := by
    change xs.length+ys.length+ds.length+ss.length=58 at total
    simpa [chessLines,groupLines,Nat.add_assoc] using (show xs.length+ys.length+ds.length+ss.length ≤ 58 by omega)
  have eq := intercept_independent (chessLines xs ys ds ss) 0 0 (by simpa using deg)
  simp only [weightedProd,Int.pow_zero,Int.one_mul,chess_top] at eq
  have top := top_form_table _ ht
  change functional (topForm xs.length ys.length ds.length ss.length) = scale^2*k at top
  rw [zero_on_grid _ cover,top] at eq
  exact hk ((Int.mul_eq_zero.mp eq.symm).resolve_left (by decide))

#print axioms two_constants_at_60
#print axioms one_constant_at_59
#print axioms no_cover_at_quota
#print axioms intercept_independent
end Gardner.Grid30

namespace Gardner.Bridge
open Grid30

private def intercept (d : Dir) (k : Nat) : Int :=
  match d with | .row | .col => 2*(k:Int)-29 | .sum | .diff => 2*(k:Int)-58

private noncomputable def padded (q : List Square) (d : Dir) (m : Nat) : List Int :=
  (fullKeys q d).toList.map (intercept d) ++ List.replicate (m-(fullKeys q d).card) 0

private theorem padded_len (q : List Square) (d : Dir) (m : Nat) (h : (fullKeys q d).card ≤ m) :
    (padded q d m).length=m := by simp [padded]; omega

private theorem root_mem {q : List Square} {d : Dir} {p : Square} (m : Nat)
    (h : occupancy 30 q d (key 30 d p)=2) :
    intercept d (key 30 d p) ∈ padded q d m := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨_,Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨?_,h⟩),rfl⟩
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by change 0<occupancy 30 q d (key 30 d p); omega))

private theorem vanishing_group (A B : Int) (ks : List Int) (a x y : Int)
    (member : a ∈ ks) (zero : A*x+B*y-a=0) : affineProd true (groupLines A B ks) x y=0 := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    change (A*x+B*y+-k)*affineProd true (groupLines A B ks) x y=0
    obtain rfl | h := List.mem_cons.mp member
    · have hx : A*x+B*y+-a=0 := by omega
      rw [hx]; simp
    · rw [ih h]; simp

theorem quota_obstruction (q : List Square) (hg : Good 30 q)
    (paired : ∀ p ∈ q, SaturatedAt 30 q p)
    (a b d s : Nat) (K : Int) (ht : (a,b,d,s,K) ∈ quotaTable)
    (h₁ : (fullKeys q .row).card ≤ a) (h₂ : (fullKeys q .col).card ≤ b)
    (h₃ : (fullKeys q .diff).card ≤ d) (h₄ : (fullKeys q .sum).card ≤ s) : K=0 := by
  by_contra hK
  apply no_cover_at_quota (padded q .row a) (padded q .col b) (padded q .diff d) (padded q .sum s) K
    (by simpa only [padded_len q _ _ h₁,padded_len q _ _ h₂,padded_len q _ _ h₃,padded_len q _ _ h₄] using ht) hK
  intro i j
  let p : Square := (i.val,j.val)
  obtain ⟨direction,hd⟩ := coverage_without_isolated hg paired p ⟨i.isLt,j.isLt⟩
  simp only [chessLines, Grid30.prod_append]
  cases direction with
  | row =>
    have v := vanishing_group 1 0 _ _ (coord i) (coord j) (root_mem a hd) (by simp [key,coord,p,intercept])
    rw [v]; simp
  | col =>
    have v := vanishing_group 0 1 _ _ (coord i) (coord j) (root_mem b hd) (by simp [key,coord,p,intercept])
    rw [v]; simp
  | diff =>
    have o := j.isLt
    have v := vanishing_group 1 (-1) _ _ (coord i) (coord j) (root_mem d hd) (by simp [key,coord,p,intercept]; omega)
    rw [v]; simp
  | sum =>
    have v := vanishing_group 1 1 _ _ (coord i) (coord j) (root_mem s hd) (by simp [key,coord,p,intercept]; omega)
    rw [v]; simp


-- The coarse saturation pattern follows from the fixed geometry as soon as
-- the isolated-queen case has been eliminated.
theorem coarse_saturation {q : List Square} (hg : Good 30 q) (len : q.length=30)
    (paired : ∀ p ∈ q, SaturatedAt 30 q p) :
    14 ≤ (fullKeys q .row).card ∧ 14 ≤ (fullKeys q .col).card ∧
    ((fullKeys q .diff).card=15 ∨ (fullKeys q .sum).card=15) ∧
    (((fullKeys q .row).card=14 ∨ (fullKeys q .col).card=14) →
      (fullKeys q .diff).card=15 ∧ (fullKeys q .sum).card=15) := by
  have X := full_count_le_15 len .row
  have Y := full_count_le_15 len .col
  have D := full_count_le_15 len .diff
  have S := full_count_le_15 len .sum
  have cut := quota_obstruction q hg paired
  have xx := cut 13 15 15 15 (-6435) (by decide)
  have yy := cut 15 13 15 15 6435 (by decide)
  have ds := cut 15 15 14 14 (-3432) (by decide)
  have xd := cut 14 15 14 15 (-3432) (by decide)
  have xs := cut 14 15 15 14 (-3432) (by decide)
  have yd := cut 15 14 14 15 (-3432) (by decide)
  have ys := cut 15 14 15 14 3432 (by decide)
  omega

#print axioms coarse_saturation
#print axioms quota_obstruction
end Gardner.Bridge
