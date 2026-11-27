import Gardner.formal.AffineProducts
import Mathlib.Tactic.Ring

namespace Gardner.Grid30

/-- The part obtained by taking one constant factor and homogeneous factors
everywhere else. This is a polynomial identity before applying the grid test. -/
def constantLayer : List Affine → Int → Int → Int
  | [], _, _ => 0
  | l :: ls, x, y =>
      l.C * affineProd false ls x y + (l.X*x + l.Y*y) * constantLayer ls x y

theorem homogeneous_append (ls ms : List Affine) (x y : Int) :
    affineProd false (ls ++ ms) x y = affineProd false ls x y * affineProd false ms x y := by
  induction ls with
  | nil => simp [affineProd]
  | cons l ls ih => simp [affineProd, ih, Int.mul_assoc]

theorem constantLayer_append (ls ms : List Affine) (x y : Int) :
    constantLayer (ls ++ ms) x y =
      constantLayer ls x y * affineProd false ms x y +
      affineProd false ls x y * constantLayer ms x y := by
  induction ls with
  | nil => simp [constantLayer, affineProd]
  | cons l ls ih => simp only [List.cons_append, constantLayer, homogeneous_append, affineProd,
      Bool.false_eq_true, ite_false, Int.add_zero, ih]; ring

theorem homogeneous_group (A B : Int) (rs : List Int) (x y : Int) :
    affineProd false (groupLines A B rs) x y = (A*x+B*y)^rs.length := by
  induction rs with
  | nil => simp [groupLines, affineProd]
  | cons r rs ih =>
    change ((A*x+B*y)+0) * affineProd false (groupLines A B rs) x y =
      (A*x+B*y)^(rs.length+1)
    rw [Int.add_zero, ih, Int.pow_succ, Int.mul_comm]

theorem constantLayer_group (A B : Int) (rs : List Int) (x y : Int) :
    constantLayer (groupLines A B rs) x y =
      -rs.sum * (A*x+B*y)^(rs.length-1) := by
  induction rs with
  | nil => simp [groupLines, constantLayer]
  | cons r rs ih =>
    cases rs with
    | nil => simp [groupLines, constantLayer, affineProd]
    | cons t ts =>
      change -r * affineProd false (groupLines A B (t::ts)) x y +
        (A*x+B*y)*constantLayer (groupLines A B (t::ts)) x y = _
      rw [homogeneous_group, ih]
      simp only [List.sum_cons, List.length_cons, Nat.add_sub_cancel, Int.pow_succ]
      ring

private theorem weighted_three (s : List (Int × Int)) (A B C : Int) (f g h : Int → Int) :
    weighted s (fun x => A*f x+B*g x+C*h x) =
      A*weighted s f+B*weighted s g+C*weighted s h := by
  induction s with
  | nil => simp [weighted]
  | cons p s ih => simp only [weighted, ih]; ring

theorem layer_functional_three (A B C : Int) (f g h : Int → Int → Int) :
    functional (fun x y => A*f x y+B*g x y+C*h x y) =
      A*functional f+B*functional g+C*functional h := by
  simp only [functional, weighted_three]

def weightedLayer (ls : List Affine) (a b : Nat) :=
  functional (fun x y => x^a*y^b*constantLayer ls x y)

theorem weightedLayer_cons (l : Affine) (ls : List Affine) (a b : Nat) :
    weightedLayer (l::ls) a b = l.X*weightedLayer ls (a+1) b +
      l.Y*weightedLayer ls a (b+1) + l.C*weightedProd false ls a b := by
  unfold weightedLayer weightedProd
  rw [← layer_functional_three]
  congr 1
  funext x y
  simp only [constantLayer, Int.pow_succ]
  ring

private theorem weighted_zero (s : List (Int × Int)) : weighted s (fun _ => 0) = 0 := by
  induction s with
  | nil => rfl
  | cons p s ih => simp [weighted, ih]

theorem weightedLayer_eq (ls : List Affine) (a b : Nat) :
    weightedLayer ls a b = oneConstant ls a b := by
  induction ls generalizing a b with
  | nil => simp [weightedLayer, constantLayer, oneConstant, functional, weighted_zero]
  | cons l ls ih => rw [weightedLayer_cons, ih, ih]; rfl

theorem constantLayer_chess (xs ys ds ss : List Int) (x y : Int) :
    constantLayer (chessLines xs ys ds ss) x y =
      -xs.sum * topForm (xs.length-1) ys.length ds.length ss.length x y +
      -ys.sum * topForm xs.length (ys.length-1) ds.length ss.length x y +
      -ds.sum * topForm xs.length ys.length (ds.length-1) ss.length x y +
      -ss.sum * topForm xs.length ys.length ds.length (ss.length-1) x y := by
  simp only [chessLines, constantLayer_append, homogeneous_append,
    constantLayer_group, homogeneous_group, topForm]
  simp only [Int.one_mul, Int.zero_mul, Int.add_zero, Int.zero_add, Int.neg_one_mul]
  simp only [sub_eq_add_neg]
  ring

theorem layer_functional_add (f g : Int → Int → Int) :
    functional (fun x y => f x y+g x y) = functional f+functional g := by
  simpa using layer_functional_three 1 1 0 f g (fun _ _ => 0)

theorem layer_functional_scale (a : Int) (f : Int → Int → Int) :
    functional (fun x y => a*f x y) = a*functional f := by
  simpa using layer_functional_three a 0 0 f (fun _ _ => 0) (fun _ _ => 0)

theorem oneConstant_chess (xs ys ds ss : List Int) :
    oneConstant (chessLines xs ys ds ss) 0 0 =
      -xs.sum * functional (topForm (xs.length-1) ys.length ds.length ss.length) +
      -ys.sum * functional (topForm xs.length (ys.length-1) ds.length ss.length) +
      -ds.sum * functional (topForm xs.length ys.length (ds.length-1) ss.length) +
      -ss.sum * functional (topForm xs.length ys.length ds.length (ss.length-1)) := by
  rw [← weightedLayer_eq]
  simp only [weightedLayer, Int.pow_zero, Int.one_mul, constantLayer_chess]
  rw [layer_functional_add, layer_functional_add, layer_functional_add]
  rw [layer_functional_scale, layer_functional_scale, layer_functional_scale,
    layer_functional_scale]

private theorem weighted_zero_on (s : List (Int × Int)) (f : Int → Int)
    (h : ∀ p ∈ s, f p.1 = 0) : weighted s f = 0 := by
  induction s with
  | nil => rfl
  | cons p s ih =>
    simp only [weighted, h p (by simp), ih (fun a ha => h a (by simp [ha])),
      Int.mul_zero, Int.add_zero]

theorem layer_grid_zero (f : Int → Int → Int)
    (h : ∀ i j : Fin 30, f (coord i) (coord j) = 0) : functional f = 0 := by
  apply weighted_zero_on
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  apply weighted_zero_on
  intro p hp
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hp
  exact h ⟨i, List.mem_range.mp hi⟩ ⟨j, List.mem_range.mp hj⟩

theorem chess_homogeneous (xs ys ds ss : List Int) (x y : Int) :
    affineProd false (chessLines xs ys ds ss) x y =
      topForm xs.length ys.length ds.length ss.length x y := by
  simp only [chessLines, homogeneous_append, homogeneous_group, topForm]
  simp [sub_eq_add_neg]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem odd_top_table : ∀ z ∈ ([(14,15,15,15),(15,14,15,15),
    (15,15,14,15),(15,15,15,14)] : List (Nat × Nat × Nat × Nat)),
    functional (topForm z.1 z.2.1 z.2.2.1 z.2.2.2) = 0 := by decide

/-- A degree-59 cover has zero first-constant layer. The homogeneous odd
part contributes zero to the centered grid functional. -/
theorem first_layer_zero (xs ys ds ss : List Int)
    (degree : xs.length + ys.length + ds.length + ss.length = 59)
    (homogeneous : functional (topForm xs.length ys.length ds.length ss.length) = 0)
    (cover : ∀ i j : Fin 30,
      affineProd true (chessLines xs ys ds ss) (coord i) (coord j) = 0) :
    oneConstant (chessLines xs ys ds ss) 0 0 = 0 := by
  have expansion := one_constant_at_59 (chessLines xs ys ds ss) 0 0
    (by simp [chessLines, groupLines]; omega)
  simp only [weightedProd, Int.pow_zero, Int.one_mul, chess_homogeneous] at expansion
  rw [layer_grid_zero _ cover, homogeneous] at expansion
  omega

/-- The coefficient equation excluding a deficient row axis. -/
theorem deficient_axis_equation (xs ys ds ss : List Int)
    (hx : xs.length = 14) (hy : ys.length = 15)
    (hd : ds.length = 15) (hs : ss.length = 15)
    (cover : ∀ i j : Fin 30,
      affineProd true (chessLines xs ys ds ss) (coord i) (coord j) = 0) :
    6435*xs.sum + 3432*(ds.sum+ss.sum) = 0 := by
  have ht := odd_top_table (14,15,15,15) (by decide)
  have eq := first_layer_zero xs ys ds ss (by omega) (by simpa [hx,hy,hd,hs] using ht) cover
  rw [oneConstant_chess] at eq
  simp only [hx,hy,hd,hs] at eq
  have xx := top_form_table (13,15,15,15,-6435) (by decide)
  have xy := top_form_table (14,14,15,15,0) (by decide)
  have xd := top_form_table (14,15,14,15,-3432) (by decide)
  have xs' := top_form_table (14,15,15,14,-3432) (by decide)
  change functional (topForm 13 15 15 15) = scale^2*(-6435) at xx
  change functional (topForm 14 14 15 15) = scale^2*0 at xy
  change functional (topForm 14 15 14 15) = scale^2*(-3432) at xd
  change functional (topForm 14 15 15 14) = scale^2*(-3432) at xs'
  norm_num only at eq
  rw [xx,xy,xd,xs'] at eq
  have factored : scale^2 * (6435*xs.sum + 3432*(ds.sum+ss.sum)) = 0 := by
    calc _ = _ := by ring
         _ = 0 := eq
  exact (Int.mul_eq_zero.mp factored).resolve_left (by decide)

theorem deficient_sum_equation (xs ys ds ss : List Int)
    (hx : xs.length = 15) (hy : ys.length = 15)
    (hd : ds.length = 15) (hs : ss.length = 14)
    (cover : ∀ i j : Fin 30,
      affineProd true (chessLines xs ys ds ss) (coord i) (coord j) = 0) :
    xs.sum-ys.sum+ds.sum = 0 := by
  have ht := odd_top_table (15,15,15,14) (by decide)
  have eq := first_layer_zero xs ys ds ss (by omega) (by simpa [hx,hy,hd,hs] using ht) cover
  rw [oneConstant_chess] at eq
  simp only [hx,hy,hd,hs] at eq
  have xs' := top_form_table (14,15,15,14,-3432) (by decide)
  have ys' := top_form_table (15,14,15,14,3432) (by decide)
  have ds' := top_form_table (15,15,14,14,-3432) (by decide)
  have ss' := top_form_table (15,15,15,13,0) (by decide)
  change functional (topForm 14 15 15 14) = scale^2*(-3432) at xs'
  change functional (topForm 15 14 15 14) = scale^2*3432 at ys'
  change functional (topForm 15 15 14 14) = scale^2*(-3432) at ds'
  change functional (topForm 15 15 15 13) = scale^2*0 at ss'
  norm_num only at eq
  rw [xs',ys',ds',ss'] at eq
  have factored : (scale^2*3432)*(xs.sum-ys.sum+ds.sum) = 0 := by
    calc _ = _ := by ring
         _ = 0 := eq
  exact (Int.mul_eq_zero.mp factored).resolve_left (by decide)

#print axioms first_layer_zero
#print axioms deficient_axis_equation

end Gardner.Grid30
