import Gardner.kernel.ConstantLayer
import Gardner.formal.FullMoment

namespace Gardner.Grid30

/-- Exactly two constant-factor choices in a product of affine factors. -/
def secondLayer : List Affine → Int → Int → Int
  | [], _, _ => 0
  | l::ls, x, y => l.C*constantLayer ls x y +
      (l.X*x+l.Y*y)*secondLayer ls x y

theorem secondLayer_append (ls ms : List Affine) (x y : Int) :
    secondLayer (ls++ms) x y = secondLayer ls x y*affineProd false ms x y +
      constantLayer ls x y*constantLayer ms x y +
      affineProd false ls x y*secondLayer ms x y := by
  induction ls with
  | nil => simp [secondLayer,constantLayer,affineProd]
  | cons l ls ih =>
    simp only [List.cons_append,secondLayer,constantLayer_append,
      constantLayer,affineProd,Bool.false_eq_true,ite_false,Int.add_zero,ih]
    ring

theorem secondLayer_group (A B : Int) (rs : List Int) (x y : Int) :
    secondLayer (groupLines A B rs) x y =
      pairSum rs * (A*x+B*y)^(rs.length-2) := by
  induction rs with
  | nil => simp [groupLines,secondLayer,pairSum]
  | cons r rs ih =>
    cases rs with
    | nil => simp [groupLines,secondLayer,constantLayer,pairSum]
    | cons t ts =>
      cases ts with
      | nil => simp [groupLines,secondLayer,constantLayer,affineProd,pairSum]
      | cons u us =>
        change -r*constantLayer (groupLines A B (t::u::us)) x y +
          (A*x+B*y)*secondLayer (groupLines A B (t::u::us)) x y = _
        rw [constantLayer_group,ih]
        have n1 : (t::u::us).length-1 = us.length+1 := by simp
        have n2 : (t::u::us).length-2 = us.length := by simp
        have n3 : (r::t::u::us).length-2 = us.length+1 := by simp
        rw [n1,n2,n3]
        simp only [pairSum,List.sum_cons,Int.pow_succ]
        ring

def weightedSecond (ls : List Affine) (a b : Nat) :=
  functional (fun x y => x^a*y^b*secondLayer ls x y)

theorem weightedSecond_cons (l : Affine) (ls : List Affine) (a b : Nat) :
    weightedSecond (l::ls) a b = l.X*weightedSecond ls (a+1) b +
      l.Y*weightedSecond ls a (b+1) + l.C*weightedLayer ls a b := by
  unfold weightedSecond weightedLayer
  rw [← layer_functional_three]
  congr 1
  funext x y
  simp only [secondLayer,Int.pow_succ]
  ring

theorem weightedSecond_eq (ls : List Affine) (a b : Nat) :
    weightedSecond ls a b = twoConstants ls a b := by
  induction ls generalizing a b with
  | nil =>
    have h := layer_grid_zero (fun _ _ => 0) (by intros; rfl)
    simpa [weightedSecond,secondLayer,twoConstants] using h
  | cons l ls ih =>
    rw [weightedSecond_cons,ih,ih,weightedLayer_eq]
    rfl

theorem secondLayer_full_chess (xs ys ds ss : List Int)
    (hx : xs.length=15) (hy : ys.length=15) (hd : ds.length=15) (hs : ss.length=15)
    (x y : Int) :
    secondLayer (chessLines xs ys ds ss) x y =
      pairSum xs*topForm 13 15 15 15 x y +
      pairSum ys*topForm 15 13 15 15 x y +
      pairSum ds*topForm 15 15 13 15 x y +
      pairSum ss*topForm 15 15 15 13 x y +
      xs.sum*ys.sum*topForm 14 14 15 15 x y +
      xs.sum*ds.sum*topForm 14 15 14 15 x y +
      xs.sum*ss.sum*topForm 14 15 15 14 x y +
      ys.sum*ds.sum*topForm 15 14 14 15 x y +
      ys.sum*ss.sum*topForm 15 14 15 14 x y +
      ds.sum*ss.sum*topForm 15 15 14 14 x y := by
  simp only [chessLines,secondLayer_append,constantLayer_append,homogeneous_append,
    secondLayer_group,constantLayer_group,homogeneous_group,hx,hy,hd,hs,topForm]
  norm_num only
  simp only [Int.one_mul,Int.zero_mul,Int.add_zero,Int.zero_add,Int.neg_one_mul,sub_eq_add_neg]
  ring

theorem first_layer_full_zero (xs ys ds ss : List Int)
    (hx : xs.length=15) (hy : ys.length=15) (hd : ds.length=15) (hs : ss.length=15) :
    oneConstant (chessLines xs ys ds ss) 0 0 = 0 := by
  rw [oneConstant_chess]
  simp only [hx,hy,hd,hs]
  norm_num only
  have a := odd_top_table (14,15,15,15) (by decide)
  have b := odd_top_table (15,14,15,15) (by decide)
  have c := odd_top_table (15,15,14,15) (by decide)
  have d := odd_top_table (15,15,15,14) (by decide)
  change functional (topForm 14 15 15 15) = 0 at a
  change functional (topForm 15 14 15 15) = 0 at b
  change functional (topForm 15 15 14 15) = 0 at c
  change functional (topForm 15 15 15 14) = 0 at d
  rw [a,b,c,d]
  ring

theorem second_layer_full_zero (xs ys ds ss : List Int)
    (hx : xs.length=15) (hy : ys.length=15) (hd : ds.length=15) (hs : ss.length=15)
    (cover : ∀ i j : Fin 30,
      affineProd true (chessLines xs ys ds ss) (coord i) (coord j) = 0) :
    functional (secondLayer (chessLines xs ys ds ss)) = 0 := by
  have expansion := two_constants_at_60 (chessLines xs ys ds ss) 0 0
    (by simp [chessLines,groupLines,hx,hy,hd,hs])
  simp only [weightedProd,Int.pow_zero,Int.one_mul,chess_homogeneous,hx,hy,hd,hs] at expansion
  rw [layer_grid_zero _ cover,fully_paired_top,first_layer_full_zero xs ys ds ss hx hy hd hs]
    at expansion
  have zero : twoConstants (chessLines xs ys ds ss) 0 0 = 0 := by omega
  rw [← weightedSecond_eq] at zero
  simpa only [weightedSecond,Int.pow_zero,Int.one_mul] using zero

private theorem quota_values :
    functional (topForm 13 15 15 15) = scale^2*(-6435) ∧
    functional (topForm 15 13 15 15) = scale^2*6435 ∧
    functional (topForm 15 15 13 15) = 0 ∧
    functional (topForm 15 15 15 13) = 0 ∧
    functional (topForm 14 14 15 15) = 0 ∧
    functional (topForm 14 15 14 15) = scale^2*(-3432) ∧
    functional (topForm 14 15 15 14) = scale^2*(-3432) ∧
    functional (topForm 15 14 14 15) = scale^2*(-3432) ∧
    functional (topForm 15 14 15 14) = scale^2*3432 ∧
    functional (topForm 15 15 14 14) = scale^2*(-3432) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact top_form_table (13,15,15,15,-6435) (by decide)
  · exact top_form_table (15,13,15,15,6435) (by decide)
  · simpa using top_form_table (15,15,13,15,0) (by decide)
  · simpa using top_form_table (15,15,15,13,0) (by decide)
  · simpa using top_form_table (14,14,15,15,0) (by decide)
  · exact top_form_table (14,15,14,15,-3432) (by decide)
  · exact top_form_table (14,15,15,14,-3432) (by decide)
  · exact top_form_table (15,14,14,15,-3432) (by decide)
  · exact top_form_table (15,14,15,14,3432) (by decide)
  · exact top_form_table (15,15,14,14,-3432) (by decide)

theorem full_second_layer_formula (xs ys ds ss : List Int)
    (hx : xs.length=15) (hy : ys.length=15) (hd : ds.length=15) (hs : ss.length=15) :
    functional (secondLayer (chessLines xs ys ds ss)) = scale^2 *
      (-6435*pairSum xs + 6435*pairSum ys - 3432*xs.sum*ds.sum - 3432*xs.sum*ss.sum
        -3432*ys.sum*ds.sum + 3432*ys.sum*ss.sum - 3432*ds.sum*ss.sum) := by
  change functional (fun x y => secondLayer (chessLines xs ys ds ss) x y) = _
  simp_rw [secondLayer_full_chess xs ys ds ss hx hy hd hs]
  simp only [layer_functional_add,layer_functional_scale]
  obtain ⟨a,b,c,d,e,f,g,h,i,j⟩ := quota_values
  rw [a,b,c,d,e,f,g,h,i,j]
  ring

theorem full_axis_moment_identity (xs ys ds ss : List Int)
    (hx : xs.length=15) (hy : ys.length=15) (hd : ds.length=15) (hs : ss.length=15)
    (cover : ∀ i j : Fin 30,
      affineProd true (chessLines xs ys ds ss) (coord i) (coord j) = 0)
    (pairedD : ds.sum = xs.sum-ys.sum) (pairedS : ss.sum = xs.sum+ys.sum) :
    21*xs.sum^2-5*(xs.map (fun x => x^2)).sum =
      21*ys.sum^2-5*(ys.map (fun y => y^2)).sum := by
  apply full_omissions xs.sum ys.sum ds.sum ss.sum
    (xs.map (fun x => x^2)).sum (ys.map (fun y => y^2)).sum (pairSum xs) (pairSum ys)
    pairedD pairedS (pair_sum_formula xs) (pair_sum_formula ys)
  have zero := second_layer_full_zero xs ys ds ss hx hy hd hs cover
  rw [full_second_layer_formula xs ys ds ss hx hy hd hs] at zero
  exact (Int.mul_eq_zero.mp zero).resolve_left (by decide)

#print axioms second_layer_full_zero
#print axioms full_axis_moment_identity
end Gardner.Grid30
