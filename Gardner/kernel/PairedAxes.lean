import Gardner.kernel.Saturation
import Gardner.kernel.ConstantLayer
import Gardner.kernel.Transpose

namespace Gardner.Bridge
open Grid30

def centerShift : Dir → Int
  | .row | .col => 29
  | .diff | .sum => 58

def centeredKey (d : Dir) (k : Nat) : Int := 2*(k:Int)-centerShift d

noncomputable def coverRoots (q : List Square) (d : Dir) (m : Nat) : List Int :=
  (fullKeys q d).toList.map (centeredKey d) ++
    List.replicate (m-(fullKeys q d).card) 0

theorem coverRoots_length (q : List Square) (d : Dir) (m : Nat)
    (h : (fullKeys q d).card ≤ m) : (coverRoots q d m).length = m := by
  simp [coverRoots]
  omega

private theorem sum_affine (ks : List Nat) (a b : Int) :
    (ks.map (fun k : Nat => a*(k:Int)+b)).sum = a*(ks.sum:Int)+(ks.length:Int)*b := by
  induction ks with
  | nil => simp
  | cons k ks ih => simp only [List.map_cons, List.sum_cons, List.length_cons,
      Nat.cast_add, Nat.cast_one, ih]; ring

theorem coverRoots_sum (q : List Square) (d : Dir) (m : Nat) :
    (coverRoots q d m).sum = 2*((fullKeys q d).toList.sum:Int) -
      ((fullKeys q d).card:Int)*centerShift d := by
  have h := sum_affine (fullKeys q d).toList 2 (-centerShift d)
  simp only [coverRoots, List.sum_append, List.sum_replicate, nsmul_zero, add_zero]
  change ((fullKeys q d).toList.map (fun k : Nat => 2*(k:Int)-centerShift d)).sum = _
  simpa only [sub_eq_add_neg, Finset.length_toList, mul_neg] using h

private theorem affine_append (ls ms : List Affine) (x y : Int) :
    affineProd true (ls++ms) x y = affineProd true ls x y * affineProd true ms x y := by
  induction ls with
  | nil => simp [affineProd]
  | cons l ls ih => simp [affineProd, ih, Int.mul_assoc]

private theorem group_zero (A B : Int) (ks : List Int) (a x y : Int)
    (member : a ∈ ks) (zero : A*x+B*y-a = 0) :
    affineProd true (groupLines A B ks) x y = 0 := by
  induction ks with
  | nil => contradiction
  | cons k ks ih =>
    change (A*x+B*y+-k)*affineProd true (groupLines A B ks) x y = 0
    obtain rfl | h := List.mem_cons.mp member
    · have hx : A*x+B*y+-a = 0 := by omega
      rw [hx]; simp
    · rw [ih h]; simp

private theorem root_member {q : List Square} {d : Dir} {p : Square} (m : Nat)
    (h : occupancy 30 q d (key 30 d p) = 2) :
    centeredKey d (key 30 d p) ∈ coverRoots q d m := by
  apply List.mem_append_left
  apply List.mem_map.mpr
  refine ⟨_, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨?_,h⟩),rfl⟩
  exact List.mem_toFinset.mpr (List.count_pos_iff.mp (by
    change 0 < occupancy 30 q d (key 30 d p); omega))

theorem coverRoots_vanish {q : List Square} (hg : Good 30 q) (len : q.length = 30)
    (a b d s : Nat) : ∀ i j : Fin 30,
    affineProd true (chessLines (coverRoots q .row a) (coverRoots q .col b)
      (coverRoots q .diff d) (coverRoots q .sum s)) (coord i) (coord j) = 0 := by
  intro i j
  let p : Square := (i.val,j.val)
  obtain ⟨direction, hd⟩ := coverage_without_isolated hg (no_isolated30 hg len)
    p ⟨i.isLt,j.isLt⟩
  simp only [chessLines, affine_append]
  cases direction with
  | row =>
    have h := group_zero 1 0 _ _ (coord i) (coord j) (root_member a hd)
      (by simp [centeredKey,centerShift,key,coord,p])
    rw [h]; simp
  | col =>
    have h := group_zero 0 1 _ _ (coord i) (coord j) (root_member b hd)
      (by simp [centeredKey,centerShift,key,coord,p])
    rw [h]; simp
  | diff =>
    have h := group_zero 1 (-1) _ _ (coord i) (coord j) (root_member d hd)
      (by have hj := j.isLt; simp [centeredKey,centerShift,key,coord,p]; omega)
    rw [h]; simp
  | sum =>
    have h := group_zero 1 1 _ _ (coord i) (coord j) (root_member s hd)
      (by simp [centeredKey,centerShift,key,coord,p]; omega)
    rw [h]; simp

private theorem diagonal_key_sums {q : List Square} (ho : ∀ p ∈ q, onBoard 30 p) :
    (q.map (key 30 .sum)).sum + (q.map (key 30 .diff)).sum =
      2*(q.map Prod.fst).sum + 29*q.length := by
  induction q with
  | nil => rfl
  | cons p q ih =>
    have hp := ho p (by simp)
    have hq := ih (fun t ht => ho t (by simp [ht]))
    unfold onBoard at hp
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    simp only [key] at *
    omega

theorem paired_diagonal_root_sums {q : List Square} (hg : Good 30 q)
    (len : q.length = 30) (hd : (fullKeys q .diff).card = 15)
    (hs : (fullKeys q .sum).card = 15) :
    (coverRoots q .diff 15).sum + (coverRoots q .sum 15).sum =
      2*((q.map Prod.fst).sum:Int)-30*29 := by
  have pd := (complete_pairs len .diff hd).sum_eq
  have ps := (complete_pairs len .sum hs).sum_eq
  simp only [List.sum_append] at pd ps
  have total := diagonal_key_sums hg.1.2.1
  have half : (fullKeys q .diff).toList.sum + (fullKeys q .sum).toList.sum =
      (q.map Prod.fst).sum + 435 := by omega
  have cast := congrArg (fun n : Nat => (n:Int)) half
  simp only [Nat.cast_add] at cast
  rw [coverRoots_sum,coverRoots_sum,hd,hs]
  simp only [centerShift]
  omega

/-- Each axis of a hypothetical maximal size-30 placement has fifteen pairs.
The row half follows directly from the actual affine line cover. -/
theorem paired_rows30 {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    (fullKeys q .row).card = 15 := by
  have coarse := saturation30 hg len
  have upper := full_count_le_15 len .row
  by_contra ne
  have row14 : (fullKeys q .row).card = 14 := by omega
  have diagonals := coarse.2.2.2 (.inl row14)
  have hcol := full_count_le_15 len .col
  have hx := coverRoots_length q .row 14 (by omega)
  have hy := coverRoots_length q .col 15 hcol
  have hd := coverRoots_length q .diff 15 (by omega)
  have hs := coverRoots_length q .sum 15 (by omega)
  have eq := deficient_axis_equation (coverRoots q .row 14) (coverRoots q .col 15)
    (coverRoots q .diff 15) (coverRoots q .sum 15) hx hy hd hs
    (coverRoots_vanish hg len 14 15 15 15)
  rw [coverRoots_sum,paired_diagonal_root_sums hg len diagonals.1 diagonals.2] at eq
  simp only [centerShift,row14] at eq
  exact deficient_row_impossible hg len row14 diagonals.2 diagonals.1 (by omega)

#print axioms paired_rows30

theorem paired_columns30 {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    (fullKeys q .col).card = 15 := by
  have rows := paired_rows30 (transpose_good hg) (by simpa using len)
  change ((q.map Prod.snd).toFinset.filter (fun k => (q.map Prod.snd).count k = 2)).card = 15
  simpa only [fullKeys, occupancy, List.map_map, Function.comp_def, key,
    Prod.fst_swap] using rows

theorem paired_axes30 {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    (fullKeys q .row).card = 15 ∧ (fullKeys q .col).card = 15 :=
  ⟨paired_rows30 hg len,paired_columns30 hg len⟩

#print axioms paired_axes30
end Gardner.Bridge
