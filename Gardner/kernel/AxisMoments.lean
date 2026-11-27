import Gardner.kernel.PairedAxes
import Gardner.kernel.SecondLayer

namespace Gardner.Bridge
open Grid30

private theorem raw_projections {q : List Square} (ho : ∀ p ∈ q, onBoard 30 p) :
    (q.map (key 30 .sum)).sum = (q.map Prod.fst).sum+(q.map Prod.snd).sum ∧
    (q.map (key 30 .diff)).sum+(q.map Prod.snd).sum =
      (q.map Prod.fst).sum+29*q.length := by
  induction q with
  | nil => decide
  | cons p q ih =>
    have hp := ho p (by simp)
    have hq := ih (fun t ht => ho t (by simp [ht]))
    unfold onBoard at hp
    simp only [List.map_cons,List.sum_cons,List.length_cons,key] at *
    exact ⟨by omega,by omega⟩

theorem paired_difference_root_sum {q : List Square} (hg : Good 30 q)
    (len : q.length = 30) (hd : (fullKeys q .diff).card = 15) :
    (coverRoots q .diff 15).sum =
      (coverRoots q .row 15).sum-(coverRoots q .col 15).sum := by
  have hr := paired_rows30 hg len
  have hc := paired_columns30 hg len
  have rp := (complete_pairs len .row hr).sum_eq
  have cp := (complete_pairs len .col hc).sum_eq
  have dp := (complete_pairs len .diff hd).sum_eq
  simp only [List.sum_append] at rp cp dp
  have projections := raw_projections hg.1.2.1
  have equation : 2*(fullKeys q .diff).toList.sum+2*(fullKeys q .col).toList.sum =
      2*(fullKeys q .row).toList.sum+870 := by
    change (q.map Prod.fst).sum = _ at rp
    change (q.map Prod.snd).sum = _ at cp
    omega
  have cast := congrArg (fun n : Nat => (n:Int)) equation
  simp only [Nat.cast_add,Nat.cast_mul] at cast
  rw [coverRoots_sum,coverRoots_sum,coverRoots_sum,hr,hc,hd]
  simp only [centerShift]
  omega

theorem paired_sum_root_sum {q : List Square} (hg : Good 30 q)
    (len : q.length = 30) (hs : (fullKeys q .sum).card = 15) :
    (coverRoots q .sum 15).sum =
      (coverRoots q .row 15).sum+(coverRoots q .col 15).sum := by
  have hr := paired_rows30 hg len
  have hc := paired_columns30 hg len
  have rp := (complete_pairs len .row hr).sum_eq
  have cp := (complete_pairs len .col hc).sum_eq
  have sp := (complete_pairs len .sum hs).sum_eq
  simp only [List.sum_append] at rp cp sp
  have projections := raw_projections hg.1.2.1
  have equation : 2*(fullKeys q .sum).toList.sum =
      2*(fullKeys q .row).toList.sum+2*(fullKeys q .col).toList.sum := by
    change (q.map Prod.fst).sum = _ at rp
    change (q.map Prod.snd).sum = _ at cp
    omega
  have cast := congrArg (fun n : Nat => (n:Int)) equation
  simp only [Nat.cast_add,Nat.cast_mul] at cast
  rw [coverRoots_sum,coverRoots_sum,coverRoots_sum,hr,hc,hs]
  simp only [centerShift]
  omega

/-- The moment invariant used for the fully paired projected domain, now
derived from the original placement and the actual affine line cover. -/
theorem fully_paired_axis_moment {q : List Square} (hg : Good 30 q)
    (len : q.length = 30) (hd : (fullKeys q .diff).card = 15)
    (hs : (fullKeys q .sum).card = 15) :
    21*(coverRoots q .row 15).sum^2 -
      5*((coverRoots q .row 15).map (fun x => x^2)).sum =
    21*(coverRoots q .col 15).sum^2 -
      5*((coverRoots q .col 15).map (fun y => y^2)).sum := by
  apply full_axis_moment_identity (coverRoots q .row 15) (coverRoots q .col 15)
    (coverRoots q .diff 15) (coverRoots q .sum 15)
  · exact coverRoots_length q .row 15 (full_count_le_15 len .row)
  · exact coverRoots_length q .col 15 (full_count_le_15 len .col)
  · exact coverRoots_length q .diff 15 (by omega)
  · exact coverRoots_length q .sum 15 (by omega)
  · exact coverRoots_vanish hg len 15 15 15 15
  · exact paired_difference_root_sum hg len hd
  · exact paired_sum_root_sum hg len hs

theorem deficient_sum_axis_balance {q : List Square} (hg : Good 30 q)
    (len : q.length = 30) (hd : (fullKeys q .diff).card = 15)
    (hs : (fullKeys q .sum).card ≤ 14) :
    (coverRoots q .row 15).sum = (coverRoots q .col 15).sum := by
  have eq := deficient_sum_equation (coverRoots q .row 15) (coverRoots q .col 15)
    (coverRoots q .diff 15) (coverRoots q .sum 14)
    (coverRoots_length q .row 15 (full_count_le_15 len .row))
    (coverRoots_length q .col 15 (full_count_le_15 len .col))
    (coverRoots_length q .diff 15 (by omega)) (coverRoots_length q .sum 14 hs)
    (coverRoots_vanish hg len 15 15 15 14)
  rw [paired_difference_root_sum hg len hd] at eq
  omega

#print axioms fully_paired_axis_moment
#print axioms deficient_sum_axis_balance
end Gardner.Bridge
