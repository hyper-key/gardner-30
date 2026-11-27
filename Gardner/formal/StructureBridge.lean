import GardnerSolution
import Gardner.formal.GridFunctional
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card

namespace Gardner.Bridge

-- A full line is identified by a direction and its actual key in the fixed spec.
def fullKeys (q : List Square) (d : Dir) : Finset Nat :=
  (q.map (key 30 d)).toFinset.filter (fun k => occupancy 30 q d k = 2)

theorem coverage_without_isolated {q : List Square} (h : Good 30 q)
    (paired : ∀ p ∈ q, SaturatedAt 30 q p) :
    ∀ p, onBoard 30 p → SaturatedAt 30 q p := by
  intro p hp
  by_cases hmem : p ∈ q
  · exact paired p hmem
  · exact (add_fails_iff h.1 hp hmem).mp (h.2 p hp hmem)

private theorem paired_subperm (q : List Square) (d : Dir) :
    ((fullKeys q d).toList ++ (fullKeys q d).toList).Subperm (q.map (key 30 d)) := by
  classical
  let ks := (fullKeys q d).toList
  apply List.subperm_iff_count.mpr
  intro k
  simp only [List.count_append]
  have count := Finset.nodup_toList (fullKeys q d) |>.count (a := k)
  change ks.count k = _ at count
  rw [count]
  by_cases hm : k ∈ ks
  · have hf := Finset.mem_filter.mp (Finset.mem_toList.mp hm : k ∈ fullKeys q d)
    have hv : (q.map (key 30 d)).count k = 2 := hf.2
    simp [show k ∈ (fullKeys q d).toList from hm,hv]
  · simp [show k ∉ (fullKeys q d).toList from hm]

theorem full_count_le_15 {q : List Square} (h : q.length=30) (d : Dir) :
    (fullKeys q d).card ≤ 15 := by
  have hh := (paired_subperm q d).length_le
  simp [h] at hh
  omega

-- With 30 entries and 15 full lines, the entire list of projected keys is
-- exactly two copies of the list of full keys, up to permutation.
theorem complete_pairs {q : List Square} (len : q.length = 30) (d : Dir)
    (complete : (fullKeys q d).card = 15) :
    (q.map (key 30 d)).Perm ((fullKeys q d).toList ++ (fullKeys q d).toList) := by
  classical
  let ks := (fullKeys q d).toList
  have sub := paired_subperm q d
  obtain ⟨l,perm,sl⟩ := List.subperm_iff.mp sub
  have le : l.length = 30 := by simpa [len] using perm.length_eq

  have eq := sl.eq_of_length (by simp [le,complete])
  exact eq ▸ perm.symm

private theorem diag_sums {q : List Square} (ho : ∀ p ∈ q, onBoard 30 p) :
    (q.map (key 30 .sum)).sum + (q.map (key 30 .diff)).sum =
      2*(q.map Prod.fst).sum + 29*q.length ∧
    (q.map (fun p => key 30 .sum p % 2)).sum +
      (q.map (fun p => key 30 .diff p % 2)).sum = q.length := by
  induction q with
  | nil => decide
  | cons p q ih =>
    have hp := ho p (by simp)
    have hq := ih (fun t ht => ho t (by simp [ht]))
    unfold onBoard at hp
    have h : key 30 .sum p + key 30 .diff p = 2*p.1+29 := by change p.1+p.2+(p.1+(29-p.2))=_; omega
    have g : key 30 .sum p % 2 + key 30 .diff p % 2 = 1 := by omega
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    omega

private theorem parity_sum (l : List Nat) : (l.map (fun t => t%2)).sum % 2 = l.sum % 2 := by
  induction l with
  | nil => decide
  | cons h l ih => simp only [List.map_cons,List.sum_cons]; omega

-- Both completed diagonal families force the row sum to be even. In particular
-- they are incompatible with the zero centered row sum from the deficient-axis
-- coefficient calculation, which would force the original row sum to be 435.
theorem both_diagonals_parity {q : List Square} (hv : Valid 30 q) (len : q.length=30)
    (ds : (fullKeys q .sum).card=15) (dd : (fullKeys q .diff).card=15) :
    (q.map Prod.fst).sum % 2 = 0 := by
  have ps := complete_pairs len .sum ds
  have pd := complete_pairs len .diff dd
  let S := (fullKeys q .sum).toList
  let D := (fullKeys q .diff).toList
  change (q.map (key 30 .sum)).Perm (S++S) at ps
  change (q.map (key 30 .diff)).Perm (D++D) at pd
  have es := ps.sum_eq
  have ed := pd.sum_eq
  have os := (ps.map (fun k => k%2)).sum_eq
  have od := (pd.map (fun k => k%2)).sum_eq
  simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def] at es ed os od
  have ⟨t,p⟩ := diag_sums hv.2.1
  have hs := parity_sum S
  have hd := parity_sum D
  omega

theorem both_diagonals_centered_nonzero {q : List Square} (h : Good 30 q) (len : q.length=30)
    (ds : (fullKeys q .sum).card=15) (dd : (fullKeys q .diff).card=15) :
    2*((q.map Prod.fst).sum : Int) - 29*(q.length : Int) ≠ 0 := by
  have p := both_diagonals_parity h.1 len ds dd
  omega


-- This is the actual sum of the 14 centered saturated row keys. Linear is
-- exactly the remaining condition supplied by the degree-59 line product.
theorem deficient_row_impossible {q : List Square} (h : Good 30 q) (len : q.length=30)
    (row14 : (fullKeys q .row).card=14)
    (ds : (fullKeys q .sum).card=15) (dd : (fullKeys q .diff).card=15)
    (linear : 6435*(2*((fullKeys q .row).toList.sum : Int)-14*29) +
        3432*(2*((q.map Prod.fst).sum : Int)-30*29) = 0) : False := by
  let ks := (fullKeys q .row).toList
  obtain ⟨l,perm,sl⟩ := List.subperm_iff.mp (paired_subperm q .row)
  obtain ⟨extra, ex⟩ := sl.exists_perm_append
  have p := perm.symm.trans ex
  change (q.map Prod.fst).Perm ((ks++ks)++extra) at p
  have lk : ks.length = 14 := by simpa [ks] using row14
  have le := p.length_eq
  simp only [List.length_map,List.length_append,lk,len] at le
  have short : extra.length=2 := by omega
  have inside (x : Nat) (hx : x ∈ extra) : x < 30 := by
    have hm := p.mem_iff.mpr (List.mem_append_right _ hx)
    obtain ⟨pt,hp,rfl⟩ := List.mem_map.mp hm
    exact (h.1.2.1 pt hp).1
  obtain ⟨u,v,he⟩ : ∃ u v : Nat, extra=[u,v] := by
    cases extra with
    | nil => simp at short
    | cons u tl => cases tl with
      | nil => simp at short
      | cons v tail =>
        have ht : tail=[] := List.length_eq_zero_iff.mp (by simpa using short)
        exact ⟨u,v,by simp [ht]⟩
  subst extra
  have hu := inside u (by simp)
  have hv := inside v (by simp)
  have sums := p.sum_eq
  simp only [List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at sums
  change 6435*(2*(ks.sum : Int)-14*29) + 3432*(2*((q.map Prod.fst).sum : Int)-30*29) = 0 at linear
  have odd := both_diagonals_parity h.1 len ds dd
  omega


-- Actual integer linear factors, in the same coordinates as the moment functional.
def lineEval (d : Dir) (k : Nat) (x y : Int) : Int :=
  match d with
  | .row => x - (2*(k:Int)-29)
  | .col => y - (2*(k:Int)-29)
  | .sum => x+y - (2*(k:Int)-58)
  | .diff => x-y - (2*(k:Int)-58)

def familyEval (q : List Square) (d : Dir) (x y : Int) : Int :=
  ∏ k ∈ fullKeys q d, lineEval d k x y

def coverEval (q : List Square) (x y : Int) : Int :=
  familyEval q .row x y * familyEval q .col x y *
  familyEval q .sum x y * familyEval q .diff x y

private theorem line_zero (p : Square) (hp : onBoard 30 p) (d : Dir) :
    lineEval d (key 30 d p) (Grid30.coord p.1) (Grid30.coord p.2) = 0 := by
  unfold onBoard at hp
  cases d <;> simp [lineEval,key,Grid30.coord] <;> omega

theorem cover_vanishes {q : List Square} (hg : Good 30 q)
    (noIsolated : ∀ p ∈ q, SaturatedAt 30 q p) (i j : Fin 30) :
    coverEval q (Grid30.coord i) (Grid30.coord j) = 0 := by
  let p : Square := (i.val,j.val)
  have hb : onBoard 30 p := ⟨i.isLt,j.isLt⟩
  obtain ⟨d,hd⟩ := coverage_without_isolated hg noIsolated p hb
  have mem : key 30 d p ∈ fullKeys q d := by
    apply Finset.mem_filter.mpr
    refine ⟨List.mem_toFinset.mpr ?_,hd⟩
    exact List.count_pos_iff.mp (by change 0 < occupancy 30 q d (key 30 d p); omega)
  have zero : familyEval q d (Grid30.coord i) (Grid30.coord j) = 0 :=
    by
      unfold familyEval
      exact Finset.prod_eq_zero (f := fun k => lineEval d k (Grid30.coord i) (Grid30.coord j)) mem (line_zero p hb d)
  cases d <;> simp [coverEval,zero]

#print axioms cover_vanishes
#print axioms deficient_row_impossible
#print axioms coverage_without_isolated
#print axioms complete_pairs
#print axioms both_diagonals_centered_nonzero
end Gardner.Bridge
