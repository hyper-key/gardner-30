import GardnerSolution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Max

namespace Gardner.Perimeter
open Finset

def edge (lr hr lc hc : Nat) (p : Square) : Prop :=
  (lr ≤ p.1 ∧ p.1 ≤ hr ∧ lc ≤ p.2 ∧ p.2 ≤ hc) ∧
  (p.1 = lr ∨ p.1 = hr ∨ p.2 = lc ∨ p.2 = hc)

private def firstSide (d : Dir) (lr lc hc : Nat) (p : Square) : Bool :=
  decide (p.1 = lr ∨ p.2 = (match d with | .sum => hc | _ => lc))

theorem diagonal_frame_bound (F : Finset Square) (lr hr lc hc : Nat)
    (hb : ∀ p ∈ F, edge lr hr lc hc p)
    (ho : ∀ p ∈ F, onBoard 30 p) (d : Dir) (hd : d = .sum ∨ d = .diff) (k : Nat) :
    (F.filter (fun p => key 30 d p = k)).card ≤ 2 := by
  classical
  let part := firstSide d lr lc hc
  have h := Finset.card_le_card_of_injOn (s := F.filter (fun p => key 30 d p=k))
    (t := (Finset.univ : Finset Bool)) part (fun _ _ => Finset.mem_univ _) (by
      intro a hA b hB he
      obtain ⟨ham,hak⟩ := Finset.mem_filter.mp hA
      obtain ⟨hbm,hbk⟩ := Finset.mem_filter.mp hB
      obtain ⟨ba,fa⟩ := hb a ham
      obtain ⟨bb,fb⟩ := hb b hbm
      have oa := ho a ham
      have ob := ho b hbm
      rcases hd with rfl | rfl <;>
        simp only [part,firstSide, key,decide_eq_decide] at he hak hbk <;>
        unfold onBoard at oa ob <;> apply Prod.ext <;> omega)
  rwa [show (Finset.univ : Finset Bool).card = 2 by decide] at h

private theorem fiber_occ {q : List Square} (hq : q.Nodup) (d : Dir) (k : Nat) :
    (q.toFinset.filter (fun p => key 30 d p = k)).card = occupancy 30 q d k := by
  induction q with
  | nil => simp [occupancy]
  | cons p q ih =>
    have ⟨hn,ht⟩ := List.nodup_cons.mp hq
    by_cases h : key 30 d p = k
    · simp [Finset.filter_insert, h, hn, ih ht,occupancy]
    · simp [Finset.filter_insert, h, ih ht,occupancy]

private def full (q : List Square) (d : Dir) : Finset Nat :=
  (q.map (key 30 d)).toFinset.filter (fun k => occupancy 30 q d k = 2)
private theorem mem_full {q : List Square} {d : Dir} {k : Nat} :
    k ∈ full q d ↔ occupancy 30 q d k = 2 := by
  simp only [full, Finset.mem_filter, List.mem_toFinset]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    by_contra nh
    have z := List.count_eq_zero_of_not_mem nh
    unfold occupancy at h
    omega

private theorem full_card_in {q : List Square} (hq : q.Nodup) (d : Dir) :
    (q.toFinset.filter (fun p => key 30 d p ∈ full q d)).card = (full q d).card*2 := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ = ∑ _k ∈ full q d, 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [fiber_occ hq, mem_full.mp hk]
    _ = _ := by simp

private theorem full_le {q : List Square} (hq : q.Nodup) (d : Dir) :
    (full q d).card*2 ≤ q.length := by
  rw [← full_card_in hq]
  simpa [List.toFinset_card_of_nodup hq] using
    (Finset.card_le_card (Finset.filter_subset (fun p => key 30 d p ∈ full q d) q.toFinset))


private theorem extremes {s : Finset Nat} (h : 2 ≤ s.card) :
    ∃ lo hi, lo ∈ s ∧ hi ∈ s ∧ lo ≠ hi ∧ ∀ x ∈ s, lo ≤ x ∧ x ≤ hi := by
  have hn := Finset.card_pos.mp (by omega : 0 < s.card)
  let lo := s.min' hn
  let hi := s.max' hn
  have bounds : ∀ x ∈ s, lo ≤ x ∧ x ≤ hi := fun x hx => ⟨s.min'_le _ hx,s.le_max' _ hx⟩
  refine ⟨lo, hi, s.min'_mem _, s.max'_mem _, ?_, bounds⟩
  intro he
  have sub : s ⊆ {lo} := by
    intro x hx
    have := bounds x hx
    simpa using (by omega : x=lo)
  have hc := Finset.card_le_card sub
  simp only [Finset.card_singleton] at hc
  omega

private theorem frame_exists {R C : Finset Nat} (hr : 2 ≤ R.card) (hc : 2 ≤ C.card) :
    ∃ (F : Finset Square) (lr ur lc uc : Nat),
      F.card+4 = 2*R.card+2*C.card ∧
      ∀ p ∈ F, p.1 ∈ R ∧ p.2 ∈ C ∧ edge lr ur lc uc p := by
  obtain ⟨lr,ur,hlr,hur,hnr,br⟩ := extremes hr
  obtain ⟨lc,uc,hlc,huc,hnc,bc⟩ := extremes hc
  let ER : Finset Nat := {lr,ur}
  let EC : Finset Nat := {lc,uc}
  let F := (ER ×ˢ C) ∪ ((R \ ER) ×ˢ EC)
  have sr : ER ⊆ R := by
    intro x hx; simp [ER] at hx; rcases hx with rfl | rfl <;> assumption
  have sc : EC ⊆ C := by
    intro x hx; simp [EC] at hx; rcases hx with rfl | rfl <;> assumption
  have dr : ER.card = 2 := by simp [ER,hnr]
  have dc : EC.card = 2 := by simp [EC,hnc]
  have dj : Disjoint (ER ×ˢ C) ((R \ ER) ×ˢ EC) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    exact (Finset.mem_sdiff.mp (Finset.mem_product.mp hq).1).2 (Finset.mem_product.mp hp).1
  refine ⟨F,lr,ur,lc,uc,?_,?_⟩
  · dsimp only [F]
    rw [Finset.card_union_of_disjoint dj, Finset.card_product, Finset.card_product,
        Finset.card_sdiff_of_subset sr,dr,dc]; omega
  · intro p hp
    have hp' : p.1 ∈ R ∧ p.2 ∈ C ∧ (p.1 ∈ ER ∨ p.2 ∈ EC) := by
      rcases Finset.mem_union.mp hp with h | h
      · have h := Finset.mem_product.mp h
        exact ⟨sr h.1,h.2,.inl h.1⟩
      · have h := Finset.mem_product.mp h
        exact ⟨(Finset.mem_sdiff.mp h.1).1,sc h.2,.inr h.2⟩
    obtain ⟨ar,ac,e⟩ := hp'
    have hrng := br _ ar
    have hcng := bc _ ac
    refine ⟨ar,ac,⟨⟨hrng.1,hrng.2,hcng⟩,?_⟩⟩
    simpa [ER,EC,or_assoc] using e


private theorem axes_in_range {q : List Square} (hg : Good 30 q)
    (d : Dir) (hd : d=.row ∨ d=.col) : full q d ⊆ Finset.range 30 := by
  intro k hk
  have hm := Finset.mem_filter.mp hk
  obtain ⟨p, hp, e⟩ := List.mem_map.mp (List.mem_toFinset.mp hm.1)
  have ho := hg.1.2.1 p hp
  apply Finset.mem_range.mpr
  rcases hd with rfl | rfl <;> simp [key] at e <;> unfold onBoard at ho <;> omega

private def covered (q : List Square) (d : Dir) (F : Finset Square) : Finset Square :=
  F.filter (fun p => key 30 d p ∈ full q d)

private theorem covered_card {q : List Square} {d : Dir} {F : Finset Square}
    (hl : ∀ k, (F.filter (fun p => key 30 d p=k)).card ≤ 2) :
    (covered q d F).card ≤ (full q d).card*2 := by
  unfold covered
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ _k ∈ full q d, 2 := Finset.sum_le_sum (fun i _ => hl i)
    _ = _ := by simp

private theorem exception_bound {q : List Square} (h : q.Nodup) {F : Finset Square} {d : Dir}
    (hn : ∀ p ∈ F, key 30 d p ∉ full q d) :
    (F ∩ q.toFinset).card + (full q d).card*2 ≤ q.length := by
  let outside := q.toFinset \ q.toFinset.filter (fun p => key 30 d p ∈ full q d)
  have sub : F ∩ q.toFinset ⊆ outside := by
    intro p hp
    have ⟨hf,hq⟩ := Finset.mem_inter.mp hp
    exact Finset.mem_sdiff.mpr ⟨hq, fun e => hn p hf (Finset.mem_filter.mp e).2⟩
  have hc := Finset.card_le_card sub
  have hu := full_le h d
  have he : outside.card = q.length - (full q d).card*2 := by
    unfold outside
    rw [Finset.card_sdiff_of_subset (Finset.filter_subset _ _),full_card_in h,
      List.toFinset_card_of_nodup h]
  omega

theorem lower30 (q : List Square) (hg : Good 30 q) : 30 ≤ q.length := by
  classical
  by_contra hn
  have hrow := full_le hg.1.1 .row
  have hcol := full_le hg.1.1 .col
  have hsum := full_le hg.1.1 .sum
  have hdif := full_le hg.1.1 .diff
  let R := Finset.range 30 \ full q .row
  let C := Finset.range 30 \ full q .col
  have hr : R.card = 30 - (full q .row).card := by
    simp [R,Finset.card_sdiff_of_subset (axes_in_range hg .row (.inl rfl))]
  have hc : C.card = 30 - (full q .col).card := by
    simp [C,Finset.card_sdiff_of_subset (axes_in_range hg .col (.inr rfl))]
  obtain ⟨F,lr,ur,lc,uc,hcard,geom⟩ := frame_exists (R:=R) (C:=C) (by omega) (by omega)
  have oh (p) (hp : p ∈ F) : onBoard 30 p :=
    ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp (geom p hp).1).1,
     Finset.mem_range.mp (Finset.mem_sdiff.mp (geom p hp).2.1).1⟩
  have noRow (p) (hp : p ∈ F) : key 30 .row p ∉ full q .row :=
    (Finset.mem_sdiff.mp (geom p hp).1).2
  have noCol (p) (hp : p ∈ F) : key 30 .col p ∉ full q .col :=
    (Finset.mem_sdiff.mp (geom p hp).2.1).2
  have hcov : F ⊆ (F ∩ q.toFinset) ∪ covered q .sum F ∪ covered q .diff F := by
    intro p hp
    by_cases e : p ∈ q
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp,List.mem_toFinset.mpr e⟩))
    obtain ⟨d,hd⟩ := (add_fails_iff hg.1 (oh p hp) e).mp (hg.2 p (oh p hp) e)
    have h := mem_full.mpr hd
    cases d with
    | row => exact (noRow p hp h).elim
    | col => exact (noCol p hp h).elim
    | sum => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩))
    | diff => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩)
  have sub := Finset.card_le_card hcov
  have u₁ := Finset.card_union_le (F ∩ q.toFinset) (covered q .sum F)
  have u₂ := Finset.card_union_le ((F ∩ q.toFinset) ∪ covered q .sum F) (covered q .diff F)
  have fiber := diagonal_frame_bound F lr ur lc uc (fun p hp => (geom p hp).2.2) oh
  have ds := covered_card (q:=q) (fiber .sum (.inl rfl))
  have dd := covered_card (q:=q) (fiber .diff (.inr rfl))
  have er := exception_bound hg.1.1 noRow
  have ec := exception_bound hg.1.1 noCol
  omega


/-- At cardinality 30 some family is completely paired.  The frame argument
also rules out the possibility that every family has at most fourteen pairs. -/
theorem complete_family30 (q : List Square) (hg : Good 30 q) (len : q.length = 30) :
    ∃ d : Dir, (full q d).card = 15 := by
  classical
  by_contra hn
  have incomplete (d : Dir) : (full q d).card ≤ 14 := by
    have h := full_le hg.1.1 d
    have ne : (full q d).card ≠ 15 := fun e => hn ⟨d,e⟩
    omega
  have ir := incomplete .row
  have ic := incomplete .col
  have is := incomplete .sum
  have id := incomplete .diff
  have hrow := full_le hg.1.1 .row
  have hcol := full_le hg.1.1 .col
  have hsum := full_le hg.1.1 .sum
  have hdif := full_le hg.1.1 .diff
  let R := Finset.range 30 \ full q .row
  let C := Finset.range 30 \ full q .col
  have hr : R.card = 30 - (full q .row).card := by
    simp [R,Finset.card_sdiff_of_subset (axes_in_range hg .row (.inl rfl))]
  have hc : C.card = 30 - (full q .col).card := by
    simp [C,Finset.card_sdiff_of_subset (axes_in_range hg .col (.inr rfl))]
  obtain ⟨F,lr,ur,lc,uc,hcard,geom⟩ := frame_exists (R:=R) (C:=C) (by omega) (by omega)
  have oh (p) (hp : p ∈ F) : onBoard 30 p :=
    ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp (geom p hp).1).1,
     Finset.mem_range.mp (Finset.mem_sdiff.mp (geom p hp).2.1).1⟩
  have noRow (p) (hp : p ∈ F) : key 30 .row p ∉ full q .row :=
    (Finset.mem_sdiff.mp (geom p hp).1).2
  have noCol (p) (hp : p ∈ F) : key 30 .col p ∉ full q .col :=
    (Finset.mem_sdiff.mp (geom p hp).2.1).2
  have hcov : F ⊆ (F ∩ q.toFinset) ∪ covered q .sum F ∪ covered q .diff F := by
    intro p hp
    by_cases e : p ∈ q
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hp,List.mem_toFinset.mpr e⟩))
    obtain ⟨d,hd⟩ := (add_fails_iff hg.1 (oh p hp) e).mp (hg.2 p (oh p hp) e)
    have h := mem_full.mpr hd
    cases d with
    | row => exact (noRow p hp h).elim
    | col => exact (noCol p hp h).elim
    | sum => exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩))
    | diff => exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩)
  have sub := Finset.card_le_card hcov
  have u₁ := Finset.card_union_le (F ∩ q.toFinset) (covered q .sum F)
  have u₂ := Finset.card_union_le ((F ∩ q.toFinset) ∪ covered q .sum F) (covered q .diff F)
  have fiber := diagonal_frame_bound F lr ur lc uc (fun p hp => (geom p hp).2.2) oh
  have ds := covered_card (q:=q) (fiber .sum (.inl rfl))
  have dd := covered_card (q:=q) (fiber .diff (.inr rfl))
  have er := exception_bound hg.1.1 noRow
  have ec := exception_bound hg.1.1 noCol
  omega


/-- Public geometric interface for subsequent equality-case reductions. -/
theorem axis_extremes {s : Finset Nat} (h : 2 ≤ s.card) :
    ∃ lo hi, lo ∈ s ∧ hi ∈ s ∧ lo ≠ hi ∧ ∀ x ∈ s, lo ≤ x ∧ x ≤ hi :=
  extremes h

theorem frame_of_axes {R C : Finset Nat} (hr : 2 ≤ R.card) (hc : 2 ≤ C.card) :
    ∃ (F : Finset Square) (lr ur lc uc : Nat),
      F.card+4 = 2*R.card+2*C.card ∧
      ∀ p ∈ F, p.1 ∈ R ∧ p.2 ∈ C ∧ edge lr ur lc uc p :=
  frame_exists hr hc

#print axioms lower30
end Gardner.Perimeter
