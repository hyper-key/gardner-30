import Gardner.kernel.PairedAxes

namespace Gardner.Kernel
open Finset Bridge

/-- A necessary cover of the unused axis product by ordinary diagonal keys. -/
structure DiagonalCover where
  rows : Finset Nat
  cols : Finset Nat
  differences : Finset Nat
  sums : Finset Nat
  row_card : rows.card = 15
  col_card : cols.card = 15
  rows_in : rows ⊆ Finset.range 30
  cols_in : cols ⊆ Finset.range 30
  diff_le : differences.card ≤ 15
  sum_le : sums.card ≤ 15
  complete : differences.card = 15 ∨ sums.card = 15
  covers : ∀ r ∈ rows, ∀ c ∈ cols,
    key 30 .diff (r,c) ∈ differences ∨ key 30 .sum (r,c) ∈ sums

private theorem full_axis_in {q : List Square} (hg : Good 30 q) (d : Dir)
    (hd : d = .row ∨ d = .col) : fullKeys q d ⊆ Finset.range 30 := by
  intro k hk
  obtain ⟨p,hp,eq⟩ := List.mem_map.mp
    (List.mem_toFinset.mp (Finset.mem_filter.mp hk).1)
  have ho := hg.1.2.1 p hp
  apply Finset.mem_range.mpr
  rcases hd with rfl | rfl <;> simp only [key] at eq <;>
    unfold onBoard at ho <;> omega

noncomputable def coverOfGood {q : List Square} (hg : Good 30 q) (len : q.length = 30) :
    DiagonalCover where
  rows := Finset.range 30 \ fullKeys q .row
  cols := Finset.range 30 \ fullKeys q .col
  differences := fullKeys q .diff
  sums := fullKeys q .sum
  row_card := by
    rw [Finset.card_sdiff_of_subset (full_axis_in hg .row (.inl rfl))]
    simp [paired_rows30 hg len]
  col_card := by
    rw [Finset.card_sdiff_of_subset (full_axis_in hg .col (.inr rfl))]
    simp [paired_columns30 hg len]
  rows_in := Finset.sdiff_subset
  cols_in := Finset.sdiff_subset
  diff_le := full_count_le_15 len .diff
  sum_le := full_count_le_15 len .sum
  complete := (saturation30 hg len).2.2.1
  covers := by
    intro r hr c hc
    have ho : onBoard 30 (r,c) :=
      ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hr).1,
       Finset.mem_range.mp (Finset.mem_sdiff.mp hc).1⟩
    obtain ⟨d,hd⟩ := coverage_without_isolated hg (no_isolated30 hg len) (r,c) ho
    have member : key 30 d (r,c) ∈ fullKeys q d := Finset.mem_filter.mpr
      ⟨List.mem_toFinset.mpr (List.count_pos_iff.mp (by
        change 0 < occupancy 30 q d (key 30 d (r,c)); omega)),hd⟩
    cases d with
    | row => exact ((Finset.mem_sdiff.mp hr).2 member).elim
    | col => exact ((Finset.mem_sdiff.mp hc).2 member).elim
    | diff => exact .inl member
    | sum => exact .inr member

private theorem covered_card (F : Finset Square) (K : Finset Nat) (f : Square → Nat)
    (m : Nat) (fibers : ∀ k, (F.filter (fun p => f p = k)).card ≤ m) :
    (F.filter (fun p => f p ∈ K)).card ≤ K.card*m := by
  rw [← Finset.sum_card_fiberwise_eq_card_filter]
  calc
    _ ≤ ∑ k ∈ K, m := Finset.sum_le_sum (fun k _ => fibers k)
    _ = _ := by simp

private theorem target_card_le (P : DiagonalCover) (F : Finset Square) (m : Nat)
    (targets : ∀ p ∈ F, p.1 ∈ P.rows ∧ p.2 ∈ P.cols)
    (fibers : ∀ d, d = .sum ∨ d = .diff → ∀ k,
      (F.filter (fun p => key 30 d p = k)).card ≤ m) :
    F.card ≤ m*(P.differences.card+P.sums.card) := by
  let D := F.filter (fun p => key 30 .diff p ∈ P.differences)
  let S := F.filter (fun p => key 30 .sum p ∈ P.sums)
  have sub : F ⊆ D ∪ S := by
    intro p hp
    have cov := P.covers p.1 (targets p hp).1 p.2 (targets p hp).2
    rcases cov with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp,h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp,h⟩)
  have card := Finset.card_le_card sub
  have union := Finset.card_union_le D S
  have dd := covered_card F P.differences (key 30 .diff) m (fibers .diff (.inr rfl))
  have ss := covered_card F P.sums (key 30 .sum) m (fibers .sum (.inl rfl))
  change D.card ≤ _ at dd
  change S.card ≤ _ at ss
  rw [Nat.mul_add, Nat.mul_comm m P.differences.card, Nat.mul_comm m P.sums.card]
  omega

theorem at_least_28_diagonals (P : DiagonalCover) :
    28 ≤ P.differences.card + P.sums.card := by
  obtain ⟨F,lr,hr,lc,hc,size,geom⟩ := Perimeter.frame_of_axes
    (R:=P.rows) (C:=P.cols) (by rw [P.row_card]; omega) (by rw [P.col_card]; omega)
  have on (p) (hp : p ∈ F) : onBoard 30 p :=
    ⟨Finset.mem_range.mp (P.rows_in (geom p hp).1),
     Finset.mem_range.mp (P.cols_in (geom p hp).2.1)⟩
  have bound := target_card_le P F 2 (fun p hp => ⟨(geom p hp).1,(geom p hp).2.1⟩)
    (Perimeter.diagonal_frame_bound F lr hr lc hc (fun p hp => (geom p hp).2.2) on)
  rw [P.row_card,P.col_card] at size
  omega

theorem diagonal_count_cases (P : DiagonalCover) :
    (P.differences.card = 15 ∧ P.sums.card = 13) ∨
    (P.differences.card = 15 ∧ P.sums.card = 14) ∨
    (P.differences.card = 15 ∧ P.sums.card = 15) ∨
    (P.differences.card = 14 ∧ P.sums.card = 15) ∨
    (P.differences.card = 13 ∧ P.sums.card = 15) := by
  have lower := at_least_28_diagonals P
  have a := P.diff_le
  have b := P.sum_le
  have c := P.complete
  omega

theorem long_column_bound (P : DiagonalCover) (lr hr lc hc : Nat)
    (rb : ∀ r ∈ P.rows, lr ≤ r ∧ r ≤ hr)
    (lc_mem : lc ∈ P.cols) (hc_mem : hc ∈ P.cols)
    (long : hr-lr < hc-lc) : 30 ≤ P.differences.card+P.sums.card := by
  let F := P.rows ×ˢ ({lc,hc} : Finset Nat)
  have distinct : lc ≠ hc := by omega
  have size : F.card = 30 := by simp [F,P.row_card,distinct]
  have low_range := Finset.mem_range.mp (P.cols_in lc_mem)
  have high_range := Finset.mem_range.mp (P.cols_in hc_mem)
  have targets : ∀ p ∈ F, p.1 ∈ P.rows ∧ p.2 ∈ P.cols := by
    intro p hp
    obtain ⟨pr,pc⟩ := Finset.mem_product.mp hp
    have sides : p.2 = lc ∨ p.2 = hc := by simpa using pc
    exact ⟨pr,sides.elim (fun e => e ▸ lc_mem) (fun e => e ▸ hc_mem)⟩
  have fibers (d : Dir) (hd : d = .sum ∨ d = .diff) (k : Nat) :
      (F.filter (fun p => key 30 d p = k)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp t ht
    obtain ⟨pf,pk⟩ := Finset.mem_filter.mp hp
    obtain ⟨tf,tk⟩ := Finset.mem_filter.mp ht
    obtain ⟨pr,pc⟩ := Finset.mem_product.mp pf
    obtain ⟨tr,tc⟩ := Finset.mem_product.mp tf
    have pside : p.2 = lc ∨ p.2 = hc := by simpa using pc
    have tside : t.2 = lc ∨ t.2 = hc := by simpa using tc
    have pb := rb p.1 pr
    have tb := rb t.1 tr
    rcases pside with ps | ps <;> rcases tside with ts | ts <;>
      rcases hd with rfl | rfl <;> simp only [key] at pk tk <;>
      apply Prod.ext <;> omega
  have bound := target_card_le P F 1 targets fibers
  simpa only [size,Nat.one_mul] using bound

theorem long_row_bound (P : DiagonalCover) (lr hr lc hc : Nat)
    (cb : ∀ c ∈ P.cols, lc ≤ c ∧ c ≤ hc)
    (lr_mem : lr ∈ P.rows) (hr_mem : hr ∈ P.rows)
    (long : hc-lc < hr-lr) : 30 ≤ P.differences.card+P.sums.card := by
  let F := ({lr,hr} : Finset Nat) ×ˢ P.cols
  have distinct : lr ≠ hr := by omega
  have size : F.card = 30 := by simp [F,P.col_card,distinct]
  have targets : ∀ p ∈ F, p.1 ∈ P.rows ∧ p.2 ∈ P.cols := by
    intro p hp
    obtain ⟨pr,pc⟩ := Finset.mem_product.mp hp
    have sides : p.1 = lr ∨ p.1 = hr := by simpa using pr
    exact ⟨sides.elim (fun e => e ▸ lr_mem) (fun e => e ▸ hr_mem),pc⟩
  have fibers (d : Dir) (hd : d = .sum ∨ d = .diff) (k : Nat) :
      (F.filter (fun p => key 30 d p = k)).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro p hp t ht
    obtain ⟨pf,pk⟩ := Finset.mem_filter.mp hp
    obtain ⟨tf,tk⟩ := Finset.mem_filter.mp ht
    obtain ⟨pr,pc⟩ := Finset.mem_product.mp pf
    obtain ⟨tr,tc⟩ := Finset.mem_product.mp tf
    have pside : p.1 = lr ∨ p.1 = hr := by simpa using pr
    have tside : t.1 = lr ∨ t.1 = hr := by simpa using tr
    have pb := cb p.2 pc
    have tb := cb t.2 tc
    have pc_range := Finset.mem_range.mp (P.cols_in pc)
    have tc_range := Finset.mem_range.mp (P.cols_in tc)
    rcases pside with ps | ps <;> rcases tside with ts | ts <;>
      rcases hd with rfl | rfl <;> simp only [key] at pk tk <;>
      apply Prod.ext <;> omega
  have bound := target_card_le P F 1 targets fibers
  simpa only [size,Nat.one_mul] using bound

theorem equal_spans_of_fewer_than_30 (P : DiagonalCover)
    (fewer : P.differences.card+P.sums.card < 30) :
    ∃ lr hr lc hc, lr ∈ P.rows ∧ hr ∈ P.rows ∧ lc ∈ P.cols ∧ hc ∈ P.cols ∧
      (∀ r ∈ P.rows, lr ≤ r ∧ r ≤ hr) ∧
      (∀ c ∈ P.cols, lc ≤ c ∧ c ≤ hc) ∧ hr-lr = hc-lc := by
  obtain ⟨lr,hr,lr_mem,hr_mem,_,rb⟩ := Perimeter.axis_extremes
    (s:=P.rows) (by rw [P.row_card]; omega)
  obtain ⟨lc,hc,lc_mem,hc_mem,_,cb⟩ := Perimeter.axis_extremes
    (s:=P.cols) (by rw [P.col_card]; omega)
  refine ⟨lr,hr,lc,hc,lr_mem,hr_mem,lc_mem,hc_mem,rb,cb,?_⟩
  have a := long_column_bound P lr hr lc hc rb lc_mem hc_mem
  have b := long_row_bound P lr hr lc hc cb lr_mem hr_mem
  omega

#print axioms coverOfGood
#print axioms at_least_28_diagonals
#print axioms diagonal_count_cases
#print axioms equal_spans_of_fewer_than_30
end Gardner.Kernel
