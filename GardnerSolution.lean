import GardnerData
namespace Gardner

theorem diff_key_iff {n : Nat} {p s : Square} (hp : onBoard n p) (hs : onBoard n s) :
    key n .diff p = key n .diff s ↔ p.1 + s.2 = s.1 + p.2 := by
  simp only [key]; unfold onBoard at *; omega

private theorem occ_cons (n : Nat) (p : Square) (q : List Square) (d : Dir) (k : Nat) :
    occupancy n (p :: q) d k = occupancy n q d k + (if key n d p = k then 1 else 0) := by
  simp [occupancy, List.count_cons, beq_iff_eq]

private theorem occ_cap {n : Nat} {q : List Square} (hv : Valid n q) (d : Dir) (k : Nat) :
    occupancy n q d k ≤ 2 := by
  by_cases h : k ∈ q.map (key n d)
  · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact hv.2.2 s hs d
  · simp [occupancy, List.count_eq_zero_of_not_mem h]

theorem add_fails_iff {n : Nat} {q : List Square} {p : Square}
    (hq : Valid n q) (hp : onBoard n p) (he : p ∉ q) :
    ¬ Valid n (p :: q) ↔ SaturatedAt n q p := by
  classical
  constructor
  · intro hf
    apply Classical.byContradiction
    intro h
    apply hf
    refine ⟨List.nodup_cons.mpr ⟨he,hq.1⟩, ?_, ?_⟩
    · intro s hs; rcases List.mem_cons.mp hs with rfl | hmem
      · exact hp
      · exact hq.2.1 _ hmem
    · intro s _ d; rw [occ_cons]
      split <;> rename_i hk
      · have hc := occ_cap hq d (key n d s)
        have hn : occupancy n q d (key n d s) ≠ 2 := fun e => h ⟨d, hk ▸ e⟩
        omega
      · simpa using occ_cap hq d (key n d s)
  · rintro ⟨d,hd⟩ ha
    have h := ha.2.2 p (by simp) d
    simp [occ_cons, hd] at h


-- A certificate lists some saturated lines. The independent conditions below
-- check each line against q and every board square against that list or q.
private def Listed (n : Nat) (ls : List (Dir × Nat)) (p : Square) : Prop :=
  ∃ l ∈ ls, key n l.1 p = l.2

private instance (n : Nat) (ls : List (Dir × Nat)) (p : Square) :
    Decidable (Listed n ls p) := by unfold Listed; infer_instance

private theorem good_of_lines {n : Nat} {q : List Square} {ls : List (Dir × Nat)}
    (hv : Valid n q) (hl : ∀ l ∈ ls, occupancy n q l.1 l.2 = 2)
    (hb : ∀ r c : Fin n, Listed n ls (r.val,c.val) ∨ (r.val,c.val) ∈ q) : Good n q := by
  refine ⟨hv, ?_⟩
  intro p hp he
  obtain ⟨l, hmem, hk⟩ := (hb ⟨p.1,hp.1⟩ ⟨p.2,hp.2⟩).resolve_right he
  apply (add_fails_iff hv hp he).mpr
  exact ⟨l.1, hk ▸ hl l hmem⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem upper31 : ∃ q : List Square, q.length = 31 ∧ Good 30 q := by
  refine ⟨witness, rfl, ?_⟩
  apply good_of_lines (ls := witnessLines) <;> decide

end Gardner
