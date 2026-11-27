import Gardner.kernel.PairedAxes
import Mathlib.Data.List.Nodup

namespace Gardner

def reflectCol (p : Square) : Square := (p.1,29-p.2)

def reflectedDir : Dir → Dir
  | .row => .row
  | .col => .col
  | .diff => .sum
  | .sum => .diff

theorem reflectCol_twice (p : Square) (hp : onBoard 30 p) :
    reflectCol (reflectCol p) = p := by
  unfold onBoard at hp
  apply Prod.ext
  · rfl
  · simp only [reflectCol]; omega

private theorem reflected_key_eq (p t : Square) (hp : onBoard 30 p)
    (ht : onBoard 30 t) (d : Dir) :
    key 30 d (reflectCol p) = key 30 d (reflectCol t) ↔
      key 30 (reflectedDir d) p = key 30 (reflectedDir d) t := by
  unfold onBoard at hp ht
  cases d <;> simp only [key,reflectCol,reflectedDir] <;> omega

theorem reflected_occupancy (q : List Square) (ho : ∀ t ∈ q, onBoard 30 t)
    (p : Square) (hp : onBoard 30 p) (d : Dir) :
    occupancy 30 (q.map reflectCol) d (key 30 d (reflectCol p)) =
      occupancy 30 q (reflectedDir d) (key 30 (reflectedDir d) p) := by
  induction q with
  | nil => rfl
  | cons t q ih =>
    have ht := ho t (by simp)
    have hq := ih (fun a ha => ho a (by simp [ha]))
    simp only [occupancy,List.map_cons,List.count_cons] at hq ⊢
    rw [hq]
    simp only [beq_iff_eq,reflected_key_eq t p ht hp d]

theorem reflectCol_valid {q : List Square} (hv : Valid 30 q) :
    Valid 30 (q.map reflectCol) := by
  refine ⟨?_,?_,?_⟩
  · apply List.Nodup.map_on _ hv.1
    intro p hp t ht eq
    have pboard := hv.2.1 p hp
    have tboard := hv.2.1 t ht
    have back := congrArg reflectCol eq
    rwa [reflectCol_twice p pboard,reflectCol_twice t tboard] at back
  · intro p hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
    have board := hv.2.1 t ht
    exact ⟨board.1,by simp only [reflectCol]; omega⟩
  · intro p hp d
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
    rw [reflected_occupancy q hv.2.1 t (hv.2.1 t ht) d]
    exact hv.2.2 t ht (reflectedDir d)

theorem reflectCol_good {q : List Square} (hg : Good 30 q) :
    Good 30 (q.map reflectCol) := by
  refine ⟨reflectCol_valid hg.1,?_⟩
  intro p hp hn hv
  have ho : onBoard 30 (reflectCol p) := ⟨hp.1,by simp only [reflectCol]; omega⟩
  have vacant : reflectCol p ∉ q := by
    intro h
    exact hn (List.mem_map.mpr ⟨reflectCol p,h,reflectCol_twice p hp⟩)
  have back : (q.map reflectCol).map reflectCol = q := by
    rw [List.map_map]
    calc
      _ = q.map id := List.map_congr_left (fun t ht => reflectCol_twice t (hg.1.2.1 t ht))
      _ = q := List.map_id q
  have original := reflectCol_valid hv
  rw [List.map_cons,back] at original
  exact hg.2 (reflectCol p) ho vacant original

namespace Bridge

theorem reflected_diff_keys (q : List Square) (ho : ∀ p ∈ q, onBoard 30 p) :
    (q.map reflectCol).map (key 30 .diff) = q.map (key 30 .sum) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro p hp
  have h := ho p hp
  unfold onBoard at h
  simp only [Function.comp_def,key,reflectCol]
  omega

theorem reflected_sum_keys (q : List Square) :
    (q.map reflectCol).map (key 30 .sum) = q.map (key 30 .diff) := by
  rw [List.map_map]
  rfl

theorem reflectCol_full_diff (q : List Square) (ho : ∀ p ∈ q, onBoard 30 p) :
    fullKeys (q.map reflectCol) .diff = fullKeys q .sum := by
  simp only [fullKeys,occupancy,reflected_diff_keys q ho]
  rfl

theorem reflectCol_full_sum (q : List Square) :
    fullKeys (q.map reflectCol) .sum = fullKeys q .diff := by
  simp only [fullKeys,occupancy,reflected_sum_keys]
  rfl

/-- Choosing an orientation is a proved board bijection, not an invariance
condition on the placement. -/
theorem orient_complete_difference {q : List Square} (hg : Good 30 q) (len : q.length=30) :
    ∃ t : List Square, Good 30 t ∧ t.length=30 ∧ (fullKeys t .diff).card=15 := by
  rcases (saturation30 hg len).2.2.1 with d | s
  · exact ⟨q,hg,len,d⟩
  · refine ⟨q.map reflectCol,reflectCol_good hg,by simpa using len,?_⟩
    rw [reflectCol_full_diff q hg.1.2.1]
    exact s

#print axioms orient_complete_difference
end Bridge
end Gardner
