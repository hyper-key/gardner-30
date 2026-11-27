import GardnerSolution
import Mathlib.Data.List.Defs
import Mathlib.Data.Prod.Basic

namespace Gardner

def transposeDir : Dir → Dir
  | .row => .col
  | .col => .row
  | .sum => .sum
  | .diff => .diff

private theorem transpose_key_eq (p t : Square) (hp : onBoard 30 p)
    (ht : onBoard 30 t) (d : Dir) :
    key 30 d p.swap = key 30 d t.swap ↔
      key 30 (transposeDir d) p = key 30 (transposeDir d) t := by
  unfold onBoard at hp ht
  cases d <;> simp only [key,transposeDir,Prod.fst_swap,Prod.snd_swap] <;> omega

theorem transpose_occupancy (q : List Square) (ho : ∀ t ∈ q, onBoard 30 t)
    (p : Square) (hp : onBoard 30 p) (d : Dir) :
    occupancy 30 (q.map Prod.swap) d (key 30 d p.swap) =
      occupancy 30 q (transposeDir d) (key 30 (transposeDir d) p) := by
  induction q with
  | nil => rfl
  | cons t q ih =>
    have ht := ho t (by simp)
    have hq := ih (fun a ha => ho a (by simp [ha]))
    simp only [occupancy,List.map_cons,List.count_cons] at hq ⊢
    rw [hq]
    have he := transpose_key_eq t p ht hp d
    simp only [beq_iff_eq, he]

theorem transpose_valid {q : List Square} (hv : Valid 30 q) :
    Valid 30 (q.map Prod.swap) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hv.1.map Prod.swap (fun _ _ h he => h (Prod.swap_inj.mp he))
  · intro p hp
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
    exact ⟨(hv.2.1 t ht).2,(hv.2.1 t ht).1⟩
  · intro p hp d
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hp
    rw [transpose_occupancy q hv.2.1 t (hv.2.1 t ht) d]
    exact hv.2.2 t ht (transposeDir d)

theorem transpose_good {q : List Square} (hg : Good 30 q) :
    Good 30 (q.map Prod.swap) := by
  refine ⟨transpose_valid hg.1, ?_⟩
  intro p hp hn hvalid
  have ho : onBoard 30 p.swap := ⟨hp.2,hp.1⟩
  have vacant : p.swap ∉ q := by
    intro h
    exact hn (List.mem_map.mpr ⟨p.swap,h,by simp⟩)
  have hv := transpose_valid hvalid
  simp only [List.map_cons,List.map_map,Function.comp_def,Prod.swap_swap,List.map_id'] at hv
  exact hg.2 p.swap ho vacant hv

#print axioms transpose_good
end Gardner
