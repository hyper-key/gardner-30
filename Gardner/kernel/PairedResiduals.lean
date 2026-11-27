import Gardner.kernel.ResidualMoments
import Gardner.exact.Marginal

namespace Gardner.Kernel.MomentCuts

def differenceDomain (rows cols : List Int) : List Int :=
  rows.flatMap (fun r => cols.map (fun c => r-c))

def sumDomain (rows cols : List Int) : List Int :=
  rows.flatMap (fun r => cols.map (fun c => r+c))

def pairedProblem (rows cols requiredD requiredS : List Int) : Problem :=
  residualProblem (differenceDomain rows cols) (sumDomain rows cols) requiredD requiredS
    (2*(rows.sum-cols.sum)) (2*(rows.sum+cols.sum))
    (4*(squareSum rows+squareSum cols))

private theorem projection_domain (f : Int → Int → Int) (q : List (Int × Int))
    (rows cols : List Int) (hr : (q.map Prod.fst).Perm (rows++rows))
    (hc : (q.map Prod.snd).Perm (cols++cols)) :
    ∀ k ∈ q.map (fun p => f p.1 p.2),
      k ∈ rows.flatMap (fun r => cols.map (fun c => f r c)) := by
  intro k hk
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hk
  have rmem : p.1 ∈ rows := by
    have h := hr.mem_iff.mp (List.mem_map.mpr ⟨p,hp,rfl⟩)
    simpa only [List.mem_append,or_self] using h
  have cmem : p.2 ∈ cols := by
    have h := hc.mem_iff.mp (List.mem_map.mpr ⟨p,hp,rfl⟩)
    simpa only [List.mem_append,or_self] using h
  exact List.mem_flatMap.mpr ⟨p.1,rmem,List.mem_map.mpr ⟨p.2,cmem,rfl⟩⟩

/-- This connects the concrete residual arithmetic checker to genuine queen
coordinates with two occurrences of each active row and column. -/
theorem paired_residual_realizes (q : List (Int × Int)) (rows cols requiredD requiredS : List Int)
    (rows_length : rows.length = 15)
    (hr : (q.map Prod.fst).Perm (rows++rows))
    (hc : (q.map Prod.snd).Perm (cols++cols))
    (nd : requiredD.Nodup) (ns : requiredS.Nodup)
    (fullD : ∀ k ∈ requiredD, (Marginal.differences q).count k = 2)
    (fullS : ∀ k ∈ requiredS, (Marginal.sums q).count k = 2) :
    ∃ ds ss, Realizes (pairedProblem rows cols requiredD requiredS) ds ss := by
  have length : q.length = 30 := by
    have h := hr.length_eq
    simp only [List.length_map,List.length_append,rows_length] at h
    omega
  have moments := Marginal.paired_moments q rows cols hr hc
  apply residual_realizes (differenceDomain rows cols) (sumDomain rows cols)
    requiredD requiredS (Marginal.differences q) (Marginal.sums q)
    (2*(rows.sum-cols.sum)) (2*(rows.sum+cols.sum))
    (4*(squareSum rows+squareSum cols)) nd ns fullD fullS
  · exact projection_domain (fun r c => r-c) q rows cols hr hc
  · exact projection_domain (fun r c => r+c) q rows cols hr hc
  · simpa only [Marginal.differences,List.length_map] using length
  · simpa only [Marginal.sums,List.length_map] using length
  · exact moments.1
  · exact moments.2.1
  · exact moments.2.2

#print axioms paired_residual_realizes
end Gardner.Kernel.MomentCuts
