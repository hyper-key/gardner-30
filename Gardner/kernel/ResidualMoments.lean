import Gardner.kernel.MomentCuts
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.List.Sort

namespace Gardner.Kernel.MomentCuts

private theorem required_subperm (values required : List Int) (nd : required.Nodup)
    (full : ∀ k ∈ required, values.count k = 2) :
    (required++required).Subperm values := by
  apply List.subperm_iff_count.mpr
  intro k
  simp only [List.count_append]
  have count := nd.count (a:=k)
  rw [count]
  by_cases h : k ∈ required
  · simp [h,full k h]
  · simp [h]

theorem remove_required (values required : List Int) (nd : required.Nodup)
    (full : ∀ k ∈ required, values.count k = 2) :
    ∃ rest, values.Perm ((required++required)++rest) ∧
      rest.length = values.length-2*required.length ∧
      rest.sum = values.sum-2*required.sum ∧
      squareSum rest = squareSum values-2*squareSum required ∧
      ∀ k ∈ rest, k ∈ values ∧ k ∉ required := by
  obtain ⟨l,perm,sl⟩ := List.subperm_iff.mp (required_subperm values required nd full)
  obtain ⟨rest,append⟩ := sl.exists_perm_append
  have p := perm.symm.trans append
  have length := p.length_eq
  have first := p.sum_eq
  have second := (p.map (fun k => k^2)).sum_eq
  simp only [List.length_append] at length
  simp only [List.sum_append] at first
  simp only [List.map_append,List.sum_append] at second
  refine ⟨rest,p,by omega,by omega,?_,?_⟩
  · unfold squareSum; omega
  · intro k hk
    refine ⟨p.mem_iff.mpr (List.mem_append_right _ hk),?_⟩
    intro member
    have count := p.count_eq k
    have one := nd.count (a:=k)
    simp only [List.count_append] at count
    rw [one,ite_eq_left member,full k member] at count
    have positive := List.count_pos_iff.mpr hk
    omega

def allowedKeys (domain required : List Int) : List Int :=
  ((domain.eraseDups).filter (fun k => decide (k ∉ required))).insertionSort (· ≤ ·)

theorem mem_allowedKeys (domain required : List Int) (k : Int) :
    k ∈ allowedKeys domain required ↔ k ∈ domain ∧ k ∉ required := by
  simp [allowedKeys]

def residualProblem (domainD domainS requiredD requiredS : List Int)
    (firstD firstS totalSquares : Int) : Problem where
  dkeys := allowedKeys domainD requiredD
  skeys := allowedKeys domainS requiredS
  dleft := 30-2*requiredD.length
  sleft := 30-2*requiredS.length
  dsum := firstD-2*requiredD.sum
  ssum := firstS-2*requiredS.sum
  squares := totalSquares-2*squareSum requiredD-2*squareSum requiredS

/-- Removing two occurrences of every required saturated key produces a model
of the relaxed arithmetic problem. Extra saturated keys remain permitted. -/
theorem residual_realizes (domainD domainS requiredD requiredS ds ss : List Int)
    (firstD firstS totalSquares : Int)
    (nd : requiredD.Nodup) (ns : requiredS.Nodup)
    (fullD : ∀ k ∈ requiredD, ds.count k = 2)
    (fullS : ∀ k ∈ requiredS, ss.count k = 2)
    (d_domain : ∀ k ∈ ds, k ∈ domainD) (s_domain : ∀ k ∈ ss, k ∈ domainS)
    (d_len : ds.length = 30) (s_len : ss.length = 30)
    (d_first : ds.sum = firstD) (s_first : ss.sum = firstS)
    (second : squareSum ds+squareSum ss = totalSquares) :
    ∃ rd rs, Realizes (residualProblem domainD domainS requiredD requiredS
      firstD firstS totalSquares) rd rs := by
  obtain ⟨rd,_,rd_len,rd_first,rd_second,rd_mem⟩ := remove_required ds requiredD nd fullD
  obtain ⟨rs,_,rs_len,rs_first,rs_second,rs_mem⟩ := remove_required ss requiredS ns fullS
  refine ⟨rd,rs,?_,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    exact (mem_allowedKeys domainD requiredD k).mpr
      ⟨d_domain k (rd_mem k hk).1,(rd_mem k hk).2⟩
  · intro k hk
    exact (mem_allowedKeys domainS requiredS k).mpr
      ⟨s_domain k (rs_mem k hk).1,(rs_mem k hk).2⟩
  · simpa only [residualProblem,d_len] using rd_len
  · simpa only [residualProblem,s_len] using rs_len
  · simpa only [residualProblem,d_first] using rd_first
  · simpa only [residualProblem,s_first] using rs_first
  · simp only [residualProblem]; omega

#print axioms remove_required
#print axioms residual_realizes
end Gardner.Kernel.MomentCuts
