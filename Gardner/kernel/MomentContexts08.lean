import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1024 : List Int := [0,1,2,3,4,5,12,17,21,24,25,26,27,28,29]
def cols1024 : List Int := [0,1,2,3,4,5,12,17,21,24,25,26,27,28,29]
def requiredD1024 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1024 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1024_eq : pairedProblem rows1024 cols1024 requiredD1024 requiredS1024 =
    MomentData.problem1024 := by rfl
theorem leaf1024 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1024++rows1024))
    (hc : (q.map Prod.snd).Perm (cols1024++cols1024))
    (hd : ∀ k ∈ requiredD1024, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1024, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1024 cols1024 requiredD1024 requiredS1024
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1024_eq] at model
  exact MomentData.excluded1024 ds ss model
def rows1025 : List Int := [0,1,2,3,4,5,14,15,21,24,25,26,27,28,29]
def cols1025 : List Int := [0,1,2,3,4,5,14,15,21,24,25,26,27,28,29]
def requiredD1025 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1025 : List Int := [19,23,24,25,26,27,28,29,30,31,32,33,34,35,39]
theorem problem1025_eq : pairedProblem rows1025 cols1025 requiredD1025 requiredS1025 =
    MomentData.problem1025 := by rfl
theorem leaf1025 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1025++rows1025))
    (hc : (q.map Prod.snd).Perm (cols1025++cols1025))
    (hd : ∀ k ∈ requiredD1025, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1025, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1025 cols1025 requiredD1025 requiredS1025
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1025_eq] at model
  exact MomentData.excluded1025 ds ss model
def rows1026 : List Int := [0,1,2,3,4,5,14,15,21,24,25,26,27,28,29]
def cols1026 : List Int := [0,1,2,3,4,5,14,15,21,24,25,26,27,28,29]
def requiredD1026 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1026 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1026_eq : pairedProblem rows1026 cols1026 requiredD1026 requiredS1026 =
    MomentData.problem1026 := by rfl
theorem leaf1026 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1026++rows1026))
    (hc : (q.map Prod.snd).Perm (cols1026++cols1026))
    (hd : ∀ k ∈ requiredD1026, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1026, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1026 cols1026 requiredD1026 requiredS1026
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1026_eq] at model
  exact MomentData.excluded1026 ds ss model
def rows1027 : List Int := [0,1,2,3,4,5,11,18,22,24,25,26,27,28,29]
def cols1027 : List Int := [0,1,2,3,4,5,11,18,22,24,25,26,27,28,29]
def requiredD1027 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1027 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1027_eq : pairedProblem rows1027 cols1027 requiredD1027 requiredS1027 =
    MomentData.problem1027 := by rfl
theorem leaf1027 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1027++rows1027))
    (hc : (q.map Prod.snd).Perm (cols1027++cols1027))
    (hd : ∀ k ∈ requiredD1027, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1027, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1027 cols1027 requiredD1027 requiredS1027
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1027_eq] at model
  exact MomentData.excluded1027 ds ss model
def rows1028 : List Int := [0,1,2,3,4,5,11,18,22,24,25,26,27,28,29]
def cols1028 : List Int := [0,1,2,3,4,6,10,17,23,24,25,26,27,28,29]
def requiredD1028 : List Int := [-9,-7,-5,-3,-2,-1,0,1,2,3,4,5,7,9,11]
def requiredS1028 : List Int := [18,20,22,24,25,26,27,28,29,30,31,32,34,36,38]
theorem problem1028_eq : pairedProblem rows1028 cols1028 requiredD1028 requiredS1028 =
    MomentData.problem1028 := by rfl
theorem leaf1028 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1028++rows1028))
    (hc : (q.map Prod.snd).Perm (cols1028++cols1028))
    (hd : ∀ k ∈ requiredD1028, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1028, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1028 cols1028 requiredD1028 requiredS1028
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1028_eq] at model
  exact MomentData.excluded1028 ds ss model
def rows1029 : List Int := [0,1,2,3,4,6,10,17,23,24,25,26,27,28,29]
def cols1029 : List Int := [0,1,2,3,4,6,10,17,23,24,25,26,27,28,29]
def requiredD1029 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1029 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1029_eq : pairedProblem rows1029 cols1029 requiredD1029 requiredS1029 =
    MomentData.problem1029 := by rfl
theorem leaf1029 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1029++rows1029))
    (hc : (q.map Prod.snd).Perm (cols1029++cols1029))
    (hd : ∀ k ∈ requiredD1029, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1029, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1029 cols1029 requiredD1029 requiredS1029
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1029_eq] at model
  exact MomentData.excluded1029 ds ss model
def rows1030 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def cols1030 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def requiredD1030 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1030 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1030_eq : pairedProblem rows1030 cols1030 requiredD1030 requiredS1030 =
    MomentData.problem1030 := by rfl
theorem leaf1030 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1030++rows1030))
    (hc : (q.map Prod.snd).Perm (cols1030++cols1030))
    (hd : ∀ k ∈ requiredD1030, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1030, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1030 cols1030 requiredD1030 requiredS1030
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1030_eq] at model
  exact MomentData.excluded1030 ds ss model
def rows1031 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def cols1031 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def requiredD1031 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS1031 : List Int := [19,21,23,24,25,26,27,28,29,30,31,32,33,35,37]
theorem problem1031_eq : pairedProblem rows1031 cols1031 requiredD1031 requiredS1031 =
    MomentData.problem1031 := by rfl
theorem leaf1031 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1031++rows1031))
    (hc : (q.map Prod.snd).Perm (cols1031++cols1031))
    (hd : ∀ k ∈ requiredD1031, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1031, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1031 cols1031 requiredD1031 requiredS1031
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1031_eq] at model
  exact MomentData.excluded1031 ds ss model
def rows1032 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def cols1032 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def requiredD1032 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1032 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem1032_eq : pairedProblem rows1032 cols1032 requiredD1032 requiredS1032 =
    MomentData.problem1032 := by rfl
theorem leaf1032 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1032++rows1032))
    (hc : (q.map Prod.snd).Perm (cols1032++cols1032))
    (hd : ∀ k ∈ requiredD1032, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1032, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1032 cols1032 requiredD1032 requiredS1032
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1032_eq] at model
  exact MomentData.excluded1032 ds ss model
def rows1033 : List Int := [0,1,2,3,4,5,13,16,22,24,25,26,27,28,29]
def cols1033 : List Int := [0,1,2,3,4,5,13,16,22,24,25,26,27,28,29]
def requiredD1033 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1033 : List Int := [21,23,24,25,26,27,28,29,30,31,32,33,34,35,37]
theorem problem1033_eq : pairedProblem rows1033 cols1033 requiredD1033 requiredS1033 =
    MomentData.problem1033 := by rfl
theorem leaf1033 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1033++rows1033))
    (hc : (q.map Prod.snd).Perm (cols1033++cols1033))
    (hd : ∀ k ∈ requiredD1033, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1033, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1033 cols1033 requiredD1033 requiredS1033
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1033_eq] at model
  exact MomentData.excluded1033 ds ss model
def rows1034 : List Int := [0,1,2,3,4,7,9,18,23,24,25,26,27,28,29]
def cols1034 : List Int := [0,1,2,3,4,7,9,18,23,24,25,26,27,28,29]
def requiredD1034 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1034 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1034_eq : pairedProblem rows1034 cols1034 requiredD1034 requiredS1034 =
    MomentData.problem1034 := by rfl
theorem leaf1034 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1034++rows1034))
    (hc : (q.map Prod.snd).Perm (cols1034++cols1034))
    (hd : ∀ k ∈ requiredD1034, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1034, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1034 cols1034 requiredD1034 requiredS1034
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1034_eq] at model
  exact MomentData.excluded1034 ds ss model
def rows1035 : List Int := [0,1,2,3,4,7,10,17,23,24,25,26,27,28,29]
def cols1035 : List Int := [0,1,2,3,4,7,10,17,23,24,25,26,27,28,29]
def requiredD1035 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1035 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1035_eq : pairedProblem rows1035 cols1035 requiredD1035 requiredS1035 =
    MomentData.problem1035 := by rfl
theorem leaf1035 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1035++rows1035))
    (hc : (q.map Prod.snd).Perm (cols1035++cols1035))
    (hd : ∀ k ∈ requiredD1035, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1035, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1035 cols1035 requiredD1035 requiredS1035
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1035_eq] at model
  exact MomentData.excluded1035 ds ss model
def rows1036 : List Int := [0,1,2,3,4,8,10,17,23,24,25,26,27,28,29]
def cols1036 : List Int := [0,1,2,3,4,8,10,17,23,24,25,26,27,28,29]
def requiredD1036 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1036 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1036_eq : pairedProblem rows1036 cols1036 requiredD1036 requiredS1036 =
    MomentData.problem1036 := by rfl
theorem leaf1036 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1036++rows1036))
    (hc : (q.map Prod.snd).Perm (cols1036++cols1036))
    (hd : ∀ k ∈ requiredD1036, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1036, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1036 cols1036 requiredD1036 requiredS1036
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1036_eq] at model
  exact MomentData.excluded1036 ds ss model
def rows1037 : List Int := [0,1,2,3,4,8,13,14,23,24,25,26,27,28,29]
def cols1037 : List Int := [0,1,2,3,4,8,13,14,23,24,25,26,27,28,29]
def requiredD1037 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1037 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem1037_eq : pairedProblem rows1037 cols1037 requiredD1037 requiredS1037 =
    MomentData.problem1037 := by rfl
theorem leaf1037 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1037++rows1037))
    (hc : (q.map Prod.snd).Perm (cols1037++cols1037))
    (hd : ∀ k ∈ requiredD1037, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1037, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1037 cols1037 requiredD1037 requiredS1037
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1037_eq] at model
  exact MomentData.excluded1037 ds ss model
def rows1038 : List Int := [0,1,2,3,4,9,10,17,23,24,25,26,27,28,29]
def cols1038 : List Int := [0,1,2,3,4,9,10,17,23,24,25,26,27,28,29]
def requiredD1038 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1038 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1038_eq : pairedProblem rows1038 cols1038 requiredD1038 requiredS1038 =
    MomentData.problem1038 := by rfl
theorem leaf1038 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1038++rows1038))
    (hc : (q.map Prod.snd).Perm (cols1038++cols1038))
    (hd : ∀ k ∈ requiredD1038, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1038, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1038 cols1038 requiredD1038 requiredS1038
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1038_eq] at model
  exact MomentData.excluded1038 ds ss model
def rows1039 : List Int := [0,1,2,3,4,10,11,17,23,24,25,26,27,28,29]
def cols1039 : List Int := [0,1,2,3,4,10,11,17,23,24,25,26,27,28,29]
def requiredD1039 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1039 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1039_eq : pairedProblem rows1039 cols1039 requiredD1039 requiredS1039 =
    MomentData.problem1039 := by rfl
theorem leaf1039 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1039++rows1039))
    (hc : (q.map Prod.snd).Perm (cols1039++cols1039))
    (hd : ∀ k ∈ requiredD1039, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1039, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1039 cols1039 requiredD1039 requiredS1039
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1039_eq] at model
  exact MomentData.excluded1039 ds ss model
def rows1040 : List Int := [0,1,2,3,4,9,12,18,23,24,25,26,27,28,29]
def cols1040 : List Int := [0,1,2,3,4,9,12,18,23,24,25,26,27,28,29]
def requiredD1040 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1040 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1040_eq : pairedProblem rows1040 cols1040 requiredD1040 requiredS1040 =
    MomentData.problem1040 := by rfl
theorem leaf1040 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1040++rows1040))
    (hc : (q.map Prod.snd).Perm (cols1040++cols1040))
    (hd : ∀ k ∈ requiredD1040, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1040, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1040 cols1040 requiredD1040 requiredS1040
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1040_eq] at model
  exact MomentData.excluded1040 ds ss model
def rows1041 : List Int := [0,1,2,3,4,10,12,17,23,24,25,26,27,28,29]
def cols1041 : List Int := [0,1,2,3,4,10,12,17,23,24,25,26,27,28,29]
def requiredD1041 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1041 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1041_eq : pairedProblem rows1041 cols1041 requiredD1041 requiredS1041 =
    MomentData.problem1041 := by rfl
theorem leaf1041 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1041++rows1041))
    (hc : (q.map Prod.snd).Perm (cols1041++cols1041))
    (hd : ∀ k ∈ requiredD1041, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1041, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1041 cols1041 requiredD1041 requiredS1041
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1041_eq] at model
  exact MomentData.excluded1041 ds ss model
def rows1042 : List Int := [0,1,2,3,4,6,13,21,23,24,25,26,27,28,29]
def cols1042 : List Int := [0,1,2,3,4,6,13,21,23,24,25,26,27,28,29]
def requiredD1042 : List Int := [-12,-10,-8,-6,-4,-3,-2,0,2,3,4,6,8,10,12]
def requiredS1042 : List Int := [15,17,19,21,23,24,25,27,29,30,31,33,35,37,39]
theorem problem1042_eq : pairedProblem rows1042 cols1042 requiredD1042 requiredS1042 =
    MomentData.problem1042 := by rfl
theorem leaf1042 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1042++rows1042))
    (hc : (q.map Prod.snd).Perm (cols1042++cols1042))
    (hd : ∀ k ∈ requiredD1042, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1042, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1042 cols1042 requiredD1042 requiredS1042
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1042_eq] at model
  exact MomentData.excluded1042 ds ss model
def rows1043 : List Int := [0,1,2,3,4,8,13,19,23,24,25,26,27,28,29]
def cols1043 : List Int := [0,1,2,3,4,8,13,19,23,24,25,26,27,28,29]
def requiredD1043 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS1043 : List Int := [15,17,19,21,23,25,26,27,28,29,31,33,35,37,39]
theorem problem1043_eq : pairedProblem rows1043 cols1043 requiredD1043 requiredS1043 =
    MomentData.problem1043 := by rfl
theorem leaf1043 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1043++rows1043))
    (hc : (q.map Prod.snd).Perm (cols1043++cols1043))
    (hd : ∀ k ∈ requiredD1043, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1043, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1043 cols1043 requiredD1043 requiredS1043
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1043_eq] at model
  exact MomentData.excluded1043 ds ss model
def rows1044 : List Int := [0,1,2,3,4,9,13,18,23,24,25,26,27,28,29]
def cols1044 : List Int := [0,1,2,3,4,9,13,18,23,24,25,26,27,28,29]
def requiredD1044 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1044 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1044_eq : pairedProblem rows1044 cols1044 requiredD1044 requiredS1044 =
    MomentData.problem1044 := by rfl
theorem leaf1044 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1044++rows1044))
    (hc : (q.map Prod.snd).Perm (cols1044++cols1044))
    (hd : ∀ k ∈ requiredD1044, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1044, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1044 cols1044 requiredD1044 requiredS1044
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1044_eq] at model
  exact MomentData.excluded1044 ds ss model
def rows1045 : List Int := [0,1,2,3,4,10,13,17,23,24,25,26,27,28,29]
def cols1045 : List Int := [0,1,2,3,4,10,13,17,23,24,25,26,27,28,29]
def requiredD1045 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1045 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1045_eq : pairedProblem rows1045 cols1045 requiredD1045 requiredS1045 =
    MomentData.problem1045 := by rfl
theorem leaf1045 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1045++rows1045))
    (hc : (q.map Prod.snd).Perm (cols1045++cols1045))
    (hd : ∀ k ∈ requiredD1045, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1045, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1045 cols1045 requiredD1045 requiredS1045
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1045_eq] at model
  exact MomentData.excluded1045 ds ss model
def rows1046 : List Int := [0,1,2,3,4,7,14,20,23,24,25,26,27,28,29]
def cols1046 : List Int := [0,1,2,3,4,7,14,20,23,24,25,26,27,28,29]
def requiredD1046 : List Int := [-13,-11,-9,-7,-5,-3,-1,0,1,3,5,7,9,11,13]
def requiredS1046 : List Int := [14,16,18,20,22,24,26,27,28,30,32,34,36,38,40]
theorem problem1046_eq : pairedProblem rows1046 cols1046 requiredD1046 requiredS1046 =
    MomentData.problem1046 := by rfl
theorem leaf1046 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1046++rows1046))
    (hc : (q.map Prod.snd).Perm (cols1046++cols1046))
    (hd : ∀ k ∈ requiredD1046, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1046, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1046 cols1046 requiredD1046 requiredS1046
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1046_eq] at model
  exact MomentData.excluded1046 ds ss model
def rows1047 : List Int := [0,1,2,3,4,8,14,19,23,24,25,26,27,28,29]
def cols1047 : List Int := [0,1,2,3,4,8,14,19,23,24,25,26,27,28,29]
def requiredD1047 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS1047 : List Int := [15,17,19,21,23,25,26,27,28,29,31,33,35,37,39]
theorem problem1047_eq : pairedProblem rows1047 cols1047 requiredD1047 requiredS1047 =
    MomentData.problem1047 := by rfl
theorem leaf1047 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1047++rows1047))
    (hc : (q.map Prod.snd).Perm (cols1047++cols1047))
    (hd : ∀ k ∈ requiredD1047, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1047, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1047 cols1047 requiredD1047 requiredS1047
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1047_eq] at model
  exact MomentData.excluded1047 ds ss model
def rows1048 : List Int := [0,1,2,3,4,9,14,18,23,24,25,26,27,28,29]
def cols1048 : List Int := [0,1,2,3,4,9,14,18,23,24,25,26,27,28,29]
def requiredD1048 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1048 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1048_eq : pairedProblem rows1048 cols1048 requiredD1048 requiredS1048 =
    MomentData.problem1048 := by rfl
theorem leaf1048 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1048++rows1048))
    (hc : (q.map Prod.snd).Perm (cols1048++cols1048))
    (hd : ∀ k ∈ requiredD1048, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1048, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1048 cols1048 requiredD1048 requiredS1048
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1048_eq] at model
  exact MomentData.excluded1048 ds ss model
def rows1049 : List Int := [0,1,2,3,4,10,14,17,23,24,25,26,27,28,29]
def cols1049 : List Int := [0,1,2,3,4,10,14,17,23,24,25,26,27,28,29]
def requiredD1049 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1049 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1049_eq : pairedProblem rows1049 cols1049 requiredD1049 requiredS1049 =
    MomentData.problem1049 := by rfl
theorem leaf1049 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1049++rows1049))
    (hc : (q.map Prod.snd).Perm (cols1049++cols1049))
    (hd : ∀ k ∈ requiredD1049, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1049, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1049 cols1049 requiredD1049 requiredS1049
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1049_eq] at model
  exact MomentData.excluded1049 ds ss model
def rows1050 : List Int := [0,1,2,3,4,8,15,19,23,24,25,26,27,28,29]
def cols1050 : List Int := [0,1,2,3,4,8,15,19,23,24,25,26,27,28,29]
def requiredD1050 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS1050 : List Int := [15,17,19,21,23,25,26,27,28,29,31,33,35,37,39]
theorem problem1050_eq : pairedProblem rows1050 cols1050 requiredD1050 requiredS1050 =
    MomentData.problem1050 := by rfl
theorem leaf1050 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1050++rows1050))
    (hc : (q.map Prod.snd).Perm (cols1050++cols1050))
    (hd : ∀ k ∈ requiredD1050, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1050, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1050 cols1050 requiredD1050 requiredS1050
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1050_eq] at model
  exact MomentData.excluded1050 ds ss model
def rows1051 : List Int := [0,1,2,3,4,9,15,18,23,24,25,26,27,28,29]
def cols1051 : List Int := [0,1,2,3,4,9,15,18,23,24,25,26,27,28,29]
def requiredD1051 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1051 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1051_eq : pairedProblem rows1051 cols1051 requiredD1051 requiredS1051 =
    MomentData.problem1051 := by rfl
theorem leaf1051 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1051++rows1051))
    (hc : (q.map Prod.snd).Perm (cols1051++cols1051))
    (hd : ∀ k ∈ requiredD1051, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1051, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1051 cols1051 requiredD1051 requiredS1051
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1051_eq] at model
  exact MomentData.excluded1051 ds ss model
def rows1052 : List Int := [0,1,2,3,4,10,15,17,23,24,25,26,27,28,29]
def cols1052 : List Int := [0,1,2,3,4,10,15,17,23,24,25,26,27,28,29]
def requiredD1052 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1052 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1052_eq : pairedProblem rows1052 cols1052 requiredD1052 requiredS1052 =
    MomentData.problem1052 := by rfl
theorem leaf1052 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1052++rows1052))
    (hc : (q.map Prod.snd).Perm (cols1052++cols1052))
    (hd : ∀ k ∈ requiredD1052, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1052, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1052 cols1052 requiredD1052 requiredS1052
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1052_eq] at model
  exact MomentData.excluded1052 ds ss model
def rows1053 : List Int := [0,1,2,3,4,9,16,18,23,24,25,26,27,28,29]
def cols1053 : List Int := [0,1,2,3,4,9,16,18,23,24,25,26,27,28,29]
def requiredD1053 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1053 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem1053_eq : pairedProblem rows1053 cols1053 requiredD1053 requiredS1053 =
    MomentData.problem1053 := by rfl
theorem leaf1053 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1053++rows1053))
    (hc : (q.map Prod.snd).Perm (cols1053++cols1053))
    (hd : ∀ k ∈ requiredD1053, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1053, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1053 cols1053 requiredD1053 requiredS1053
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1053_eq] at model
  exact MomentData.excluded1053 ds ss model
def rows1054 : List Int := [0,1,2,3,4,10,16,17,23,24,25,26,27,28,29]
def cols1054 : List Int := [0,1,2,3,4,10,16,17,23,24,25,26,27,28,29]
def requiredD1054 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1054 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1054_eq : pairedProblem rows1054 cols1054 requiredD1054 requiredS1054 =
    MomentData.problem1054 := by rfl
theorem leaf1054 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1054++rows1054))
    (hc : (q.map Prod.snd).Perm (cols1054++cols1054))
    (hd : ∀ k ∈ requiredD1054, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1054, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1054 cols1054 requiredD1054 requiredS1054
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1054_eq] at model
  exact MomentData.excluded1054 ds ss model
def rows1055 : List Int := [0,1,2,3,4,10,17,18,23,24,25,26,27,28,29]
def cols1055 : List Int := [0,1,2,3,4,10,17,18,23,24,25,26,27,28,29]
def requiredD1055 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1055 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1055_eq : pairedProblem rows1055 cols1055 requiredD1055 requiredS1055 =
    MomentData.problem1055 := by rfl
theorem leaf1055 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1055++rows1055))
    (hc : (q.map Prod.snd).Perm (cols1055++cols1055))
    (hd : ∀ k ∈ requiredD1055, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1055, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1055 cols1055 requiredD1055 requiredS1055
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1055_eq] at model
  exact MomentData.excluded1055 ds ss model
def rows1056 : List Int := [0,1,2,3,4,11,16,18,23,24,25,26,27,28,29]
def cols1056 : List Int := [0,1,2,3,4,11,16,18,23,24,25,26,27,28,29]
def requiredD1056 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1056 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem1056_eq : pairedProblem rows1056 cols1056 requiredD1056 requiredS1056 =
    MomentData.problem1056 := by rfl
theorem leaf1056 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1056++rows1056))
    (hc : (q.map Prod.snd).Perm (cols1056++cols1056))
    (hd : ∀ k ∈ requiredD1056, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1056, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1056 cols1056 requiredD1056 requiredS1056
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1056_eq] at model
  exact MomentData.excluded1056 ds ss model
def rows1057 : List Int := [0,1,2,3,4,12,15,18,23,24,25,26,27,28,29]
def cols1057 : List Int := [0,1,2,3,4,12,15,18,23,24,25,26,27,28,29]
def requiredD1057 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1057 : List Int := [19,21,22,23,24,25,26,27,28,29,30,31,32,33,35]
theorem problem1057_eq : pairedProblem rows1057 cols1057 requiredD1057 requiredS1057 =
    MomentData.problem1057 := by rfl
theorem leaf1057 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1057++rows1057))
    (hc : (q.map Prod.snd).Perm (cols1057++cols1057))
    (hd : ∀ k ∈ requiredD1057, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1057, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1057 cols1057 requiredD1057 requiredS1057
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1057_eq] at model
  exact MomentData.excluded1057 ds ss model
def rows1058 : List Int := [0,1,2,3,4,13,14,18,23,24,25,26,27,28,29]
def cols1058 : List Int := [0,1,2,3,4,13,14,18,23,24,25,26,27,28,29]
def requiredD1058 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1058 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem1058_eq : pairedProblem rows1058 cols1058 requiredD1058 requiredS1058 =
    MomentData.problem1058 := by rfl
theorem leaf1058 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1058++rows1058))
    (hc : (q.map Prod.snd).Perm (cols1058++cols1058))
    (hd : ∀ k ∈ requiredD1058, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1058, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1058 cols1058 requiredD1058 requiredS1058
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1058_eq] at model
  exact MomentData.excluded1058 ds ss model
def rows1059 : List Int := [0,1,2,3,4,10,17,19,23,24,25,26,27,28,29]
def cols1059 : List Int := [0,1,2,3,4,10,17,19,23,24,25,26,27,28,29]
def requiredD1059 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1059 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1059_eq : pairedProblem rows1059 cols1059 requiredD1059 requiredS1059 =
    MomentData.problem1059 := by rfl
theorem leaf1059 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1059++rows1059))
    (hc : (q.map Prod.snd).Perm (cols1059++cols1059))
    (hd : ∀ k ∈ requiredD1059, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1059, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1059 cols1059 requiredD1059 requiredS1059
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1059_eq] at model
  exact MomentData.excluded1059 ds ss model
def rows1060 : List Int := [0,1,2,3,4,11,16,19,23,24,25,26,27,28,29]
def cols1060 : List Int := [0,1,2,3,4,11,16,19,23,24,25,26,27,28,29]
def requiredD1060 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1060 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem1060_eq : pairedProblem rows1060 cols1060 requiredD1060 requiredS1060 =
    MomentData.problem1060 := by rfl
theorem leaf1060 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1060++rows1060))
    (hc : (q.map Prod.snd).Perm (cols1060++cols1060))
    (hd : ∀ k ∈ requiredD1060, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1060, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1060 cols1060 requiredD1060 requiredS1060
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1060_eq] at model
  exact MomentData.excluded1060 ds ss model
def rows1061 : List Int := [0,1,2,3,4,12,15,19,23,24,25,26,27,28,29]
def cols1061 : List Int := [0,1,2,3,4,12,15,19,23,24,25,26,27,28,29]
def requiredD1061 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1061 : List Int := [19,21,22,23,24,25,26,27,28,29,30,31,32,33,35]
theorem problem1061_eq : pairedProblem rows1061 cols1061 requiredD1061 requiredS1061 =
    MomentData.problem1061 := by rfl
theorem leaf1061 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1061++rows1061))
    (hc : (q.map Prod.snd).Perm (cols1061++cols1061))
    (hd : ∀ k ∈ requiredD1061, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1061, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1061 cols1061 requiredD1061 requiredS1061
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1061_eq] at model
  exact MomentData.excluded1061 ds ss model
def rows1062 : List Int := [0,1,2,3,4,13,14,19,23,24,25,26,27,28,29]
def cols1062 : List Int := [0,1,2,3,4,13,14,19,23,24,25,26,27,28,29]
def requiredD1062 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1062 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem1062_eq : pairedProblem rows1062 cols1062 requiredD1062 requiredS1062 =
    MomentData.problem1062 := by rfl
theorem leaf1062 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1062++rows1062))
    (hc : (q.map Prod.snd).Perm (cols1062++cols1062))
    (hd : ∀ k ∈ requiredD1062, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1062, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1062 cols1062 requiredD1062 requiredS1062
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1062_eq] at model
  exact MomentData.excluded1062 ds ss model
def rows1063 : List Int := [0,1,2,3,4,10,17,20,23,24,25,26,27,28,29]
def cols1063 : List Int := [0,1,2,3,4,10,17,20,23,24,25,26,27,28,29]
def requiredD1063 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1063 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1063_eq : pairedProblem rows1063 cols1063 requiredD1063 requiredS1063 =
    MomentData.problem1063 := by rfl
theorem leaf1063 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1063++rows1063))
    (hc : (q.map Prod.snd).Perm (cols1063++cols1063))
    (hd : ∀ k ∈ requiredD1063, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1063, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1063 cols1063 requiredD1063 requiredS1063
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1063_eq] at model
  exact MomentData.excluded1063 ds ss model
def rows1064 : List Int := [0,1,2,3,4,11,16,20,23,24,25,26,27,28,29]
def cols1064 : List Int := [0,1,2,3,4,11,16,20,23,24,25,26,27,28,29]
def requiredD1064 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1064 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem1064_eq : pairedProblem rows1064 cols1064 requiredD1064 requiredS1064 =
    MomentData.problem1064 := by rfl
theorem leaf1064 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1064++rows1064))
    (hc : (q.map Prod.snd).Perm (cols1064++cols1064))
    (hd : ∀ k ∈ requiredD1064, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1064, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1064 cols1064 requiredD1064 requiredS1064
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1064_eq] at model
  exact MomentData.excluded1064 ds ss model
def rows1065 : List Int := [0,1,2,3,4,12,15,20,23,24,25,26,27,28,29]
def cols1065 : List Int := [0,1,2,3,4,12,15,20,23,24,25,26,27,28,29]
def requiredD1065 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1065 : List Int := [19,21,22,23,24,25,26,27,28,29,30,31,32,33,35]
theorem problem1065_eq : pairedProblem rows1065 cols1065 requiredD1065 requiredS1065 =
    MomentData.problem1065 := by rfl
theorem leaf1065 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1065++rows1065))
    (hc : (q.map Prod.snd).Perm (cols1065++cols1065))
    (hd : ∀ k ∈ requiredD1065, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1065, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1065 cols1065 requiredD1065 requiredS1065
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1065_eq] at model
  exact MomentData.excluded1065 ds ss model
def rows1066 : List Int := [0,1,2,3,4,13,14,20,23,24,25,26,27,28,29]
def cols1066 : List Int := [0,1,2,3,4,13,14,20,23,24,25,26,27,28,29]
def requiredD1066 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1066 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem1066_eq : pairedProblem rows1066 cols1066 requiredD1066 requiredS1066 =
    MomentData.problem1066 := by rfl
theorem leaf1066 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1066++rows1066))
    (hc : (q.map Prod.snd).Perm (cols1066++cols1066))
    (hd : ∀ k ∈ requiredD1066, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1066, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1066 cols1066 requiredD1066 requiredS1066
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1066_eq] at model
  exact MomentData.excluded1066 ds ss model
def rows1067 : List Int := [0,1,2,3,4,13,14,20,23,24,25,26,27,28,29]
def cols1067 : List Int := [0,1,2,3,4,13,14,20,23,24,25,26,27,28,29]
def requiredD1067 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1067 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1067_eq : pairedProblem rows1067 cols1067 requiredD1067 requiredS1067 =
    MomentData.problem1067 := by rfl
theorem leaf1067 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1067++rows1067))
    (hc : (q.map Prod.snd).Perm (cols1067++cols1067))
    (hd : ∀ k ∈ requiredD1067, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1067, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1067 cols1067 requiredD1067 requiredS1067
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1067_eq] at model
  exact MomentData.excluded1067 ds ss model
def rows1068 : List Int := [0,1,2,3,4,10,17,21,23,24,25,26,27,28,29]
def cols1068 : List Int := [0,1,2,3,4,10,17,21,23,24,25,26,27,28,29]
def requiredD1068 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1068 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem1068_eq : pairedProblem rows1068 cols1068 requiredD1068 requiredS1068 =
    MomentData.problem1068 := by rfl
theorem leaf1068 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1068++rows1068))
    (hc : (q.map Prod.snd).Perm (cols1068++cols1068))
    (hd : ∀ k ∈ requiredD1068, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1068, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1068 cols1068 requiredD1068 requiredS1068
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1068_eq] at model
  exact MomentData.excluded1068 ds ss model
def rows1069 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def cols1069 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def requiredD1069 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1069 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem1069_eq : pairedProblem rows1069 cols1069 requiredD1069 requiredS1069 =
    MomentData.problem1069 := by rfl
theorem leaf1069 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1069++rows1069))
    (hc : (q.map Prod.snd).Perm (cols1069++cols1069))
    (hd : ∀ k ∈ requiredD1069, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1069, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1069 cols1069 requiredD1069 requiredS1069
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1069_eq] at model
  exact MomentData.excluded1069 ds ss model
def rows1070 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def cols1070 : List Int := [0,1,2,3,5,10,15,22,23,24,25,26,27,28,29]
def requiredD1070 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS1070 : List Int := [17,19,21,22,23,24,25,26,27,28,29,30,31,33,35]
theorem problem1070_eq : pairedProblem rows1070 cols1070 requiredD1070 requiredS1070 =
    MomentData.problem1070 := by rfl
theorem leaf1070 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1070++rows1070))
    (hc : (q.map Prod.snd).Perm (cols1070++cols1070))
    (hd : ∀ k ∈ requiredD1070, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1070, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1070 cols1070 requiredD1070 requiredS1070
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1070_eq] at model
  exact MomentData.excluded1070 ds ss model
def rows1071 : List Int := [0,1,2,3,4,12,15,21,23,24,25,26,27,28,29]
def cols1071 : List Int := [0,1,2,3,4,12,15,21,23,24,25,26,27,28,29]
def requiredD1071 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1071 : List Int := [19,21,22,23,24,25,26,27,28,29,30,31,32,33,35]
theorem problem1071_eq : pairedProblem rows1071 cols1071 requiredD1071 requiredS1071 =
    MomentData.problem1071 := by rfl
theorem leaf1071 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1071++rows1071))
    (hc : (q.map Prod.snd).Perm (cols1071++cols1071))
    (hd : ∀ k ∈ requiredD1071, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1071, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1071 cols1071 requiredD1071 requiredS1071
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1071_eq] at model
  exact MomentData.excluded1071 ds ss model
def rows1072 : List Int := [0,1,2,3,4,13,14,21,23,24,25,26,27,28,29]
def cols1072 : List Int := [0,1,2,3,4,13,14,21,23,24,25,26,27,28,29]
def requiredD1072 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1072 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem1072_eq : pairedProblem rows1072 cols1072 requiredD1072 requiredS1072 =
    MomentData.problem1072 := by rfl
theorem leaf1072 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1072++rows1072))
    (hc : (q.map Prod.snd).Perm (cols1072++cols1072))
    (hd : ∀ k ∈ requiredD1072, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1072, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1072 cols1072 requiredD1072 requiredS1072
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1072_eq] at model
  exact MomentData.excluded1072 ds ss model
def rows1073 : List Int := [0,1,2,3,9,12,16,22,23,24,25,26,27,28,29]
def cols1073 : List Int := [0,1,2,3,9,12,16,22,23,24,25,26,27,28,29]
def requiredD1073 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1073 : List Int := [15,17,19,21,22,23,24,25,26,27,28,29,31,33,35]
theorem problem1073_eq : pairedProblem rows1073 cols1073 requiredD1073 requiredS1073 =
    MomentData.problem1073 := by rfl
theorem leaf1073 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1073++rows1073))
    (hc : (q.map Prod.snd).Perm (cols1073++cols1073))
    (hd : ∀ k ∈ requiredD1073, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1073, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1073 cols1073 requiredD1073 requiredS1073
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1073_eq] at model
  exact MomentData.excluded1073 ds ss model
def rows1074 : List Int := [0,1,2,3,8,13,17,22,23,24,25,26,27,28,29]
def cols1074 : List Int := [0,1,2,3,8,13,17,22,23,24,25,26,27,28,29]
def requiredD1074 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1074 : List Int := [14,16,18,20,22,23,24,25,26,27,28,30,32,34,36]
theorem problem1074_eq : pairedProblem rows1074 cols1074 requiredD1074 requiredS1074 =
    MomentData.problem1074 := by rfl
theorem leaf1074 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1074++rows1074))
    (hc : (q.map Prod.snd).Perm (cols1074++cols1074))
    (hd : ∀ k ∈ requiredD1074, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1074, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1074 cols1074 requiredD1074 requiredS1074
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1074_eq] at model
  exact MomentData.excluded1074 ds ss model
def rows1075 : List Int := [0,1,2,3,8,14,17,22,23,24,25,26,27,28,29]
def cols1075 : List Int := [0,1,2,3,8,14,17,22,23,24,25,26,27,28,29]
def requiredD1075 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1075 : List Int := [14,16,18,20,22,23,24,25,26,27,28,30,32,34,36]
theorem problem1075_eq : pairedProblem rows1075 cols1075 requiredD1075 requiredS1075 =
    MomentData.problem1075 := by rfl
theorem leaf1075 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1075++rows1075))
    (hc : (q.map Prod.snd).Perm (cols1075++cols1075))
    (hd : ∀ k ∈ requiredD1075, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1075, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1075 cols1075 requiredD1075 requiredS1075
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1075_eq] at model
  exact MomentData.excluded1075 ds ss model
def rows1076 : List Int := [0,1,2,3,10,15,18,22,23,24,25,26,27,28,29]
def cols1076 : List Int := [0,1,2,3,10,15,18,22,23,24,25,26,27,28,29]
def requiredD1076 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1076 : List Int := [16,18,20,21,22,23,24,25,26,27,28,29,30,32,34]
theorem problem1076_eq : pairedProblem rows1076 cols1076 requiredD1076 requiredS1076 =
    MomentData.problem1076 := by rfl
theorem leaf1076 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1076++rows1076))
    (hc : (q.map Prod.snd).Perm (cols1076++cols1076))
    (hd : ∀ k ∈ requiredD1076, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1076, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1076 cols1076 requiredD1076 requiredS1076
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1076_eq] at model
  exact MomentData.excluded1076 ds ss model
def rows1077 : List Int := [0,1,2,3,11,14,18,22,23,24,25,26,27,28,29]
def cols1077 : List Int := [0,1,2,3,11,14,18,22,23,24,25,26,27,28,29]
def requiredD1077 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1077 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem1077_eq : pairedProblem rows1077 cols1077 requiredD1077 requiredS1077 =
    MomentData.problem1077 := by rfl
theorem leaf1077 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1077++rows1077))
    (hc : (q.map Prod.snd).Perm (cols1077++cols1077))
    (hd : ∀ k ∈ requiredD1077, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1077, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1077 cols1077 requiredD1077 requiredS1077
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1077_eq] at model
  exact MomentData.excluded1077 ds ss model
def rows1078 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def cols1078 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def requiredD1078 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1078 : List Int := [15,19,20,21,22,23,24,25,26,27,28,29,30,31,35]
theorem problem1078_eq : pairedProblem rows1078 cols1078 requiredD1078 requiredS1078 =
    MomentData.problem1078 := by rfl
theorem leaf1078 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1078++rows1078))
    (hc : (q.map Prod.snd).Perm (cols1078++cols1078))
    (hd : ∀ k ∈ requiredD1078, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1078, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1078 cols1078 requiredD1078 requiredS1078
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1078_eq] at model
  exact MomentData.excluded1078 ds ss model
def rows1079 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def cols1079 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def requiredD1079 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1079 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1079_eq : pairedProblem rows1079 cols1079 requiredD1079 requiredS1079 =
    MomentData.problem1079 := by rfl
theorem leaf1079 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1079++rows1079))
    (hc : (q.map Prod.snd).Perm (cols1079++cols1079))
    (hd : ∀ k ∈ requiredD1079, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1079, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1079 cols1079 requiredD1079 requiredS1079
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1079_eq] at model
  exact MomentData.excluded1079 ds ss model
def rows1080 : List Int := [0,1,2,3,10,15,19,22,23,24,25,26,27,28,29]
def cols1080 : List Int := [0,1,2,3,10,15,19,22,23,24,25,26,27,28,29]
def requiredD1080 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1080 : List Int := [16,18,20,21,22,23,24,25,26,27,28,29,30,32,34]
theorem problem1080_eq : pairedProblem rows1080 cols1080 requiredD1080 requiredS1080 =
    MomentData.problem1080 := by rfl
theorem leaf1080 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1080++rows1080))
    (hc : (q.map Prod.snd).Perm (cols1080++cols1080))
    (hd : ∀ k ∈ requiredD1080, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1080, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1080 cols1080 requiredD1080 requiredS1080
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1080_eq] at model
  exact MomentData.excluded1080 ds ss model
def rows1081 : List Int := [0,1,2,3,11,14,19,22,23,24,25,26,27,28,29]
def cols1081 : List Int := [0,1,2,3,11,14,19,22,23,24,25,26,27,28,29]
def requiredD1081 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1081 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem1081_eq : pairedProblem rows1081 cols1081 requiredD1081 requiredS1081 =
    MomentData.problem1081 := by rfl
theorem leaf1081 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1081++rows1081))
    (hc : (q.map Prod.snd).Perm (cols1081++cols1081))
    (hd : ∀ k ∈ requiredD1081, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1081, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1081 cols1081 requiredD1081 requiredS1081
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1081_eq] at model
  exact MomentData.excluded1081 ds ss model
def rows1082 : List Int := [0,1,2,3,12,13,19,22,23,24,25,26,27,28,29]
def cols1082 : List Int := [0,1,2,3,12,13,19,22,23,24,25,26,27,28,29]
def requiredD1082 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1082 : List Int := [15,19,20,21,22,23,24,25,26,27,28,29,30,31,35]
theorem problem1082_eq : pairedProblem rows1082 cols1082 requiredD1082 requiredS1082 =
    MomentData.problem1082 := by rfl
theorem leaf1082 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1082++rows1082))
    (hc : (q.map Prod.snd).Perm (cols1082++cols1082))
    (hd : ∀ k ∈ requiredD1082, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1082, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1082 cols1082 requiredD1082 requiredS1082
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1082_eq] at model
  exact MomentData.excluded1082 ds ss model
def rows1083 : List Int := [0,1,2,3,10,15,20,22,23,24,25,26,27,28,29]
def cols1083 : List Int := [0,1,2,3,10,15,20,22,23,24,25,26,27,28,29]
def requiredD1083 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1083 : List Int := [16,18,20,21,22,23,24,25,26,27,28,29,30,32,34]
theorem problem1083_eq : pairedProblem rows1083 cols1083 requiredD1083 requiredS1083 =
    MomentData.problem1083 := by rfl
theorem leaf1083 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1083++rows1083))
    (hc : (q.map Prod.snd).Perm (cols1083++cols1083))
    (hd : ∀ k ∈ requiredD1083, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1083, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1083 cols1083 requiredD1083 requiredS1083
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1083_eq] at model
  exact MomentData.excluded1083 ds ss model
def rows1084 : List Int := [0,1,2,9,14,18,21,22,23,24,25,26,27,28,29]
def cols1084 : List Int := [0,1,2,9,14,18,21,22,23,24,25,26,27,28,29]
def requiredD1084 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1084 : List Int := [14,16,18,19,20,21,22,23,24,25,26,27,28,30,32]
theorem problem1084_eq : pairedProblem rows1084 cols1084 requiredD1084 requiredS1084 =
    MomentData.problem1084 := by rfl
theorem leaf1084 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1084++rows1084))
    (hc : (q.map Prod.snd).Perm (cols1084++cols1084))
    (hd : ∀ k ∈ requiredD1084, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1084, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1084 cols1084 requiredD1084 requiredS1084
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1084_eq] at model
  exact MomentData.excluded1084 ds ss model
def rows1085 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def cols1085 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def requiredD1085 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1085 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem1085_eq : pairedProblem rows1085 cols1085 requiredD1085 requiredS1085 =
    MomentData.problem1085 := by rfl
theorem leaf1085 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1085++rows1085))
    (hc : (q.map Prod.snd).Perm (cols1085++cols1085))
    (hd : ∀ k ∈ requiredD1085, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1085, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1085 cols1085 requiredD1085 requiredS1085
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1085_eq] at model
  exact MomentData.excluded1085 ds ss model
def rows1086 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def cols1086 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def requiredD1086 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1086 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1086_eq : pairedProblem rows1086 cols1086 requiredD1086 requiredS1086 =
    MomentData.problem1086 := by rfl
theorem leaf1086 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1086++rows1086))
    (hc : (q.map Prod.snd).Perm (cols1086++cols1086))
    (hd : ∀ k ∈ requiredD1086, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1086, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1086 cols1086 requiredD1086 requiredS1086
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1086_eq] at model
  exact MomentData.excluded1086 ds ss model
def rows1087 : List Int := [0,1,2,3,4,9,13,14,15,24,25,26,27,28,29]
def cols1087 : List Int := [0,1,2,3,4,9,13,14,15,24,25,26,27,28,29]
def requiredD1087 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1087 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem1087_eq : pairedProblem rows1087 cols1087 requiredD1087 requiredS1087 =
    MomentData.problem1087 := by rfl
theorem leaf1087 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1087++rows1087))
    (hc : (q.map Prod.snd).Perm (cols1087++cols1087))
    (hd : ∀ k ∈ requiredD1087, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1087, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1087 cols1087 requiredD1087 requiredS1087
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1087_eq] at model
  exact MomentData.excluded1087 ds ss model
def rows1088 : List Int := [0,1,2,3,4,13,14,15,19,24,25,26,27,28,29]
def cols1088 : List Int := [0,1,2,3,4,13,14,15,19,24,25,26,27,28,29]
def requiredD1088 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1088 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem1088_eq : pairedProblem rows1088 cols1088 requiredD1088 requiredS1088 =
    MomentData.problem1088 := by rfl
theorem leaf1088 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1088++rows1088))
    (hc : (q.map Prod.snd).Perm (cols1088++cols1088))
    (hd : ∀ k ∈ requiredD1088, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1088, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1088 cols1088 requiredD1088 requiredS1088
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1088_eq] at model
  exact MomentData.excluded1088 ds ss model
def rows1089 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def cols1089 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def requiredD1089 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1089 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem1089_eq : pairedProblem rows1089 cols1089 requiredD1089 requiredS1089 =
    MomentData.problem1089 := by rfl
theorem leaf1089 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1089++rows1089))
    (hc : (q.map Prod.snd).Perm (cols1089++cols1089))
    (hd : ∀ k ∈ requiredD1089, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1089, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1089 cols1089 requiredD1089 requiredS1089
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1089_eq] at model
  exact MomentData.excluded1089 ds ss model
def rows1090 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def cols1090 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def requiredD1090 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1090 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1090_eq : pairedProblem rows1090 cols1090 requiredD1090 requiredS1090 =
    MomentData.problem1090 := by rfl
theorem leaf1090 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1090++rows1090))
    (hc : (q.map Prod.snd).Perm (cols1090++cols1090))
    (hd : ∀ k ∈ requiredD1090, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1090, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1090 cols1090 requiredD1090 requiredS1090
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1090_eq] at model
  exact MomentData.excluded1090 ds ss model
def rows1091 : List Int := [0,1,2,3,4,13,14,15,21,24,25,26,27,28,29]
def cols1091 : List Int := [0,1,2,3,4,13,14,15,21,24,25,26,27,28,29]
def requiredD1091 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1091 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem1091_eq : pairedProblem rows1091 cols1091 requiredD1091 requiredS1091 =
    MomentData.problem1091 := by rfl
theorem leaf1091 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1091++rows1091))
    (hc : (q.map Prod.snd).Perm (cols1091++cols1091))
    (hd : ∀ k ∈ requiredD1091, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1091, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1091 cols1091 requiredD1091 requiredS1091
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1091_eq] at model
  exact MomentData.excluded1091 ds ss model
def rows1092 : List Int := [0,1,2,3,4,13,14,15,21,24,25,26,27,28,29]
def cols1092 : List Int := [0,1,2,3,4,13,14,15,21,24,25,26,27,28,29]
def requiredD1092 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1092 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1092_eq : pairedProblem rows1092 cols1092 requiredD1092 requiredS1092 =
    MomentData.problem1092 := by rfl
theorem leaf1092 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1092++rows1092))
    (hc : (q.map Prod.snd).Perm (cols1092++cols1092))
    (hd : ∀ k ∈ requiredD1092, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1092, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1092 cols1092 requiredD1092 requiredS1092
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1092_eq] at model
  exact MomentData.excluded1092 ds ss model
def rows1093 : List Int := [0,1,2,3,8,12,13,14,23,24,25,26,27,28,29]
def cols1093 : List Int := [0,1,2,3,8,12,13,14,23,24,25,26,27,28,29]
def requiredD1093 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1093 : List Int := [15,20,21,22,23,24,25,26,27,28,29,30,31,32,37]
theorem problem1093_eq : pairedProblem rows1093 cols1093 requiredD1093 requiredS1093 =
    MomentData.problem1093 := by rfl
theorem leaf1093 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1093++rows1093))
    (hc : (q.map Prod.snd).Perm (cols1093++cols1093))
    (hd : ∀ k ∈ requiredD1093, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1093, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1093 cols1093 requiredD1093 requiredS1093
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1093_eq] at model
  exact MomentData.excluded1093 ds ss model
def rows1094 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def cols1094 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def requiredD1094 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1094 : List Int := [15,20,21,22,23,24,25,26,27,28,29,30,31,32,37]
theorem problem1094_eq : pairedProblem rows1094 cols1094 requiredD1094 requiredS1094 =
    MomentData.problem1094 := by rfl
theorem leaf1094 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1094++rows1094))
    (hc : (q.map Prod.snd).Perm (cols1094++cols1094))
    (hd : ∀ k ∈ requiredD1094, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1094, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1094 cols1094 requiredD1094 requiredS1094
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1094_eq] at model
  exact MomentData.excluded1094 ds ss model
def rows1095 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def cols1095 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def requiredD1095 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1095 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1095_eq : pairedProblem rows1095 cols1095 requiredD1095 requiredS1095 =
    MomentData.problem1095 := by rfl
theorem leaf1095 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1095++rows1095))
    (hc : (q.map Prod.snd).Perm (cols1095++cols1095))
    (hd : ∀ k ∈ requiredD1095, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1095, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1095 cols1095 requiredD1095 requiredS1095
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1095_eq] at model
  exact MomentData.excluded1095 ds ss model
def rows1096 : List Int := [0,1,2,3,12,13,14,20,23,24,25,26,27,28,29]
def cols1096 : List Int := [0,1,2,3,12,13,14,20,23,24,25,26,27,28,29]
def requiredD1096 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS1096 : List Int := [15,20,21,22,23,24,25,26,27,28,29,30,31,32,37]
theorem problem1096_eq : pairedProblem rows1096 cols1096 requiredD1096 requiredS1096 =
    MomentData.problem1096 := by rfl
theorem leaf1096 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1096++rows1096))
    (hc : (q.map Prod.snd).Perm (cols1096++cols1096))
    (hd : ∀ k ∈ requiredD1096, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1096, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1096 cols1096 requiredD1096 requiredS1096
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1096_eq] at model
  exact MomentData.excluded1096 ds ss model
def rows1097 : List Int := [0,1,2,3,4,6,8,16,21,23,25,26,27,28,29]
def cols1097 : List Int := [0,1,2,3,4,6,8,16,21,23,25,26,27,28,29]
def requiredD1097 : List Int := [-12,-10,-8,-6,-5,-4,-2,0,2,4,5,6,8,10,12]
def requiredS1097 : List Int := [17,19,21,23,24,25,27,29,31,33,34,35,37,39,41]
theorem problem1097_eq : pairedProblem rows1097 cols1097 requiredD1097 requiredS1097 =
    MomentData.problem1097 := by rfl
theorem leaf1097 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1097++rows1097))
    (hc : (q.map Prod.snd).Perm (cols1097++cols1097))
    (hd : ∀ k ∈ requiredD1097, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1097, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1097 cols1097 requiredD1097 requiredS1097
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1097_eq] at model
  exact MomentData.excluded1097 ds ss model
def rows1098 : List Int := [0,1,2,3,4,13,14,15,16,20,25,26,27,28,29]
def cols1098 : List Int := [0,1,2,3,4,13,14,15,16,20,25,26,27,28,29]
def requiredD1098 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1098 : List Int := [17,23,24,25,26,27,28,29,30,31,32,33,34,35,41]
theorem problem1098_eq : pairedProblem rows1098 cols1098 requiredD1098 requiredS1098 =
    MomentData.problem1098 := by rfl
theorem leaf1098 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1098++rows1098))
    (hc : (q.map Prod.snd).Perm (cols1098++cols1098))
    (hd : ∀ k ∈ requiredD1098, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1098, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1098 cols1098 requiredD1098 requiredS1098
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1098_eq] at model
  exact MomentData.excluded1098 ds ss model
def rows1099 : List Int := [0,1,2,3,4,13,14,15,16,20,25,26,27,28,29]
def cols1099 : List Int := [0,1,2,3,4,13,14,15,16,20,25,26,27,28,29]
def requiredD1099 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1099 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1099_eq : pairedProblem rows1099 cols1099 requiredD1099 requiredS1099 =
    MomentData.problem1099 := by rfl
theorem leaf1099 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1099++rows1099))
    (hc : (q.map Prod.snd).Perm (cols1099++cols1099))
    (hd : ∀ k ∈ requiredD1099, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1099, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1099 cols1099 requiredD1099 requiredS1099
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1099_eq] at model
  exact MomentData.excluded1099 ds ss model
def rows1100 : List Int := [0,1,2,3,4,13,14,15,16,21,25,26,27,28,29]
def cols1100 : List Int := [0,1,2,3,4,13,14,15,16,21,25,26,27,28,29]
def requiredD1100 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1100 : List Int := [17,23,24,25,26,27,28,29,30,31,32,33,34,35,41]
theorem problem1100_eq : pairedProblem rows1100 cols1100 requiredD1100 requiredS1100 =
    MomentData.problem1100 := by rfl
theorem leaf1100 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1100++rows1100))
    (hc : (q.map Prod.snd).Perm (cols1100++cols1100))
    (hd : ∀ k ∈ requiredD1100, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1100, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1100 cols1100 requiredD1100 requiredS1100
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1100_eq] at model
  exact MomentData.excluded1100 ds ss model
def rows1101 : List Int := [0,1,2,3,4,13,14,15,16,21,25,26,27,28,29]
def cols1101 : List Int := [0,1,2,3,4,13,14,15,16,21,25,26,27,28,29]
def requiredD1101 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1101 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1101_eq : pairedProblem rows1101 cols1101 requiredD1101 requiredS1101 =
    MomentData.problem1101 := by rfl
theorem leaf1101 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1101++rows1101))
    (hc : (q.map Prod.snd).Perm (cols1101++cols1101))
    (hd : ∀ k ∈ requiredD1101, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1101, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1101 cols1101 requiredD1101 requiredS1101
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1101_eq] at model
  exact MomentData.excluded1101 ds ss model
def rows1102 : List Int := [0,1,2,3,8,12,13,14,15,24,25,26,27,28,29]
def cols1102 : List Int := [0,1,2,3,8,12,13,14,15,24,25,26,27,28,29]
def requiredD1102 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1102 : List Int := [15,21,22,23,24,25,26,27,28,29,30,31,32,33,39]
theorem problem1102_eq : pairedProblem rows1102 cols1102 requiredD1102 requiredS1102 =
    MomentData.problem1102 := by rfl
theorem leaf1102 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1102++rows1102))
    (hc : (q.map Prod.snd).Perm (cols1102++cols1102))
    (hd : ∀ k ∈ requiredD1102, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1102, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1102 cols1102 requiredD1102 requiredS1102
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1102_eq] at model
  exact MomentData.excluded1102 ds ss model
def rows1103 : List Int := [0,1,2,3,8,12,13,14,15,24,25,26,27,28,29]
def cols1103 : List Int := [0,1,2,3,8,12,13,14,15,24,25,26,27,28,29]
def requiredD1103 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1103 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1103_eq : pairedProblem rows1103 cols1103 requiredD1103 requiredS1103 =
    MomentData.problem1103 := by rfl
theorem leaf1103 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1103++rows1103))
    (hc : (q.map Prod.snd).Perm (cols1103++cols1103))
    (hd : ∀ k ∈ requiredD1103, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1103, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1103 cols1103 requiredD1103 requiredS1103
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1103_eq] at model
  exact MomentData.excluded1103 ds ss model
def rows1104 : List Int := [0,1,2,3,9,12,13,14,15,24,25,26,27,28,29]
def cols1104 : List Int := [0,1,2,3,9,12,13,14,15,24,25,26,27,28,29]
def requiredD1104 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1104 : List Int := [15,21,22,23,24,25,26,27,28,29,30,31,32,33,39]
theorem problem1104_eq : pairedProblem rows1104 cols1104 requiredD1104 requiredS1104 =
    MomentData.problem1104 := by rfl
theorem leaf1104 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1104++rows1104))
    (hc : (q.map Prod.snd).Perm (cols1104++cols1104))
    (hd : ∀ k ∈ requiredD1104, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1104, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1104 cols1104 requiredD1104 requiredS1104
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1104_eq] at model
  exact MomentData.excluded1104 ds ss model
def rows1105 : List Int := [0,1,2,3,5,7,12,20,22,24,25,26,27,28,29]
def cols1105 : List Int := [0,1,2,3,5,7,12,20,22,24,25,26,27,28,29]
def requiredD1105 : List Int := [-12,-10,-8,-6,-5,-4,-2,0,2,4,5,6,8,10,12]
def requiredS1105 : List Int := [15,17,19,21,22,23,25,27,29,31,32,33,35,37,39]
theorem problem1105_eq : pairedProblem rows1105 cols1105 requiredD1105 requiredS1105 =
    MomentData.problem1105 := by rfl
theorem leaf1105 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1105++rows1105))
    (hc : (q.map Prod.snd).Perm (cols1105++cols1105))
    (hd : ∀ k ∈ requiredD1105, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1105, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1105 cols1105 requiredD1105 requiredS1105
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1105_eq] at model
  exact MomentData.excluded1105 ds ss model
def rows1106 : List Int := [0,1,2,3,12,13,14,15,20,24,25,26,27,28,29]
def cols1106 : List Int := [0,1,2,3,12,13,14,15,20,24,25,26,27,28,29]
def requiredD1106 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1106 : List Int := [15,21,22,23,24,25,26,27,28,29,30,31,32,33,39]
theorem problem1106_eq : pairedProblem rows1106 cols1106 requiredD1106 requiredS1106 =
    MomentData.problem1106 := by rfl
theorem leaf1106 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1106++rows1106))
    (hc : (q.map Prod.snd).Perm (cols1106++cols1106))
    (hd : ∀ k ∈ requiredD1106, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1106, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1106 cols1106 requiredD1106 requiredS1106
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1106_eq] at model
  exact MomentData.excluded1106 ds ss model
def rows1107 : List Int := [0,1,2,3,12,13,14,15,20,24,25,26,27,28,29]
def cols1107 : List Int := [0,1,2,3,12,13,14,15,20,24,25,26,27,28,29]
def requiredD1107 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1107 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1107_eq : pairedProblem rows1107 cols1107 requiredD1107 requiredS1107 =
    MomentData.problem1107 := by rfl
theorem leaf1107 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1107++rows1107))
    (hc : (q.map Prod.snd).Perm (cols1107++cols1107))
    (hd : ∀ k ∈ requiredD1107, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1107, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1107 cols1107 requiredD1107 requiredS1107
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1107_eq] at model
  exact MomentData.excluded1107 ds ss model
def rows1108 : List Int := [0,1,2,3,12,13,14,15,21,24,25,26,27,28,29]
def cols1108 : List Int := [0,1,2,3,12,13,14,15,21,24,25,26,27,28,29]
def requiredD1108 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1108 : List Int := [15,21,22,23,24,25,26,27,28,29,30,31,32,33,39]
theorem problem1108_eq : pairedProblem rows1108 cols1108 requiredD1108 requiredS1108 =
    MomentData.problem1108 := by rfl
theorem leaf1108 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1108++rows1108))
    (hc : (q.map Prod.snd).Perm (cols1108++cols1108))
    (hd : ∀ k ∈ requiredD1108, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1108, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1108 cols1108 requiredD1108 requiredS1108
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1108_eq] at model
  exact MomentData.excluded1108 ds ss model
def rows1109 : List Int := [0,1,2,8,11,12,13,14,23,24,25,26,27,28,29]
def cols1109 : List Int := [0,1,2,8,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1109 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1109 : List Int := [13,19,20,21,22,23,24,25,26,27,28,29,30,31,37]
theorem problem1109_eq : pairedProblem rows1109 cols1109 requiredD1109 requiredS1109 =
    MomentData.problem1109 := by rfl
theorem leaf1109 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1109++rows1109))
    (hc : (q.map Prod.snd).Perm (cols1109++cols1109))
    (hd : ∀ k ∈ requiredD1109, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1109, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1109 cols1109 requiredD1109 requiredS1109
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1109_eq] at model
  exact MomentData.excluded1109 ds ss model
def rows1110 : List Int := [0,1,2,4,6,13,19,21,23,24,25,26,27,28,29]
def cols1110 : List Int := [0,1,2,4,6,13,19,21,23,24,25,26,27,28,29]
def requiredD1110 : List Int := [-12,-10,-8,-6,-5,-4,-2,0,2,4,5,6,8,10,12]
def requiredS1110 : List Int := [13,15,17,19,20,21,23,25,27,29,30,31,33,35,37]
theorem problem1110_eq : pairedProblem rows1110 cols1110 requiredD1110 requiredS1110 =
    MomentData.problem1110 := by rfl
theorem leaf1110 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1110++rows1110))
    (hc : (q.map Prod.snd).Perm (cols1110++cols1110))
    (hd : ∀ k ∈ requiredD1110, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1110, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1110 cols1110 requiredD1110 requiredS1110
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1110_eq] at model
  exact MomentData.excluded1110 ds ss model
def rows1111 : List Int := [0,1,7,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1111 : List Int := [0,1,7,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1111 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1111 : List Int := [11,17,18,19,20,21,22,23,24,25,26,27,28,29,35]
theorem problem1111_eq : pairedProblem rows1111 cols1111 requiredD1111 requiredS1111 =
    MomentData.problem1111 := by rfl
theorem leaf1111 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1111++rows1111))
    (hc : (q.map Prod.snd).Perm (cols1111++cols1111))
    (hd : ∀ k ∈ requiredD1111, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1111, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1111 cols1111 requiredD1111 requiredS1111
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1111_eq] at model
  exact MomentData.excluded1111 ds ss model
def rows1112 : List Int := [0,6,9,10,11,12,21,22,23,24,25,26,27,28,29]
def cols1112 : List Int := [0,6,9,10,11,12,21,22,23,24,25,26,27,28,29]
def requiredD1112 : List Int := [-12,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,12]
def requiredS1112 : List Int := [9,15,16,17,18,19,20,21,22,23,24,25,26,27,33]
theorem problem1112_eq : pairedProblem rows1112 cols1112 requiredD1112 requiredS1112 =
    MomentData.problem1112 := by rfl
theorem leaf1112 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1112++rows1112))
    (hc : (q.map Prod.snd).Perm (cols1112++cols1112))
    (hd : ∀ k ∈ requiredD1112, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1112, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1112 cols1112 requiredD1112 requiredS1112
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1112_eq] at model
  exact MomentData.excluded1112 ds ss model
def rows1113 : List Int := [0,1,2,3,8,12,13,14,15,16,25,26,27,28,29]
def cols1113 : List Int := [0,1,2,3,8,12,13,14,15,16,25,26,27,28,29]
def requiredD1113 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1113 : List Int := [15,22,23,24,25,26,27,28,29,30,31,32,33,34,41]
theorem problem1113_eq : pairedProblem rows1113 cols1113 requiredD1113 requiredS1113 =
    MomentData.problem1113 := by rfl
theorem leaf1113 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1113++rows1113))
    (hc : (q.map Prod.snd).Perm (cols1113++cols1113))
    (hd : ∀ k ∈ requiredD1113, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1113, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1113 cols1113 requiredD1113 requiredS1113
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1113_eq] at model
  exact MomentData.excluded1113 ds ss model
def rows1114 : List Int := [0,1,2,3,8,12,13,14,15,16,25,26,27,28,29]
def cols1114 : List Int := [0,1,2,3,8,12,13,14,15,16,25,26,27,28,29]
def requiredD1114 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1114 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1114_eq : pairedProblem rows1114 cols1114 requiredD1114 requiredS1114 =
    MomentData.problem1114 := by rfl
theorem leaf1114 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1114++rows1114))
    (hc : (q.map Prod.snd).Perm (cols1114++cols1114))
    (hd : ∀ k ∈ requiredD1114, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1114, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1114 cols1114 requiredD1114 requiredS1114
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1114_eq] at model
  exact MomentData.excluded1114 ds ss model
def rows1115 : List Int := [0,1,2,3,12,13,14,15,16,21,25,26,27,28,29]
def cols1115 : List Int := [0,1,2,3,12,13,14,15,16,21,25,26,27,28,29]
def requiredD1115 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1115 : List Int := [15,22,23,24,25,26,27,28,29,30,31,32,33,34,41]
theorem problem1115_eq : pairedProblem rows1115 cols1115 requiredD1115 requiredS1115 =
    MomentData.problem1115 := by rfl
theorem leaf1115 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1115++rows1115))
    (hc : (q.map Prod.snd).Perm (cols1115++cols1115))
    (hd : ∀ k ∈ requiredD1115, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1115, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1115 cols1115 requiredD1115 requiredS1115
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1115_eq] at model
  exact MomentData.excluded1115 ds ss model
def rows1116 : List Int := [0,1,2,3,12,13,14,15,16,21,25,26,27,28,29]
def cols1116 : List Int := [0,1,2,3,12,13,14,15,16,21,25,26,27,28,29]
def requiredD1116 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1116 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1116_eq : pairedProblem rows1116 cols1116 requiredD1116 requiredS1116 =
    MomentData.problem1116 := by rfl
theorem leaf1116 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1116++rows1116))
    (hc : (q.map Prod.snd).Perm (cols1116++cols1116))
    (hd : ∀ k ∈ requiredD1116, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1116, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1116 cols1116 requiredD1116 requiredS1116
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1116_eq] at model
  exact MomentData.excluded1116 ds ss model
def rows1117 : List Int := [0,1,2,7,11,12,13,14,15,24,25,26,27,28,29]
def cols1117 : List Int := [0,1,2,7,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1117 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1117 : List Int := [13,20,21,22,23,24,25,26,27,28,29,30,31,32,39]
theorem problem1117_eq : pairedProblem rows1117 cols1117 requiredD1117 requiredS1117 =
    MomentData.problem1117 := by rfl
theorem leaf1117 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1117++rows1117))
    (hc : (q.map Prod.snd).Perm (cols1117++cols1117))
    (hd : ∀ k ∈ requiredD1117, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1117, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1117 cols1117 requiredD1117 requiredS1117
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1117_eq] at model
  exact MomentData.excluded1117 ds ss model
def rows1118 : List Int := [0,1,2,7,11,12,13,14,15,24,25,26,27,28,29]
def cols1118 : List Int := [0,1,2,7,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1118 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1118 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1118_eq : pairedProblem rows1118 cols1118 requiredD1118 requiredS1118 =
    MomentData.problem1118 := by rfl
theorem leaf1118 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1118++rows1118))
    (hc : (q.map Prod.snd).Perm (cols1118++cols1118))
    (hd : ∀ k ∈ requiredD1118, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1118, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1118 cols1118 requiredD1118 requiredS1118
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1118_eq] at model
  exact MomentData.excluded1118 ds ss model
def rows1119 : List Int := [0,1,2,8,11,12,13,14,15,24,25,26,27,28,29]
def cols1119 : List Int := [0,1,2,8,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1119 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1119 : List Int := [13,20,21,22,23,24,25,26,27,28,29,30,31,32,39]
theorem problem1119_eq : pairedProblem rows1119 cols1119 requiredD1119 requiredS1119 =
    MomentData.problem1119 := by rfl
theorem leaf1119 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1119++rows1119))
    (hc : (q.map Prod.snd).Perm (cols1119++cols1119))
    (hd : ∀ k ∈ requiredD1119, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1119, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1119 cols1119 requiredD1119 requiredS1119
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1119_eq] at model
  exact MomentData.excluded1119 ds ss model
def rows1120 : List Int := [0,1,2,8,11,12,13,14,15,24,25,26,27,28,29]
def cols1120 : List Int := [0,1,2,8,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1120 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1120 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1120_eq : pairedProblem rows1120 cols1120 requiredD1120 requiredS1120 =
    MomentData.problem1120 := by rfl
theorem leaf1120 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1120++rows1120))
    (hc : (q.map Prod.snd).Perm (cols1120++cols1120))
    (hd : ∀ k ∈ requiredD1120, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1120, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1120 cols1120 requiredD1120 requiredS1120
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1120_eq] at model
  exact MomentData.excluded1120 ds ss model
def rows1121 : List Int := [0,1,2,11,12,13,14,15,20,24,25,26,27,28,29]
def cols1121 : List Int := [0,1,2,11,12,13,14,15,20,24,25,26,27,28,29]
def requiredD1121 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1121 : List Int := [13,20,21,22,23,24,25,26,27,28,29,30,31,32,39]
theorem problem1121_eq : pairedProblem rows1121 cols1121 requiredD1121 requiredS1121 =
    MomentData.problem1121 := by rfl
theorem leaf1121 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1121++rows1121))
    (hc : (q.map Prod.snd).Perm (cols1121++cols1121))
    (hd : ∀ k ∈ requiredD1121, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1121, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1121 cols1121 requiredD1121 requiredS1121
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1121_eq] at model
  exact MomentData.excluded1121 ds ss model
def rows1122 : List Int := [0,1,6,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1122 : List Int := [0,1,6,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1122 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1122 : List Int := [11,18,19,20,21,22,23,24,25,26,27,28,29,30,37]
theorem problem1122_eq : pairedProblem rows1122 cols1122 requiredD1122 requiredS1122 =
    MomentData.problem1122 := by rfl
theorem leaf1122 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1122++rows1122))
    (hc : (q.map Prod.snd).Perm (cols1122++cols1122))
    (hd : ∀ k ∈ requiredD1122, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1122, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1122 cols1122 requiredD1122 requiredS1122
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1122_eq] at model
  exact MomentData.excluded1122 ds ss model
def rows1123 : List Int := [0,1,7,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1123 : List Int := [0,1,7,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1123 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1123 : List Int := [11,18,19,20,21,22,23,24,25,26,27,28,29,30,37]
theorem problem1123_eq : pairedProblem rows1123 cols1123 requiredD1123 requiredS1123 =
    MomentData.problem1123 := by rfl
theorem leaf1123 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1123++rows1123))
    (hc : (q.map Prod.snd).Perm (cols1123++cols1123))
    (hd : ∀ k ∈ requiredD1123, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1123, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1123 cols1123 requiredD1123 requiredS1123
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1123_eq] at model
  exact MomentData.excluded1123 ds ss model
def rows1124 : List Int := [0,1,7,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1124 : List Int := [0,1,7,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1124 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1124 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1124_eq : pairedProblem rows1124 cols1124 requiredD1124 requiredS1124 =
    MomentData.problem1124 := by rfl
theorem leaf1124 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1124++rows1124))
    (hc : (q.map Prod.snd).Perm (cols1124++cols1124))
    (hd : ∀ k ∈ requiredD1124, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1124, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1124 cols1124 requiredD1124 requiredS1124
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1124_eq] at model
  exact MomentData.excluded1124 ds ss model
def rows1125 : List Int := [0,1,8,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1125 : List Int := [0,1,8,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1125 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1125 : List Int := [11,18,19,20,21,22,23,24,25,26,27,28,29,30,37]
theorem problem1125_eq : pairedProblem rows1125 cols1125 requiredD1125 requiredS1125 =
    MomentData.problem1125 := by rfl
theorem leaf1125 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1125++rows1125))
    (hc : (q.map Prod.snd).Perm (cols1125++cols1125))
    (hd : ∀ k ∈ requiredD1125, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1125, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1125 cols1125 requiredD1125 requiredS1125
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1125_eq] at model
  exact MomentData.excluded1125 ds ss model
def rows1126 : List Int := [0,5,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1126 : List Int := [0,5,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1126 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1126 : List Int := [9,16,17,18,19,20,21,22,23,24,25,26,27,28,35]
theorem problem1126_eq : pairedProblem rows1126 cols1126 requiredD1126 requiredS1126 =
    MomentData.problem1126 := by rfl
theorem leaf1126 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1126++rows1126))
    (hc : (q.map Prod.snd).Perm (cols1126++cols1126))
    (hd : ∀ k ∈ requiredD1126, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1126, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1126 cols1126 requiredD1126 requiredS1126
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1126_eq] at model
  exact MomentData.excluded1126 ds ss model
def rows1127 : List Int := [0,5,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1127 : List Int := [0,5,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1127 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1127 : List Int := [15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
theorem problem1127_eq : pairedProblem rows1127 cols1127 requiredD1127 requiredS1127 =
    MomentData.problem1127 := by rfl
theorem leaf1127 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1127++rows1127))
    (hc : (q.map Prod.snd).Perm (cols1127++cols1127))
    (hd : ∀ k ∈ requiredD1127, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1127, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1127 cols1127 requiredD1127 requiredS1127
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1127_eq] at model
  exact MomentData.excluded1127 ds ss model
def rows1128 : List Int := [0,6,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1128 : List Int := [0,6,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1128 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1128 : List Int := [9,16,17,18,19,20,21,22,23,24,25,26,27,28,35]
theorem problem1128_eq : pairedProblem rows1128 cols1128 requiredD1128 requiredS1128 =
    MomentData.problem1128 := by rfl
theorem leaf1128 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1128++rows1128))
    (hc : (q.map Prod.snd).Perm (cols1128++cols1128))
    (hd : ∀ k ∈ requiredD1128, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1128, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1128 cols1128 requiredD1128 requiredS1128
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1128_eq] at model
  exact MomentData.excluded1128 ds ss model
def rows1129 : List Int := [0,6,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1129 : List Int := [0,6,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1129 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1129 : List Int := [15,16,17,18,19,20,21,22,23,24,25,26,27,28,29]
theorem problem1129_eq : pairedProblem rows1129 cols1129 requiredD1129 requiredS1129 =
    MomentData.problem1129 := by rfl
theorem leaf1129 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1129++rows1129))
    (hc : (q.map Prod.snd).Perm (cols1129++cols1129))
    (hd : ∀ k ∈ requiredD1129, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1129, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1129 cols1129 requiredD1129 requiredS1129
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1129_eq] at model
  exact MomentData.excluded1129 ds ss model
def rows1130 : List Int := [0,7,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1130 : List Int := [0,7,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1130 : List Int := [-13,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,13]
def requiredS1130 : List Int := [9,16,17,18,19,20,21,22,23,24,25,26,27,28,35]
theorem problem1130_eq : pairedProblem rows1130 cols1130 requiredD1130 requiredS1130 =
    MomentData.problem1130 := by rfl
theorem leaf1130 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1130++rows1130))
    (hc : (q.map Prod.snd).Perm (cols1130++cols1130))
    (hd : ∀ k ∈ requiredD1130, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1130, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1130 cols1130 requiredD1130 requiredS1130
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1130_eq] at model
  exact MomentData.excluded1130 ds ss model
def rows1131 : List Int := [0,1,2,3,5,7,9,17,20,22,24,26,27,28,29]
def cols1131 : List Int := [0,1,2,3,5,7,9,17,20,22,24,26,27,28,29]
def requiredD1131 : List Int := [-12,-10,-8,-7,-6,-4,-2,0,2,4,6,7,8,10,12]
def requiredS1131 : List Int := [17,19,21,22,23,25,27,29,31,33,35,36,37,39,41]
theorem problem1131_eq : pairedProblem rows1131 cols1131 requiredD1131 requiredS1131 =
    MomentData.problem1131 := by rfl
theorem leaf1131 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1131++rows1131))
    (hc : (q.map Prod.snd).Perm (cols1131++cols1131))
    (hd : ∀ k ∈ requiredD1131, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1131, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1131 cols1131 requiredD1131 requiredS1131
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1131_eq] at model
  exact MomentData.excluded1131 ds ss model
def rows1132 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols1132 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1132 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1132 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45,48]
theorem problem1132_eq : pairedProblem rows1132 cols1132 requiredD1132 requiredS1132 =
    MomentData.problem1132 := by rfl
theorem leaf1132 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1132++rows1132))
    (hc : (q.map Prod.snd).Perm (cols1132++cols1132))
    (hd : ∀ k ∈ requiredD1132, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1132, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1132 cols1132 requiredD1132 requiredS1132
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1132_eq] at model
  exact MomentData.excluded1132 ds ss model
def rows1133 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols1133 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1133 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1133 : List Int := [12,15,18,21,24,27,29,30,33,36,39,42,45,48]
theorem problem1133_eq : pairedProblem rows1133 cols1133 requiredD1133 requiredS1133 =
    MomentData.problem1133 := by rfl
theorem leaf1133 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1133++rows1133))
    (hc : (q.map Prod.snd).Perm (cols1133++cols1133))
    (hd : ∀ k ∈ requiredD1133, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1133, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1133 cols1133 requiredD1133 requiredS1133
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1133_eq] at model
  exact MomentData.excluded1133 ds ss model
def rows1134 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols1134 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1134 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1134 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1134_eq : pairedProblem rows1134 cols1134 requiredD1134 requiredS1134 =
    MomentData.problem1134 := by rfl
theorem leaf1134 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1134++rows1134))
    (hc : (q.map Prod.snd).Perm (cols1134++cols1134))
    (hd : ∀ k ∈ requiredD1134, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1134, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1134 cols1134 requiredD1134 requiredS1134
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1134_eq] at model
  exact MomentData.excluded1134 ds ss model
def rows1135 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols1135 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1135 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1135 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem1135_eq : pairedProblem rows1135 cols1135 requiredD1135 requiredS1135 =
    MomentData.problem1135 := by rfl
theorem leaf1135 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1135++rows1135))
    (hc : (q.map Prod.snd).Perm (cols1135++cols1135))
    (hd : ∀ k ∈ requiredD1135, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1135, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1135 cols1135 requiredD1135 requiredS1135
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1135_eq] at model
  exact MomentData.excluded1135 ds ss model
def rows1136 : List Int := [0,1,2,3,12,13,14,15,16,17,21,26,27,28,29]
def cols1136 : List Int := [0,1,2,3,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1136 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1136 : List Int := [15,23,24,25,26,27,28,29,30,31,32,33,34,35,43]
theorem problem1136_eq : pairedProblem rows1136 cols1136 requiredD1136 requiredS1136 =
    MomentData.problem1136 := by rfl
theorem leaf1136 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1136++rows1136))
    (hc : (q.map Prod.snd).Perm (cols1136++cols1136))
    (hd : ∀ k ∈ requiredD1136, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1136, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1136 cols1136 requiredD1136 requiredS1136
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1136_eq] at model
  exact MomentData.excluded1136 ds ss model
def rows1137 : List Int := [0,1,2,3,12,13,14,15,16,17,21,26,27,28,29]
def cols1137 : List Int := [0,1,2,3,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1137 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1137 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1137_eq : pairedProblem rows1137 cols1137 requiredD1137 requiredS1137 =
    MomentData.problem1137 := by rfl
theorem leaf1137 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1137++rows1137))
    (hc : (q.map Prod.snd).Perm (cols1137++cols1137))
    (hd : ∀ k ∈ requiredD1137, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1137, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1137 cols1137 requiredD1137 requiredS1137
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1137_eq] at model
  exact MomentData.excluded1137 ds ss model
def rows1138 : List Int := [0,1,2,3,12,13,14,15,16,17,22,26,27,28,29]
def cols1138 : List Int := [0,1,2,3,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1138 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1138 : List Int := [15,23,24,25,26,27,28,29,30,31,32,33,34,35,43]
theorem problem1138_eq : pairedProblem rows1138 cols1138 requiredD1138 requiredS1138 =
    MomentData.problem1138 := by rfl
theorem leaf1138 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1138++rows1138))
    (hc : (q.map Prod.snd).Perm (cols1138++cols1138))
    (hd : ∀ k ∈ requiredD1138, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1138, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1138 cols1138 requiredD1138 requiredS1138
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1138_eq] at model
  exact MomentData.excluded1138 ds ss model
def rows1139 : List Int := [0,1,2,3,12,13,14,15,16,17,22,26,27,28,29]
def cols1139 : List Int := [0,1,2,3,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1139 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1139 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1139_eq : pairedProblem rows1139 cols1139 requiredD1139 requiredS1139 =
    MomentData.problem1139 := by rfl
theorem leaf1139 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1139++rows1139))
    (hc : (q.map Prod.snd).Perm (cols1139++cols1139))
    (hd : ∀ k ∈ requiredD1139, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1139, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1139 cols1139 requiredD1139 requiredS1139
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1139_eq] at model
  exact MomentData.excluded1139 ds ss model
def rows1140 : List Int := [0,1,2,3,12,13,14,15,16,17,22,26,27,28,29]
def cols1140 : List Int := [0,1,2,6,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1140 : List Int := [-13,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,15]
def requiredS1140 : List Int := [14,22,23,24,25,26,27,28,29,30,31,32,33,34,42]
theorem problem1140_eq : pairedProblem rows1140 cols1140 requiredD1140 requiredS1140 =
    MomentData.problem1140 := by rfl
theorem leaf1140 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1140++rows1140))
    (hc : (q.map Prod.snd).Perm (cols1140++cols1140))
    (hd : ∀ k ∈ requiredD1140, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1140, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1140 cols1140 requiredD1140 requiredS1140
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1140_eq] at model
  exact MomentData.excluded1140 ds ss model
def rows1141 : List Int := [0,1,2,6,11,12,13,14,15,16,25,26,27,28,29]
def cols1141 : List Int := [0,1,2,6,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1141 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1141 : List Int := [13,21,22,23,24,25,26,27,28,29,30,31,32,33,41]
theorem problem1141_eq : pairedProblem rows1141 cols1141 requiredD1141 requiredS1141 =
    MomentData.problem1141 := by rfl
theorem leaf1141 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1141++rows1141))
    (hc : (q.map Prod.snd).Perm (cols1141++cols1141))
    (hd : ∀ k ∈ requiredD1141, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1141, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1141 cols1141 requiredD1141 requiredS1141
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1141_eq] at model
  exact MomentData.excluded1141 ds ss model
def rows1142 : List Int := [0,1,2,7,11,12,13,14,15,16,25,26,27,28,29]
def cols1142 : List Int := [0,1,2,7,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1142 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1142 : List Int := [13,21,22,23,24,25,26,27,28,29,30,31,32,33,41]
theorem problem1142_eq : pairedProblem rows1142 cols1142 requiredD1142 requiredS1142 =
    MomentData.problem1142 := by rfl
theorem leaf1142 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1142++rows1142))
    (hc : (q.map Prod.snd).Perm (cols1142++cols1142))
    (hd : ∀ k ∈ requiredD1142, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1142, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1142 cols1142 requiredD1142 requiredS1142
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1142_eq] at model
  exact MomentData.excluded1142 ds ss model
def rows1143 : List Int := [0,1,2,7,11,12,13,14,15,16,25,26,27,28,29]
def cols1143 : List Int := [0,1,2,7,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1143 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1143 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1143_eq : pairedProblem rows1143 cols1143 requiredD1143 requiredS1143 =
    MomentData.problem1143 := by rfl
theorem leaf1143 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1143++rows1143))
    (hc : (q.map Prod.snd).Perm (cols1143++cols1143))
    (hd : ∀ k ∈ requiredD1143, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1143, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1143 cols1143 requiredD1143 requiredS1143
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1143_eq] at model
  exact MomentData.excluded1143 ds ss model
def rows1144 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1144 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1144 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1144 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44,47]
theorem problem1144_eq : pairedProblem rows1144 cols1144 requiredD1144 requiredS1144 =
    MomentData.problem1144 := by rfl
theorem leaf1144 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1144++rows1144))
    (hc : (q.map Prod.snd).Perm (cols1144++cols1144))
    (hd : ∀ k ∈ requiredD1144, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1144, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1144 cols1144 requiredD1144 requiredS1144
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1144_eq] at model
  exact MomentData.excluded1144 ds ss model
def rows1145 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1145 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1145 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1145 : List Int := [11,14,17,20,23,26,27,29,32,35,38,41,44,47]
theorem problem1145_eq : pairedProblem rows1145 cols1145 requiredD1145 requiredS1145 =
    MomentData.problem1145 := by rfl
theorem leaf1145 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1145++rows1145))
    (hc : (q.map Prod.snd).Perm (cols1145++cols1145))
    (hd : ∀ k ∈ requiredD1145, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1145, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1145 cols1145 requiredD1145 requiredS1145
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1145_eq] at model
  exact MomentData.excluded1145 ds ss model
def rows1146 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1146 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1146 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1146 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1146_eq : pairedProblem rows1146 cols1146 requiredD1146 requiredS1146 =
    MomentData.problem1146 := by rfl
theorem leaf1146 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1146++rows1146))
    (hc : (q.map Prod.snd).Perm (cols1146++cols1146))
    (hd : ∀ k ∈ requiredD1146, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1146, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1146 cols1146 requiredD1146 requiredS1146
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1146_eq] at model
  exact MomentData.excluded1146 ds ss model
def rows1147 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1147 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1147 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1147 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem1147_eq : pairedProblem rows1147 cols1147 requiredD1147 requiredS1147 =
    MomentData.problem1147 := by rfl
theorem leaf1147 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1147++rows1147))
    (hc : (q.map Prod.snd).Perm (cols1147++cols1147))
    (hd : ∀ k ∈ requiredD1147, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1147, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1147 cols1147 requiredD1147 requiredS1147
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1147_eq] at model
  exact MomentData.excluded1147 ds ss model
def rows1148 : List Int := [0,1,2,4,6,8,13,19,21,23,25,26,27,28,29]
def cols1148 : List Int := [0,1,2,4,6,8,13,19,21,23,25,26,27,28,29]
def requiredD1148 : List Int := [-12,-10,-8,-7,-6,-4,-2,0,2,4,6,7,8,10,12]
def requiredS1148 : List Int := [15,17,19,20,21,23,25,27,29,31,33,34,35,37,39]
theorem problem1148_eq : pairedProblem rows1148 cols1148 requiredD1148 requiredS1148 =
    MomentData.problem1148 := by rfl
theorem leaf1148 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1148++rows1148))
    (hc : (q.map Prod.snd).Perm (cols1148++cols1148))
    (hd : ∀ k ∈ requiredD1148, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1148, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1148 cols1148 requiredD1148 requiredS1148
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1148_eq] at model
  exact MomentData.excluded1148 ds ss model
def rows1149 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1149 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1149 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1149 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem1149_eq : pairedProblem rows1149 cols1149 requiredD1149 requiredS1149 =
    MomentData.problem1149 := by rfl
theorem leaf1149 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1149++rows1149))
    (hc : (q.map Prod.snd).Perm (cols1149++cols1149))
    (hd : ∀ k ∈ requiredD1149, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1149, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1149 cols1149 requiredD1149 requiredS1149
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1149_eq] at model
  exact MomentData.excluded1149 ds ss model
def rows1150 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1150 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1150 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1150 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem1150_eq : pairedProblem rows1150 cols1150 requiredD1150 requiredS1150 =
    MomentData.problem1150 := by rfl
theorem leaf1150 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1150++rows1150))
    (hc : (q.map Prod.snd).Perm (cols1150++cols1150))
    (hd : ∀ k ∈ requiredD1150, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1150, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1150 cols1150 requiredD1150 requiredS1150
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1150_eq] at model
  exact MomentData.excluded1150 ds ss model
def rows1151 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1151 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1151 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1151 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1151_eq : pairedProblem rows1151 cols1151 requiredD1151 requiredS1151 =
    MomentData.problem1151 := by rfl
theorem leaf1151 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1151++rows1151))
    (hc : (q.map Prod.snd).Perm (cols1151++cols1151))
    (hd : ∀ k ∈ requiredD1151, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1151, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1151 cols1151 requiredD1151 requiredS1151
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1151_eq] at model
  exact MomentData.excluded1151 ds ss model
#print axioms leaf1024
end Gardner.Kernel.MomentContexts
