import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows0 : List Int := [0,1,2,3,4,5,20,22,23,24,25,26,27,28,29]
def cols0 : List Int := [0,1,2,3,4,5,20,22,23,24,25,26,27,28,29]
def requiredD0 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS0 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem0_eq : pairedProblem rows0 cols0 requiredD0 requiredS0 =
    MomentData.problem0 := by rfl
theorem leaf0 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows0++rows0))
    (hc : (q.map Prod.snd).Perm (cols0++cols0))
    (hd : ∀ k ∈ requiredD0, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS0, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows0 cols0 requiredD0 requiredS0
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem0_eq] at model
  exact MomentData.excluded0 ds ss model
def rows1 : List Int := [0,1,2,3,4,18,21,22,23,24,25,26,27,28,29]
def cols1 : List Int := [0,1,2,3,4,18,21,22,23,24,25,26,27,28,29]
def requiredD1 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1_eq : pairedProblem rows1 cols1 requiredD1 requiredS1 =
    MomentData.problem1 := by rfl
theorem leaf1 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1++rows1))
    (hc : (q.map Prod.snd).Perm (cols1++cols1))
    (hd : ∀ k ∈ requiredD1, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1 cols1 requiredD1 requiredS1
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1_eq] at model
  exact MomentData.excluded1 ds ss model
def rows2 : List Int := [0,1,2,3,4,5,19,22,23,24,25,26,27,28,29]
def cols2 : List Int := [0,1,2,3,4,5,19,22,23,24,25,26,27,28,29]
def requiredD2 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem2_eq : pairedProblem rows2 cols2 requiredD2 requiredS2 =
    MomentData.problem2 := by rfl
theorem leaf2 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2++rows2))
    (hc : (q.map Prod.snd).Perm (cols2++cols2))
    (hd : ∀ k ∈ requiredD2, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2 cols2 requiredD2 requiredS2
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2_eq] at model
  exact MomentData.excluded2 ds ss model
def rows3 : List Int := [0,1,2,3,16,20,21,22,23,24,25,26,27,28,29]
def cols3 : List Int := [0,1,2,3,16,20,21,22,23,24,25,26,27,28,29]
def requiredD3 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS3 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem3_eq : pairedProblem rows3 cols3 requiredD3 requiredS3 =
    MomentData.problem3 := by rfl
theorem leaf3 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows3++rows3))
    (hc : (q.map Prod.snd).Perm (cols3++cols3))
    (hd : ∀ k ∈ requiredD3, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS3, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows3 cols3 requiredD3 requiredS3
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem3_eq] at model
  exact MomentData.excluded3 ds ss model
def rows4 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def cols4 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def requiredD4 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS4 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem4_eq : pairedProblem rows4 cols4 requiredD4 requiredS4 =
    MomentData.problem4 := by rfl
theorem leaf4 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows4++rows4))
    (hc : (q.map Prod.snd).Perm (cols4++cols4))
    (hd : ∀ k ∈ requiredD4, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS4, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows4 cols4 requiredD4 requiredS4
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem4_eq] at model
  exact MomentData.excluded4 ds ss model
def rows5 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def cols5 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def requiredD5 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS5 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem5_eq : pairedProblem rows5 cols5 requiredD5 requiredS5 =
    MomentData.problem5 := by rfl
theorem leaf5 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows5++rows5))
    (hc : (q.map Prod.snd).Perm (cols5++cols5))
    (hd : ∀ k ∈ requiredD5, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS5, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows5 cols5 requiredD5 requiredS5
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem5_eq] at model
  exact MomentData.excluded5 ds ss model
def rows6 : List Int := [0,1,2,3,4,5,18,22,23,24,25,26,27,28,29]
def cols6 : List Int := [0,1,2,3,4,5,18,22,23,24,25,26,27,28,29]
def requiredD6 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS6 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem6_eq : pairedProblem rows6 cols6 requiredD6 requiredS6 =
    MomentData.problem6 := by rfl
theorem leaf6 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows6++rows6))
    (hc : (q.map Prod.snd).Perm (cols6++cols6))
    (hd : ∀ k ∈ requiredD6, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS6, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows6 cols6 requiredD6 requiredS6
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem6_eq] at model
  exact MomentData.excluded6 ds ss model
def rows7 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def cols7 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def requiredD7 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS7 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem7_eq : pairedProblem rows7 cols7 requiredD7 requiredS7 =
    MomentData.problem7 := by rfl
theorem leaf7 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows7++rows7))
    (hc : (q.map Prod.snd).Perm (cols7++cols7))
    (hd : ∀ k ∈ requiredD7, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS7, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows7 cols7 requiredD7 requiredS7
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem7_eq] at model
  exact MomentData.excluded7 ds ss model
def rows8 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def cols8 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def requiredD8 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS8 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem8_eq : pairedProblem rows8 cols8 requiredD8 requiredS8 =
    MomentData.problem8 := by rfl
theorem leaf8 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows8++rows8))
    (hc : (q.map Prod.snd).Perm (cols8++cols8))
    (hd : ∀ k ∈ requiredD8, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS8, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows8 cols8 requiredD8 requiredS8
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem8_eq] at model
  exact MomentData.excluded8 ds ss model
def rows9 : List Int := [0,1,2,3,4,5,17,22,23,24,25,26,27,28,29]
def cols9 : List Int := [0,1,2,3,4,5,17,22,23,24,25,26,27,28,29]
def requiredD9 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS9 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem9_eq : pairedProblem rows9 cols9 requiredD9 requiredS9 =
    MomentData.problem9 := by rfl
theorem leaf9 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows9++rows9))
    (hc : (q.map Prod.snd).Perm (cols9++cols9))
    (hd : ∀ k ∈ requiredD9, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS9, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows9 cols9 requiredD9 requiredS9
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem9_eq] at model
  exact MomentData.excluded9 ds ss model
def rows10 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def cols10 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def requiredD10 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8]
def requiredS10 : List Int := [15,17,19,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem10_eq : pairedProblem rows10 cols10 requiredD10 requiredS10 =
    MomentData.problem10 := by rfl
theorem leaf10 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows10++rows10))
    (hc : (q.map Prod.snd).Perm (cols10++cols10))
    (hd : ∀ k ∈ requiredD10, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS10, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows10 cols10 requiredD10 requiredS10
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem10_eq] at model
  exact MomentData.excluded10 ds ss model
def rows11 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def cols11 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def requiredD11 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS11 : List Int := [17,19,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem11_eq : pairedProblem rows11 cols11 requiredD11 requiredS11 =
    MomentData.problem11 := by rfl
theorem leaf11 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows11++rows11))
    (hc : (q.map Prod.snd).Perm (cols11++cols11))
    (hd : ∀ k ∈ requiredD11, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS11, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows11 cols11 requiredD11 requiredS11
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem11_eq] at model
  exact MomentData.excluded11 ds ss model
def rows12 : List Int := [0,1,2,3,4,5,16,22,23,24,25,26,27,28,29]
def cols12 : List Int := [0,1,2,3,4,5,16,22,23,24,25,26,27,28,29]
def requiredD12 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS12 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem12_eq : pairedProblem rows12 cols12 requiredD12 requiredS12 =
    MomentData.problem12 := by rfl
theorem leaf12 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows12++rows12))
    (hc : (q.map Prod.snd).Perm (cols12++cols12))
    (hd : ∀ k ∈ requiredD12, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS12, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows12 cols12 requiredD12 requiredS12
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem12_eq] at model
  exact MomentData.excluded12 ds ss model
def rows13 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def cols13 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def requiredD13 : List Int := [-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7]
def requiredS13 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem13_eq : pairedProblem rows13 cols13 requiredD13 requiredS13 =
    MomentData.problem13 := by rfl
theorem leaf13 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows13++rows13))
    (hc : (q.map Prod.snd).Perm (cols13++cols13))
    (hd : ∀ k ∈ requiredD13, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS13, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows13 cols13 requiredD13 requiredS13
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem13_eq] at model
  exact MomentData.excluded13 ds ss model
def rows14 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def cols14 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def requiredD14 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS14 : List Int := [20,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem14_eq : pairedProblem rows14 cols14 requiredD14 requiredS14 =
    MomentData.problem14 := by rfl
theorem leaf14 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows14++rows14))
    (hc : (q.map Prod.snd).Perm (cols14++cols14))
    (hd : ∀ k ∈ requiredD14, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS14, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows14 cols14 requiredD14 requiredS14
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem14_eq] at model
  exact MomentData.excluded14 ds ss model
def rows15 : List Int := [0,1,2,3,4,5,14,22,23,24,25,26,27,28,29]
def cols15 : List Int := [0,1,2,3,4,5,14,22,23,24,25,26,27,28,29]
def requiredD15 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS15 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem15_eq : pairedProblem rows15 cols15 requiredD15 requiredS15 =
    MomentData.problem15 := by rfl
theorem leaf15 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows15++rows15))
    (hc : (q.map Prod.snd).Perm (cols15++cols15))
    (hd : ∀ k ∈ requiredD15, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS15, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows15 cols15 requiredD15 requiredS15
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem15_eq] at model
  exact MomentData.excluded15 ds ss model
def rows16 : List Int := [0,1,2,3,4,5,6,7,15,24,25,26,27,28,29]
def cols16 : List Int := [0,1,2,3,4,5,6,7,15,24,25,26,27,28,29]
def requiredD16 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS16 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem16_eq : pairedProblem rows16 cols16 requiredD16 requiredS16 =
    MomentData.problem16 := by rfl
theorem leaf16 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows16++rows16))
    (hc : (q.map Prod.snd).Perm (cols16++cols16))
    (hd : ∀ k ∈ requiredD16, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS16, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows16 cols16 requiredD16 requiredS16
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem16_eq] at model
  exact MomentData.excluded16 ds ss model
def rows17 : List Int := [0,1,2,3,4,5,6,7,14,24,25,26,27,28,29]
def cols17 : List Int := [0,1,2,3,4,5,6,7,14,24,25,26,27,28,29]
def requiredD17 : List Int := [-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7]
def requiredS17 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,38,40]
theorem problem17_eq : pairedProblem rows17 cols17 requiredD17 requiredS17 =
    MomentData.problem17 := by rfl
theorem leaf17 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows17++rows17))
    (hc : (q.map Prod.snd).Perm (cols17++cols17))
    (hd : ∀ k ∈ requiredD17, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS17, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows17 cols17 requiredD17 requiredS17
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem17_eq] at model
  exact MomentData.excluded17 ds ss model
def rows18 : List Int := [0,1,2,3,4,5,6,7,14,24,25,26,27,28,29]
def cols18 : List Int := [0,1,2,3,4,5,6,7,14,24,25,26,27,28,29]
def requiredD18 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS18 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,38]
theorem problem18_eq : pairedProblem rows18 cols18 requiredD18 requiredS18 =
    MomentData.problem18 := by rfl
theorem leaf18 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows18++rows18))
    (hc : (q.map Prod.snd).Perm (cols18++cols18))
    (hd : ∀ k ∈ requiredD18, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS18, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows18 cols18 requiredD18 requiredS18
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem18_eq] at model
  exact MomentData.excluded18 ds ss model
def rows19 : List Int := [0,1,2,3,4,5,6,7,13,24,25,26,27,28,29]
def cols19 : List Int := [0,1,2,3,4,5,6,7,13,24,25,26,27,28,29]
def requiredD19 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS19 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem19_eq : pairedProblem rows19 cols19 requiredD19 requiredS19 =
    MomentData.problem19 := by rfl
theorem leaf19 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows19++rows19))
    (hc : (q.map Prod.snd).Perm (cols19++cols19))
    (hd : ∀ k ∈ requiredD19, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS19, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows19 cols19 requiredD19 requiredS19
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem19_eq] at model
  exact MomentData.excluded19 ds ss model
def rows20 : List Int := [0,1,2,3,4,5,6,7,8,14,25,26,27,28,29]
def cols20 : List Int := [0,1,2,3,4,5,6,7,8,14,25,26,27,28,29]
def requiredD20 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8]
def requiredS20 : List Int := [25,27,28,29,30,31,32,33,34,35,36,37,39,41,43]
theorem problem20_eq : pairedProblem rows20 cols20 requiredD20 requiredS20 =
    MomentData.problem20 := by rfl
theorem leaf20 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows20++rows20))
    (hc : (q.map Prod.snd).Perm (cols20++cols20))
    (hd : ∀ k ∈ requiredD20, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS20, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows20 cols20 requiredD20 requiredS20
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem20_eq] at model
  exact MomentData.excluded20 ds ss model
def rows21 : List Int := [0,1,2,3,4,5,6,7,8,14,25,26,27,28,29]
def cols21 : List Int := [0,1,2,3,4,5,6,7,8,14,25,26,27,28,29]
def requiredD21 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS21 : List Int := [25,27,28,29,30,31,32,33,34,35,36,37,39,41]
theorem problem21_eq : pairedProblem rows21 cols21 requiredD21 requiredS21 =
    MomentData.problem21 := by rfl
theorem leaf21 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows21++rows21))
    (hc : (q.map Prod.snd).Perm (cols21++cols21))
    (hd : ∀ k ∈ requiredD21, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS21, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows21 cols21 requiredD21 requiredS21
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem21_eq] at model
  exact MomentData.excluded21 ds ss model
def rows22 : List Int := [0,1,2,3,4,5,6,7,12,24,25,26,27,28,29]
def cols22 : List Int := [0,1,2,3,4,5,6,7,12,24,25,26,27,28,29]
def requiredD22 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS22 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem22_eq : pairedProblem rows22 cols22 requiredD22 requiredS22 =
    MomentData.problem22 := by rfl
theorem leaf22 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows22++rows22))
    (hc : (q.map Prod.snd).Perm (cols22++cols22))
    (hd : ∀ k ∈ requiredD22, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS22, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows22 cols22 requiredD22 requiredS22
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem22_eq] at model
  exact MomentData.excluded22 ds ss model
def rows23 : List Int := [0,1,2,3,4,5,6,7,8,13,25,26,27,28,29]
def cols23 : List Int := [0,1,2,3,4,5,6,7,8,13,25,26,27,28,29]
def requiredD23 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS23 : List Int := [25,27,28,29,30,31,32,33,34,35,36,37,38,39,41]
theorem problem23_eq : pairedProblem rows23 cols23 requiredD23 requiredS23 =
    MomentData.problem23 := by rfl
theorem leaf23 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows23++rows23))
    (hc : (q.map Prod.snd).Perm (cols23++cols23))
    (hd : ∀ k ∈ requiredD23, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS23, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows23 cols23 requiredD23 requiredS23
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem23_eq] at model
  exact MomentData.excluded23 ds ss model
def rows24 : List Int := [0,1,2,3,4,5,6,7,8,13,25,26,27,28,29]
def cols24 : List Int := [0,1,2,3,4,5,6,7,8,13,25,26,27,28,29]
def requiredD24 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS24 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem24_eq : pairedProblem rows24 cols24 requiredD24 requiredS24 =
    MomentData.problem24 := by rfl
theorem leaf24 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows24++rows24))
    (hc : (q.map Prod.snd).Perm (cols24++cols24))
    (hd : ∀ k ∈ requiredD24, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS24, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows24 cols24 requiredD24 requiredS24
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem24_eq] at model
  exact MomentData.excluded24 ds ss model
def rows25 : List Int := [0,1,2,3,4,5,6,7,11,24,25,26,27,28,29]
def cols25 : List Int := [0,1,2,3,4,5,6,7,11,24,25,26,27,28,29]
def requiredD25 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS25 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem25_eq : pairedProblem rows25 cols25 requiredD25 requiredS25 =
    MomentData.problem25 := by rfl
theorem leaf25 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows25++rows25))
    (hc : (q.map Prod.snd).Perm (cols25++cols25))
    (hd : ∀ k ∈ requiredD25, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS25, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows25 cols25 requiredD25 requiredS25
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem25_eq] at model
  exact MomentData.excluded25 ds ss model
def rows26 : List Int := [0,1,2,3,4,5,6,7,8,12,25,26,27,28,29]
def cols26 : List Int := [0,1,2,3,4,5,6,7,8,12,25,26,27,28,29]
def requiredD26 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS26 : List Int := [25,27,28,29,30,31,32,33,34,35,36,37,38,39,41]
theorem problem26_eq : pairedProblem rows26 cols26 requiredD26 requiredS26 =
    MomentData.problem26 := by rfl
theorem leaf26 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows26++rows26))
    (hc : (q.map Prod.snd).Perm (cols26++cols26))
    (hd : ∀ k ∈ requiredD26, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS26, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows26 cols26 requiredD26 requiredS26
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem26_eq] at model
  exact MomentData.excluded26 ds ss model
def rows27 : List Int := [0,1,2,3,4,5,6,7,8,12,25,26,27,28,29]
def cols27 : List Int := [0,1,2,3,4,5,6,7,8,12,25,26,27,28,29]
def requiredD27 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS27 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem27_eq : pairedProblem rows27 cols27 requiredD27 requiredS27 =
    MomentData.problem27 := by rfl
theorem leaf27 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows27++rows27))
    (hc : (q.map Prod.snd).Perm (cols27++cols27))
    (hd : ∀ k ∈ requiredD27, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS27, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows27 cols27 requiredD27 requiredS27
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem27_eq] at model
  exact MomentData.excluded27 ds ss model
def rows28 : List Int := [0,1,2,3,4,5,6,7,8,9,13,26,27,28,29]
def cols28 : List Int := [0,1,2,3,4,5,6,7,8,9,13,26,27,28,29]
def requiredD28 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS28 : List Int := [28,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem28_eq : pairedProblem rows28 cols28 requiredD28 requiredS28 =
    MomentData.problem28 := by rfl
theorem leaf28 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows28++rows28))
    (hc : (q.map Prod.snd).Perm (cols28++cols28))
    (hd : ∀ k ∈ requiredD28, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS28, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows28 cols28 requiredD28 requiredS28
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem28_eq] at model
  exact MomentData.excluded28 ds ss model
def rows29 : List Int := [0,1,2,3,4,5,6,7,10,24,25,26,27,28,29]
def cols29 : List Int := [0,1,2,3,4,5,6,7,10,24,25,26,27,28,29]
def requiredD29 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS29 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem29_eq : pairedProblem rows29 cols29 requiredD29 requiredS29 =
    MomentData.problem29 := by rfl
theorem leaf29 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows29++rows29))
    (hc : (q.map Prod.snd).Perm (cols29++cols29))
    (hd : ∀ k ∈ requiredD29, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS29, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows29 cols29 requiredD29 requiredS29
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem29_eq] at model
  exact MomentData.excluded29 ds ss model
def rows30 : List Int := [0,1,2,3,4,5,6,7,8,11,25,26,27,28,29]
def cols30 : List Int := [0,1,2,3,4,5,6,7,8,11,25,26,27,28,29]
def requiredD30 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS30 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem30_eq : pairedProblem rows30 cols30 requiredD30 requiredS30 =
    MomentData.problem30 := by rfl
theorem leaf30 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows30++rows30))
    (hc : (q.map Prod.snd).Perm (cols30++cols30))
    (hd : ∀ k ∈ requiredD30, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS30, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows30 cols30 requiredD30 requiredS30
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem30_eq] at model
  exact MomentData.excluded30 ds ss model
def rows31 : List Int := [0,1,2,3,4,5,6,7,9,24,25,26,27,28,29]
def cols31 : List Int := [0,1,2,3,4,5,6,7,9,24,25,26,27,28,29]
def requiredD31 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS31 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem31_eq : pairedProblem rows31 cols31 requiredD31 requiredS31 =
    MomentData.problem31 := by rfl
theorem leaf31 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows31++rows31))
    (hc : (q.map Prod.snd).Perm (cols31++cols31))
    (hd : ∀ k ∈ requiredD31, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS31, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows31 cols31 requiredD31 requiredS31
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem31_eq] at model
  exact MomentData.excluded31 ds ss model
def rows32 : List Int := [0,1,2,3,4,13,20,22,23,24,25,26,27,28,29]
def cols32 : List Int := [0,1,2,3,4,13,20,22,23,24,25,26,27,28,29]
def requiredD32 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS32 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem32_eq : pairedProblem rows32 cols32 requiredD32 requiredS32 =
    MomentData.problem32 := by rfl
theorem leaf32 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows32++rows32))
    (hc : (q.map Prod.snd).Perm (cols32++cols32))
    (hd : ∀ k ∈ requiredD32, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS32, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows32 cols32 requiredD32 requiredS32
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem32_eq] at model
  exact MomentData.excluded32 ds ss model
def rows33 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def cols33 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def requiredD33 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS33 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem33_eq : pairedProblem rows33 cols33 requiredD33 requiredS33 =
    MomentData.problem33 := by rfl
theorem leaf33 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows33++rows33))
    (hc : (q.map Prod.snd).Perm (cols33++cols33))
    (hd : ∀ k ∈ requiredD33, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS33, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows33 cols33 requiredD33 requiredS33
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem33_eq] at model
  exact MomentData.excluded33 ds ss model
def rows34 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def cols34 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def requiredD34 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS34 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem34_eq : pairedProblem rows34 cols34 requiredD34 requiredS34 =
    MomentData.problem34 := by rfl
theorem leaf34 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows34++rows34))
    (hc : (q.map Prod.snd).Perm (cols34++cols34))
    (hd : ∀ k ∈ requiredD34, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS34, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows34 cols34 requiredD34 requiredS34
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem34_eq] at model
  exact MomentData.excluded34 ds ss model
def rows35 : List Int := [0,1,2,3,4,5,13,21,23,24,25,26,27,28,29]
def cols35 : List Int := [0,1,2,3,4,5,13,21,23,24,25,26,27,28,29]
def requiredD35 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS35 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem35_eq : pairedProblem rows35 cols35 requiredD35 requiredS35 =
    MomentData.problem35 := by rfl
theorem leaf35 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows35++rows35))
    (hc : (q.map Prod.snd).Perm (cols35++cols35))
    (hd : ∀ k ∈ requiredD35, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS35, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows35 cols35 requiredD35 requiredS35
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem35_eq] at model
  exact MomentData.excluded35 ds ss model
def rows36 : List Int := [0,1,2,3,4,5,6,14,22,24,25,26,27,28,29]
def cols36 : List Int := [0,1,2,3,4,5,6,14,22,24,25,26,27,28,29]
def requiredD36 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS36 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem36_eq : pairedProblem rows36 cols36 requiredD36 requiredS36 =
    MomentData.problem36 := by rfl
theorem leaf36 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows36++rows36))
    (hc : (q.map Prod.snd).Perm (cols36++cols36))
    (hd : ∀ k ∈ requiredD36, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS36, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows36 cols36 requiredD36 requiredS36
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem36_eq] at model
  exact MomentData.excluded36 ds ss model
def rows37 : List Int := [0,1,2,3,12,18,21,22,23,24,25,26,27,28,29]
def cols37 : List Int := [0,1,2,3,12,18,21,22,23,24,25,26,27,28,29]
def requiredD37 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS37 : List Int := [15,18,19,20,21,22,23,24,25,26,27,28,29,30,33]
theorem problem37_eq : pairedProblem rows37 cols37 requiredD37 requiredS37 =
    MomentData.problem37 := by rfl
theorem leaf37 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows37++rows37))
    (hc : (q.map Prod.snd).Perm (cols37++cols37))
    (hd : ∀ k ∈ requiredD37, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS37, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows37 cols37 requiredD37 requiredS37
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem37_eq] at model
  exact MomentData.excluded37 ds ss model
def rows38 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def cols38 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def requiredD38 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS38 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem38_eq : pairedProblem rows38 cols38 requiredD38 requiredS38 =
    MomentData.problem38 := by rfl
theorem leaf38 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows38++rows38))
    (hc : (q.map Prod.snd).Perm (cols38++cols38))
    (hd : ∀ k ∈ requiredD38, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS38, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows38 cols38 requiredD38 requiredS38
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem38_eq] at model
  exact MomentData.excluded38 ds ss model
def rows39 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def cols39 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def requiredD39 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS39 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem39_eq : pairedProblem rows39 cols39 requiredD39 requiredS39 =
    MomentData.problem39 := by rfl
theorem leaf39 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows39++rows39))
    (hc : (q.map Prod.snd).Perm (cols39++cols39))
    (hd : ∀ k ∈ requiredD39, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS39, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows39 cols39 requiredD39 requiredS39
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem39_eq] at model
  exact MomentData.excluded39 ds ss model
def rows40 : List Int := [0,1,2,3,4,5,14,20,23,24,25,26,27,28,29]
def cols40 : List Int := [0,1,2,3,4,5,14,20,23,24,25,26,27,28,29]
def requiredD40 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS40 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem40_eq : pairedProblem rows40 cols40 requiredD40 requiredS40 =
    MomentData.problem40 := by rfl
theorem leaf40 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows40++rows40))
    (hc : (q.map Prod.snd).Perm (cols40++cols40))
    (hd : ∀ k ∈ requiredD40, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS40, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows40 cols40 requiredD40 requiredS40
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem40_eq] at model
  exact MomentData.excluded40 ds ss model
def rows41 : List Int := [0,1,2,3,4,5,6,15,21,24,25,26,27,28,29]
def cols41 : List Int := [0,1,2,3,4,5,6,15,21,24,25,26,27,28,29]
def requiredD41 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS41 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem41_eq : pairedProblem rows41 cols41 requiredD41 requiredS41 =
    MomentData.problem41 := by rfl
theorem leaf41 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows41++rows41))
    (hc : (q.map Prod.snd).Perm (cols41++cols41))
    (hd : ∀ k ∈ requiredD41, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS41, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows41 cols41 requiredD41 requiredS41
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem41_eq] at model
  exact MomentData.excluded41 ds ss model
def rows42 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def cols42 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def requiredD42 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS42 : List Int := [15,18,19,20,21,22,23,24,25,26,27,28,29,30,33]
theorem problem42_eq : pairedProblem rows42 cols42 requiredD42 requiredS42 =
    MomentData.problem42 := by rfl
theorem leaf42 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows42++rows42))
    (hc : (q.map Prod.snd).Perm (cols42++cols42))
    (hd : ∀ k ∈ requiredD42, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS42, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows42 cols42 requiredD42 requiredS42
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem42_eq] at model
  exact MomentData.excluded42 ds ss model
def rows43 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def cols43 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def requiredD43 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS43 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem43_eq : pairedProblem rows43 cols43 requiredD43 requiredS43 =
    MomentData.problem43 := by rfl
theorem leaf43 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows43++rows43))
    (hc : (q.map Prod.snd).Perm (cols43++cols43))
    (hd : ∀ k ∈ requiredD43, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS43, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows43 cols43 requiredD43 requiredS43
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem43_eq] at model
  exact MomentData.excluded43 ds ss model
def rows44 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def cols44 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def requiredD44 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS44 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem44_eq : pairedProblem rows44 cols44 requiredD44 requiredS44 =
    MomentData.problem44 := by rfl
theorem leaf44 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows44++rows44))
    (hc : (q.map Prod.snd).Perm (cols44++cols44))
    (hd : ∀ k ∈ requiredD44, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS44, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows44 cols44 requiredD44 requiredS44
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem44_eq] at model
  exact MomentData.excluded44 ds ss model
def rows45 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def cols45 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def requiredD45 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS45 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem45_eq : pairedProblem rows45 cols45 requiredD45 requiredS45 =
    MomentData.problem45 := by rfl
theorem leaf45 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows45++rows45))
    (hc : (q.map Prod.snd).Perm (cols45++cols45))
    (hd : ∀ k ∈ requiredD45, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS45, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows45 cols45 requiredD45 requiredS45
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem45_eq] at model
  exact MomentData.excluded45 ds ss model
def rows46 : List Int := [0,1,2,3,4,5,14,19,23,24,25,26,27,28,29]
def cols46 : List Int := [0,1,2,3,4,5,14,19,23,24,25,26,27,28,29]
def requiredD46 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS46 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem46_eq : pairedProblem rows46 cols46 requiredD46 requiredS46 =
    MomentData.problem46 := by rfl
theorem leaf46 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows46++rows46))
    (hc : (q.map Prod.snd).Perm (cols46++cols46))
    (hd : ∀ k ∈ requiredD46, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS46, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows46 cols46 requiredD46 requiredS46
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem46_eq] at model
  exact MomentData.excluded46 ds ss model
def rows47 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def cols47 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def requiredD47 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS47 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem47_eq : pairedProblem rows47 cols47 requiredD47 requiredS47 =
    MomentData.problem47 := by rfl
theorem leaf47 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows47++rows47))
    (hc : (q.map Prod.snd).Perm (cols47++cols47))
    (hd : ∀ k ∈ requiredD47, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS47, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows47 cols47 requiredD47 requiredS47
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem47_eq] at model
  exact MomentData.excluded47 ds ss model
def rows48 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def cols48 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def requiredD48 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS48 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem48_eq : pairedProblem rows48 cols48 requiredD48 requiredS48 =
    MomentData.problem48 := by rfl
theorem leaf48 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows48++rows48))
    (hc : (q.map Prod.snd).Perm (cols48++cols48))
    (hd : ∀ k ∈ requiredD48, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS48, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows48 cols48 requiredD48 requiredS48
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem48_eq] at model
  exact MomentData.excluded48 ds ss model
def rows49 : List Int := [0,1,2,3,4,5,14,18,23,24,25,26,27,28,29]
def cols49 : List Int := [0,1,2,3,4,5,14,18,23,24,25,26,27,28,29]
def requiredD49 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS49 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem49_eq : pairedProblem rows49 cols49 requiredD49 requiredS49 =
    MomentData.problem49 := by rfl
theorem leaf49 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows49++rows49))
    (hc : (q.map Prod.snd).Perm (cols49++cols49))
    (hd : ∀ k ∈ requiredD49, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS49, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows49 cols49 requiredD49 requiredS49
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem49_eq] at model
  exact MomentData.excluded49 ds ss model
def rows50 : List Int := [0,1,2,3,4,10,17,22,23,24,25,26,27,28,29]
def cols50 : List Int := [0,1,2,3,4,10,17,22,23,24,25,26,27,28,29]
def requiredD50 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS50 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem50_eq : pairedProblem rows50 cols50 requiredD50 requiredS50 =
    MomentData.problem50 := by rfl
theorem leaf50 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows50++rows50))
    (hc : (q.map Prod.snd).Perm (cols50++cols50))
    (hd : ∀ k ∈ requiredD50, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS50, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows50 cols50 requiredD50 requiredS50
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem50_eq] at model
  exact MomentData.excluded50 ds ss model
def rows51 : List Int := [0,1,2,3,4,5,11,18,23,24,25,26,27,28,29]
def cols51 : List Int := [0,1,2,3,4,5,11,18,23,24,25,26,27,28,29]
def requiredD51 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS51 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem51_eq : pairedProblem rows51 cols51 requiredD51 requiredS51 =
    MomentData.problem51 := by rfl
theorem leaf51 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows51++rows51))
    (hc : (q.map Prod.snd).Perm (cols51++cols51))
    (hd : ∀ k ∈ requiredD51, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS51, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows51 cols51 requiredD51 requiredS51
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem51_eq] at model
  exact MomentData.excluded51 ds ss model
def rows52 : List Int := [0,1,2,3,4,5,6,12,19,24,25,26,27,28,29]
def cols52 : List Int := [0,1,2,3,4,5,6,12,19,24,25,26,27,28,29]
def requiredD52 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS52 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem52_eq : pairedProblem rows52 cols52 requiredD52 requiredS52 =
    MomentData.problem52 := by rfl
theorem leaf52 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows52++rows52))
    (hc : (q.map Prod.snd).Perm (cols52++cols52))
    (hd : ∀ k ∈ requiredD52, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS52, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows52 cols52 requiredD52 requiredS52
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem52_eq] at model
  exact MomentData.excluded52 ds ss model
def rows53 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def cols53 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def requiredD53 : List Int := [-13,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,13]
def requiredS53 : List Int := [18,20,22,23,24,26,27,28,29,30,32,33,34,36,38]
theorem problem53_eq : pairedProblem rows53 cols53 requiredD53 requiredS53 =
    MomentData.problem53 := by rfl
theorem leaf53 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows53++rows53))
    (hc : (q.map Prod.snd).Perm (cols53++cols53))
    (hd : ∀ k ∈ requiredD53, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS53, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows53 cols53 requiredD53 requiredS53
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem53_eq] at model
  exact MomentData.excluded53 ds ss model
def rows54 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def cols54 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def requiredD54 : List Int := [-10,-8,-6,-5,-4,-2,-1,0,1,2,4,5,6,8,10]
def requiredS54 : List Int := [15,19,21,23,25,26,27,28,29,30,31,33,35,37,41]
theorem problem54_eq : pairedProblem rows54 cols54 requiredD54 requiredS54 =
    MomentData.problem54 := by rfl
theorem leaf54 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows54++rows54))
    (hc : (q.map Prod.snd).Perm (cols54++cols54))
    (hd : ∀ k ∈ requiredD54, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS54, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows54 cols54 requiredD54 requiredS54
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem54_eq] at model
  exact MomentData.excluded54 ds ss model
def rows55 : List Int := [0,1,2,3,4,5,6,11,19,24,25,26,27,28,29]
def cols55 : List Int := [0,1,2,3,4,5,6,11,19,24,25,26,27,28,29]
def requiredD55 : List Int := [-13,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,13]
def requiredS55 : List Int := [20,22,24,25,26,28,29,30,31,32,34,35,36,38,40]
theorem problem55_eq : pairedProblem rows55 cols55 requiredD55 requiredS55 =
    MomentData.problem55 := by rfl
theorem leaf55 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows55++rows55))
    (hc : (q.map Prod.snd).Perm (cols55++cols55))
    (hd : ∀ k ∈ requiredD55, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS55, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows55 cols55 requiredD55 requiredS55
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem55_eq] at model
  exact MomentData.excluded55 ds ss model
def rows56 : List Int := [0,1,2,3,4,5,6,11,19,24,25,26,27,28,29]
def cols56 : List Int := [0,1,2,3,4,5,6,11,19,24,25,26,27,28,29]
def requiredD56 : List Int := [-10,-8,-6,-5,-4,-2,-1,0,1,2,4,5,6,8,10]
def requiredS56 : List Int := [17,21,23,25,27,28,29,30,31,32,33,35,37,39,43]
theorem problem56_eq : pairedProblem rows56 cols56 requiredD56 requiredS56 =
    MomentData.problem56 := by rfl
theorem leaf56 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows56++rows56))
    (hc : (q.map Prod.snd).Perm (cols56++cols56))
    (hd : ∀ k ∈ requiredD56, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS56, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows56 cols56 requiredD56 requiredS56
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem56_eq] at model
  exact MomentData.excluded56 ds ss model
def rows57 : List Int := [0,1,2,3,4,5,14,17,23,24,25,26,27,28,29]
def cols57 : List Int := [0,1,2,3,4,5,14,17,23,24,25,26,27,28,29]
def requiredD57 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS57 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem57_eq : pairedProblem rows57 cols57 requiredD57 requiredS57 =
    MomentData.problem57 := by rfl
theorem leaf57 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows57++rows57))
    (hc : (q.map Prod.snd).Perm (cols57++cols57))
    (hd : ∀ k ∈ requiredD57, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS57, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows57 cols57 requiredD57 requiredS57
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem57_eq] at model
  exact MomentData.excluded57 ds ss model
def rows58 : List Int := [0,1,2,3,4,11,16,22,23,24,25,26,27,28,29]
def cols58 : List Int := [0,1,2,3,4,11,16,22,23,24,25,26,27,28,29]
def requiredD58 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS58 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem58_eq : pairedProblem rows58 cols58 requiredD58 requiredS58 =
    MomentData.problem58 := by rfl
theorem leaf58 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows58++rows58))
    (hc : (q.map Prod.snd).Perm (cols58++cols58))
    (hd : ∀ k ∈ requiredD58, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS58, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows58 cols58 requiredD58 requiredS58
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem58_eq] at model
  exact MomentData.excluded58 ds ss model
def rows59 : List Int := [0,1,2,3,4,5,12,17,23,24,25,26,27,28,29]
def cols59 : List Int := [0,1,2,3,4,5,12,17,23,24,25,26,27,28,29]
def requiredD59 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS59 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem59_eq : pairedProblem rows59 cols59 requiredD59 requiredS59 =
    MomentData.problem59 := by rfl
theorem leaf59 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows59++rows59))
    (hc : (q.map Prod.snd).Perm (cols59++cols59))
    (hd : ∀ k ∈ requiredD59, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS59, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows59 cols59 requiredD59 requiredS59
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem59_eq] at model
  exact MomentData.excluded59 ds ss model
def rows60 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def cols60 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def requiredD60 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS60 : List Int := [14,18,20,22,23,24,25,26,27,28,29,30,32,34,38]
theorem problem60_eq : pairedProblem rows60 cols60 requiredD60 requiredS60 =
    MomentData.problem60 := by rfl
theorem leaf60 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows60++rows60))
    (hc : (q.map Prod.snd).Perm (cols60++cols60))
    (hd : ∀ k ∈ requiredD60, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS60, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows60 cols60 requiredD60 requiredS60
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem60_eq] at model
  exact MomentData.excluded60 ds ss model
def rows61 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def cols61 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def requiredD61 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS61 : List Int := [16,18,20,22,23,24,25,26,27,28,29,30,32,34,36]
theorem problem61_eq : pairedProblem rows61 cols61 requiredD61 requiredS61 =
    MomentData.problem61 := by rfl
theorem leaf61 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows61++rows61))
    (hc : (q.map Prod.snd).Perm (cols61++cols61))
    (hd : ∀ k ∈ requiredD61, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS61, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows61 cols61 requiredD61 requiredS61
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem61_eq] at model
  exact MomentData.excluded61 ds ss model
def rows62 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols62 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD62 : List Int := [-12,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,12]
def requiredS62 : List Int := [19,21,22,23,25,26,27,28,29,30,31,33,34,35,37]
theorem problem62_eq : pairedProblem rows62 cols62 requiredD62 requiredS62 =
    MomentData.problem62 := by rfl
theorem leaf62 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows62++rows62))
    (hc : (q.map Prod.snd).Perm (cols62++cols62))
    (hd : ∀ k ∈ requiredD62, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS62, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows62 cols62 requiredD62 requiredS62
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem62_eq] at model
  exact MomentData.excluded62 ds ss model
def rows63 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols63 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD63 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS63 : List Int := [16,20,22,24,25,26,27,28,29,30,31,32,34,36,40]
theorem problem63_eq : pairedProblem rows63 cols63 requiredD63 requiredS63 =
    MomentData.problem63 := by rfl
theorem leaf63 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows63++rows63))
    (hc : (q.map Prod.snd).Perm (cols63++cols63))
    (hd : ∀ k ∈ requiredD63, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS63, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows63 cols63 requiredD63 requiredS63
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem63_eq] at model
  exact MomentData.excluded63 ds ss model
def rows64 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols64 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD64 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS64 : List Int := [18,20,22,24,25,26,27,28,29,30,31,32,34,36,38]
theorem problem64_eq : pairedProblem rows64 cols64 requiredD64 requiredS64 =
    MomentData.problem64 := by rfl
theorem leaf64 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows64++rows64))
    (hc : (q.map Prod.snd).Perm (cols64++cols64))
    (hd : ∀ k ∈ requiredD64, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS64, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows64 cols64 requiredD64 requiredS64
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem64_eq] at model
  exact MomentData.excluded64 ds ss model
def rows65 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols65 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD65 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS65 : List Int := [19,21,23,24,25,26,27,28,29,30,31,32,33,35,37]
theorem problem65_eq : pairedProblem rows65 cols65 requiredD65 requiredS65 =
    MomentData.problem65 := by rfl
theorem leaf65 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows65++rows65))
    (hc : (q.map Prod.snd).Perm (cols65++cols65))
    (hd : ∀ k ∈ requiredD65, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS65, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows65 cols65 requiredD65 requiredS65
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem65_eq] at model
  exact MomentData.excluded65 ds ss model
def rows66 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def cols66 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def requiredD66 : List Int := [-12,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,12]
def requiredS66 : List Int := [21,23,24,25,27,28,29,30,31,32,33,35,36,37,39]
theorem problem66_eq : pairedProblem rows66 cols66 requiredD66 requiredS66 =
    MomentData.problem66 := by rfl
theorem leaf66 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows66++rows66))
    (hc : (q.map Prod.snd).Perm (cols66++cols66))
    (hd : ∀ k ∈ requiredD66, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS66, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows66 cols66 requiredD66 requiredS66
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem66_eq] at model
  exact MomentData.excluded66 ds ss model
def rows67 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def cols67 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def requiredD67 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS67 : List Int := [18,22,24,26,27,28,29,30,31,32,33,34,36,38,42]
theorem problem67_eq : pairedProblem rows67 cols67 requiredD67 requiredS67 =
    MomentData.problem67 := by rfl
theorem leaf67 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows67++rows67))
    (hc : (q.map Prod.snd).Perm (cols67++cols67))
    (hd : ∀ k ∈ requiredD67, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS67, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows67 cols67 requiredD67 requiredS67
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem67_eq] at model
  exact MomentData.excluded67 ds ss model
def rows68 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def cols68 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def requiredD68 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS68 : List Int := [20,22,24,26,27,28,29,30,31,32,33,34,36,38,40]
theorem problem68_eq : pairedProblem rows68 cols68 requiredD68 requiredS68 =
    MomentData.problem68 := by rfl
theorem leaf68 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows68++rows68))
    (hc : (q.map Prod.snd).Perm (cols68++cols68))
    (hd : ∀ k ∈ requiredD68, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS68, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows68 cols68 requiredD68 requiredS68
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem68_eq] at model
  exact MomentData.excluded68 ds ss model
def rows69 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def cols69 : List Int := [0,1,2,3,4,5,6,12,18,24,25,26,27,28,29]
def requiredD69 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS69 : List Int := [21,23,25,26,27,28,29,30,31,32,33,34,35,37,39]
theorem problem69_eq : pairedProblem rows69 cols69 requiredD69 requiredS69 =
    MomentData.problem69 := by rfl
theorem leaf69 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows69++rows69))
    (hc : (q.map Prod.snd).Perm (cols69++cols69))
    (hd : ∀ k ∈ requiredD69, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS69, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows69 cols69 requiredD69 requiredS69
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem69_eq] at model
  exact MomentData.excluded69 ds ss model
def rows70 : List Int := [0,1,2,3,4,5,6,7,13,19,25,26,27,28,29]
def cols70 : List Int := [0,1,2,3,4,5,6,7,13,19,25,26,27,28,29]
def requiredD70 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS70 : List Int := [20,24,26,28,29,30,31,32,33,34,35,36,38,40,44]
theorem problem70_eq : pairedProblem rows70 cols70 requiredD70 requiredS70 =
    MomentData.problem70 := by rfl
theorem leaf70 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows70++rows70))
    (hc : (q.map Prod.snd).Perm (cols70++cols70))
    (hd : ∀ k ∈ requiredD70, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS70, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows70 cols70 requiredD70 requiredS70
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem70_eq] at model
  exact MomentData.excluded70 ds ss model
def rows71 : List Int := [0,1,2,3,4,5,6,7,13,19,25,26,27,28,29]
def cols71 : List Int := [0,1,2,3,4,5,6,7,13,19,25,26,27,28,29]
def requiredD71 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS71 : List Int := [22,24,26,28,29,30,31,32,33,34,35,36,38,40,42]
theorem problem71_eq : pairedProblem rows71 cols71 requiredD71 requiredS71 =
    MomentData.problem71 := by rfl
theorem leaf71 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows71++rows71))
    (hc : (q.map Prod.snd).Perm (cols71++cols71))
    (hd : ∀ k ∈ requiredD71, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS71, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows71 cols71 requiredD71 requiredS71
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem71_eq] at model
  exact MomentData.excluded71 ds ss model
def rows72 : List Int := [0,1,2,3,4,5,10,17,23,24,25,26,27,28,29]
def cols72 : List Int := [0,1,2,3,4,5,10,17,23,24,25,26,27,28,29]
def requiredD72 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS72 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem72_eq : pairedProblem rows72 cols72 requiredD72 requiredS72 =
    MomentData.problem72 := by rfl
theorem leaf72 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows72++rows72))
    (hc : (q.map Prod.snd).Perm (cols72++cols72))
    (hd : ∀ k ∈ requiredD72, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS72, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows72 cols72 requiredD72 requiredS72
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem72_eq] at model
  exact MomentData.excluded72 ds ss model
def rows73 : List Int := [0,1,2,3,4,5,6,11,18,24,25,26,27,28,29]
def cols73 : List Int := [0,1,2,3,4,5,6,11,18,24,25,26,27,28,29]
def requiredD73 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS73 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem73_eq : pairedProblem rows73 cols73 requiredD73 requiredS73 =
    MomentData.problem73 := by rfl
theorem leaf73 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows73++rows73))
    (hc : (q.map Prod.snd).Perm (cols73++cols73))
    (hd : ∀ k ∈ requiredD73, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS73, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows73 cols73 requiredD73 requiredS73
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem73_eq] at model
  exact MomentData.excluded73 ds ss model
def rows74 : List Int := [0,1,2,3,4,5,6,7,12,19,25,26,27,28,29]
def cols74 : List Int := [0,1,2,3,4,5,6,7,12,19,25,26,27,28,29]
def requiredD74 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS74 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem74_eq : pairedProblem rows74 cols74 requiredD74 requiredS74 =
    MomentData.problem74 := by rfl
theorem leaf74 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows74++rows74))
    (hc : (q.map Prod.snd).Perm (cols74++cols74))
    (hd : ∀ k ∈ requiredD74, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS74, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows74 cols74 requiredD74 requiredS74
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem74_eq] at model
  exact MomentData.excluded74 ds ss model
def rows75 : List Int := [0,1,2,3,4,5,6,12,17,24,25,26,27,28,29]
def cols75 : List Int := [0,1,2,3,4,5,6,12,17,24,25,26,27,28,29]
def requiredD75 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS75 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem75_eq : pairedProblem rows75 cols75 requiredD75 requiredS75 =
    MomentData.problem75 := by rfl
theorem leaf75 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows75++rows75))
    (hc : (q.map Prod.snd).Perm (cols75++cols75))
    (hd : ∀ k ∈ requiredD75, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS75, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows75 cols75 requiredD75 requiredS75
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem75_eq] at model
  exact MomentData.excluded75 ds ss model
def rows76 : List Int := [0,1,2,3,4,5,6,7,13,18,25,26,27,28,29]
def cols76 : List Int := [0,1,2,3,4,5,6,7,13,18,25,26,27,28,29]
def requiredD76 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS76 : List Int := [22,24,26,27,28,29,30,31,32,33,34,35,36,38,40]
theorem problem76_eq : pairedProblem rows76 cols76 requiredD76 requiredS76 =
    MomentData.problem76 := by rfl
theorem leaf76 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows76++rows76))
    (hc : (q.map Prod.snd).Perm (cols76++cols76))
    (hd : ∀ k ∈ requiredD76, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS76, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows76 cols76 requiredD76 requiredS76
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem76_eq] at model
  exact MomentData.excluded76 ds ss model
def rows77 : List Int := [0,1,2,3,4,5,7,15,23,24,25,26,27,28,29]
def cols77 : List Int := [0,1,2,3,4,5,7,15,23,24,25,26,27,28,29]
def requiredD77 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS77 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem77_eq : pairedProblem rows77 cols77 requiredD77 requiredS77 =
    MomentData.problem77 := by rfl
theorem leaf77 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows77++rows77))
    (hc : (q.map Prod.snd).Perm (cols77++cols77))
    (hd : ∀ k ∈ requiredD77, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS77, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows77 cols77 requiredD77 requiredS77
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem77_eq] at model
  exact MomentData.excluded77 ds ss model
def rows78 : List Int := [0,1,2,3,4,5,6,8,16,24,25,26,27,28,29]
def cols78 : List Int := [0,1,2,3,4,5,6,8,16,24,25,26,27,28,29]
def requiredD78 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS78 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem78_eq : pairedProblem rows78 cols78 requiredD78 requiredS78 =
    MomentData.problem78 := by rfl
theorem leaf78 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows78++rows78))
    (hc : (q.map Prod.snd).Perm (cols78++cols78))
    (hd : ∀ k ∈ requiredD78, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS78, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows78 cols78 requiredD78 requiredS78
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem78_eq] at model
  exact MomentData.excluded78 ds ss model
def rows79 : List Int := [0,1,2,3,4,5,6,12,15,24,25,26,27,28,29]
def cols79 : List Int := [0,1,2,3,4,5,6,12,15,24,25,26,27,28,29]
def requiredD79 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS79 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem79_eq : pairedProblem rows79 cols79 requiredD79 requiredS79 =
    MomentData.problem79 := by rfl
theorem leaf79 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows79++rows79))
    (hc : (q.map Prod.snd).Perm (cols79++cols79))
    (hd : ∀ k ∈ requiredD79, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS79, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows79 cols79 requiredD79 requiredS79
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem79_eq] at model
  exact MomentData.excluded79 ds ss model
def rows80 : List Int := [0,1,2,3,4,5,6,11,15,24,25,26,27,28,29]
def cols80 : List Int := [0,1,2,3,4,5,6,11,15,24,25,26,27,28,29]
def requiredD80 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS80 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem80_eq : pairedProblem rows80 cols80 requiredD80 requiredS80 =
    MomentData.problem80 := by rfl
theorem leaf80 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows80++rows80))
    (hc : (q.map Prod.snd).Perm (cols80++cols80))
    (hd : ∀ k ∈ requiredD80, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS80, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows80 cols80 requiredD80 requiredS80
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem80_eq] at model
  exact MomentData.excluded80 ds ss model
def rows81 : List Int := [0,1,2,3,4,5,6,7,12,16,25,26,27,28,29]
def cols81 : List Int := [0,1,2,3,4,5,6,7,12,16,25,26,27,28,29]
def requiredD81 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS81 : List Int := [23,26,27,28,29,30,31,32,33,34,35,36,37,38,41]
theorem problem81_eq : pairedProblem rows81 cols81 requiredD81 requiredS81 =
    MomentData.problem81 := by rfl
theorem leaf81 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows81++rows81))
    (hc : (q.map Prod.snd).Perm (cols81++cols81))
    (hd : ∀ k ∈ requiredD81, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS81, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows81 cols81 requiredD81 requiredS81
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem81_eq] at model
  exact MomentData.excluded81 ds ss model
def rows82 : List Int := [0,1,2,3,4,5,6,7,12,16,25,26,27,28,29]
def cols82 : List Int := [0,1,2,3,4,5,6,7,12,16,25,26,27,28,29]
def requiredD82 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS82 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem82_eq : pairedProblem rows82 cols82 requiredD82 requiredS82 =
    MomentData.problem82 := by rfl
theorem leaf82 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows82++rows82))
    (hc : (q.map Prod.snd).Perm (cols82++cols82))
    (hd : ∀ k ∈ requiredD82, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS82, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows82 cols82 requiredD82 requiredS82
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem82_eq] at model
  exact MomentData.excluded82 ds ss model
def rows83 : List Int := [0,1,2,3,4,5,6,10,15,24,25,26,27,28,29]
def cols83 : List Int := [0,1,2,3,4,5,6,10,15,24,25,26,27,28,29]
def requiredD83 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS83 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem83_eq : pairedProblem rows83 cols83 requiredD83 requiredS83 =
    MomentData.problem83 := by rfl
theorem leaf83 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows83++rows83))
    (hc : (q.map Prod.snd).Perm (cols83++cols83))
    (hd : ∀ k ∈ requiredD83, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS83, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows83 cols83 requiredD83 requiredS83
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem83_eq] at model
  exact MomentData.excluded83 ds ss model
def rows84 : List Int := [0,1,2,3,4,5,6,7,11,16,25,26,27,28,29]
def cols84 : List Int := [0,1,2,3,4,5,6,7,11,16,25,26,27,28,29]
def requiredD84 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS84 : List Int := [23,26,27,28,29,30,31,32,33,34,35,36,37,38,41]
theorem problem84_eq : pairedProblem rows84 cols84 requiredD84 requiredS84 =
    MomentData.problem84 := by rfl
theorem leaf84 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows84++rows84))
    (hc : (q.map Prod.snd).Perm (cols84++cols84))
    (hd : ∀ k ∈ requiredD84, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS84, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows84 cols84 requiredD84 requiredS84
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem84_eq] at model
  exact MomentData.excluded84 ds ss model
def rows85 : List Int := [0,1,2,3,4,5,6,7,11,16,25,26,27,28,29]
def cols85 : List Int := [0,1,2,3,4,5,6,7,11,16,25,26,27,28,29]
def requiredD85 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS85 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem85_eq : pairedProblem rows85 cols85 requiredD85 requiredS85 =
    MomentData.problem85 := by rfl
theorem leaf85 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows85++rows85))
    (hc : (q.map Prod.snd).Perm (cols85++cols85))
    (hd : ∀ k ∈ requiredD85, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS85, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows85 cols85 requiredD85 requiredS85
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem85_eq] at model
  exact MomentData.excluded85 ds ss model
def rows86 : List Int := [0,1,2,3,4,5,6,7,8,12,17,26,27,28,29]
def cols86 : List Int := [0,1,2,3,4,5,6,7,8,12,17,26,27,28,29]
def requiredD86 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS86 : List Int := [25,28,29,30,31,32,33,34,35,36,37,38,39,40,43]
theorem problem86_eq : pairedProblem rows86 cols86 requiredD86 requiredS86 =
    MomentData.problem86 := by rfl
theorem leaf86 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows86++rows86))
    (hc : (q.map Prod.snd).Perm (cols86++cols86))
    (hd : ∀ k ∈ requiredD86, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS86, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows86 cols86 requiredD86 requiredS86
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem86_eq] at model
  exact MomentData.excluded86 ds ss model
def rows87 : List Int := [0,1,2,3,4,5,6,7,8,12,17,26,27,28,29]
def cols87 : List Int := [0,1,2,3,4,5,6,7,8,12,17,26,27,28,29]
def requiredD87 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS87 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem87_eq : pairedProblem rows87 cols87 requiredD87 requiredS87 =
    MomentData.problem87 := by rfl
theorem leaf87 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows87++rows87))
    (hc : (q.map Prod.snd).Perm (cols87++cols87))
    (hd : ∀ k ∈ requiredD87, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS87, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows87 cols87 requiredD87 requiredS87
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem87_eq] at model
  exact MomentData.excluded87 ds ss model
def rows88 : List Int := [0,1,2,3,4,5,8,14,23,24,25,26,27,28,29]
def cols88 : List Int := [0,1,2,3,4,5,8,14,23,24,25,26,27,28,29]
def requiredD88 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS88 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem88_eq : pairedProblem rows88 cols88 requiredD88 requiredS88 =
    MomentData.problem88 := by rfl
theorem leaf88 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows88++rows88))
    (hc : (q.map Prod.snd).Perm (cols88++cols88))
    (hd : ∀ k ∈ requiredD88, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS88, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows88 cols88 requiredD88 requiredS88
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem88_eq] at model
  exact MomentData.excluded88 ds ss model
def rows89 : List Int := [0,1,2,3,4,5,6,9,15,24,25,26,27,28,29]
def cols89 : List Int := [0,1,2,3,4,5,6,9,15,24,25,26,27,28,29]
def requiredD89 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS89 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem89_eq : pairedProblem rows89 cols89 requiredD89 requiredS89 =
    MomentData.problem89 := by rfl
theorem leaf89 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows89++rows89))
    (hc : (q.map Prod.snd).Perm (cols89++cols89))
    (hd : ∀ k ∈ requiredD89, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS89, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows89 cols89 requiredD89 requiredS89
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem89_eq] at model
  exact MomentData.excluded89 ds ss model
def rows90 : List Int := [0,1,2,3,4,5,6,7,10,16,25,26,27,28,29]
def cols90 : List Int := [0,1,2,3,4,5,6,7,10,16,25,26,27,28,29]
def requiredD90 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS90 : List Int := [23,26,27,28,29,30,31,32,33,34,35,36,37,38,41]
theorem problem90_eq : pairedProblem rows90 cols90 requiredD90 requiredS90 =
    MomentData.problem90 := by rfl
theorem leaf90 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows90++rows90))
    (hc : (q.map Prod.snd).Perm (cols90++cols90))
    (hd : ∀ k ∈ requiredD90, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS90, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows90 cols90 requiredD90 requiredS90
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem90_eq] at model
  exact MomentData.excluded90 ds ss model
def rows91 : List Int := [0,1,2,3,4,5,6,7,10,16,25,26,27,28,29]
def cols91 : List Int := [0,1,2,3,4,5,6,7,10,16,25,26,27,28,29]
def requiredD91 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS91 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem91_eq : pairedProblem rows91 cols91 requiredD91 requiredS91 =
    MomentData.problem91 := by rfl
theorem leaf91 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows91++rows91))
    (hc : (q.map Prod.snd).Perm (cols91++cols91))
    (hd : ∀ k ∈ requiredD91, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS91, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows91 cols91 requiredD91 requiredS91
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem91_eq] at model
  exact MomentData.excluded91 ds ss model
def rows92 : List Int := [0,1,2,3,4,5,6,7,8,11,17,26,27,28,29]
def cols92 : List Int := [0,1,2,3,4,5,6,7,8,11,17,26,27,28,29]
def requiredD92 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS92 : List Int := [25,28,29,30,31,32,33,34,35,36,37,38,39,40,43]
theorem problem92_eq : pairedProblem rows92 cols92 requiredD92 requiredS92 =
    MomentData.problem92 := by rfl
theorem leaf92 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows92++rows92))
    (hc : (q.map Prod.snd).Perm (cols92++cols92))
    (hd : ∀ k ∈ requiredD92, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS92, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows92 cols92 requiredD92 requiredS92
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem92_eq] at model
  exact MomentData.excluded92 ds ss model
def rows93 : List Int := [0,1,2,3,4,5,6,8,15,24,25,26,27,28,29]
def cols93 : List Int := [0,1,2,3,4,5,6,8,15,24,25,26,27,28,29]
def requiredD93 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS93 : List Int := [21,24,25,26,27,28,29,30,31,32,33,34,35,36,39]
theorem problem93_eq : pairedProblem rows93 cols93 requiredD93 requiredS93 =
    MomentData.problem93 := by rfl
theorem leaf93 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows93++rows93))
    (hc : (q.map Prod.snd).Perm (cols93++cols93))
    (hd : ∀ k ∈ requiredD93, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS93, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows93 cols93 requiredD93 requiredS93
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem93_eq] at model
  exact MomentData.excluded93 ds ss model
def rows94 : List Int := [0,1,2,3,4,5,6,8,15,24,25,26,27,28,29]
def cols94 : List Int := [0,1,2,3,4,5,6,8,15,24,25,26,27,28,29]
def requiredD94 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS94 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem94_eq : pairedProblem rows94 cols94 requiredD94 requiredS94 =
    MomentData.problem94 := by rfl
theorem leaf94 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows94++rows94))
    (hc : (q.map Prod.snd).Perm (cols94++cols94))
    (hd : ∀ k ∈ requiredD94, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS94, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows94 cols94 requiredD94 requiredS94
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem94_eq] at model
  exact MomentData.excluded94 ds ss model
def rows95 : List Int := [0,1,2,3,4,5,6,7,9,16,25,26,27,28,29]
def cols95 : List Int := [0,1,2,3,4,5,6,7,9,16,25,26,27,28,29]
def requiredD95 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS95 : List Int := [23,26,27,28,29,30,31,32,33,34,35,36,37,38,41]
theorem problem95_eq : pairedProblem rows95 cols95 requiredD95 requiredS95 =
    MomentData.problem95 := by rfl
theorem leaf95 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows95++rows95))
    (hc : (q.map Prod.snd).Perm (cols95++cols95))
    (hd : ∀ k ∈ requiredD95, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS95, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows95 cols95 requiredD95 requiredS95
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem95_eq] at model
  exact MomentData.excluded95 ds ss model
def rows96 : List Int := [0,1,2,3,10,15,20,22,23,24,25,26,27,28,29]
def cols96 : List Int := [0,1,2,3,10,15,20,22,23,24,25,26,27,28,29]
def requiredD96 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS96 : List Int := [16,18,20,21,22,23,24,25,26,27,28,29,30,32,34]
theorem problem96_eq : pairedProblem rows96 cols96 requiredD96 requiredS96 =
    MomentData.problem96 := by rfl
theorem leaf96 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows96++rows96))
    (hc : (q.map Prod.snd).Perm (cols96++cols96))
    (hd : ∀ k ∈ requiredD96, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS96, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows96 cols96 requiredD96 requiredS96
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem96_eq] at model
  exact MomentData.excluded96 ds ss model
def rows97 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def cols97 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def requiredD97 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS97 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem97_eq : pairedProblem rows97 cols97 requiredD97 requiredS97 =
    MomentData.problem97 := by rfl
theorem leaf97 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows97++rows97))
    (hc : (q.map Prod.snd).Perm (cols97++cols97))
    (hd : ∀ k ∈ requiredD97, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS97, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows97 cols97 requiredD97 requiredS97
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem97_eq] at model
  exact MomentData.excluded97 ds ss model
def rows98 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def cols98 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def requiredD98 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS98 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem98_eq : pairedProblem rows98 cols98 requiredD98 requiredS98 =
    MomentData.problem98 := by rfl
theorem leaf98 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows98++rows98))
    (hc : (q.map Prod.snd).Perm (cols98++cols98))
    (hd : ∀ k ∈ requiredD98, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS98, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows98 cols98 requiredD98 requiredS98
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem98_eq] at model
  exact MomentData.excluded98 ds ss model
def rows99 : List Int := [0,1,2,3,4,5,6,13,18,23,25,26,27,28,29]
def cols99 : List Int := [0,1,2,3,4,5,6,13,18,23,25,26,27,28,29]
def requiredD99 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS99 : List Int := [22,24,26,27,28,29,30,31,32,33,34,35,36,38,40]
theorem problem99_eq : pairedProblem rows99 cols99 requiredD99 requiredS99 =
    MomentData.problem99 := by rfl
theorem leaf99 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows99++rows99))
    (hc : (q.map Prod.snd).Perm (cols99++cols99))
    (hd : ∀ k ∈ requiredD99, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS99, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows99 cols99 requiredD99 requiredS99
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem99_eq] at model
  exact MomentData.excluded99 ds ss model
def rows100 : List Int := [0,1,2,3,4,11,16,21,23,24,25,26,27,28,29]
def cols100 : List Int := [0,1,2,3,5,10,15,22,23,24,25,26,27,28,29]
def requiredD100 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS100 : List Int := [17,19,21,22,23,24,25,26,27,28,29,30,31,33,35]
theorem problem100_eq : pairedProblem rows100 cols100 requiredD100 requiredS100 =
    MomentData.problem100 := by rfl
theorem leaf100 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows100++rows100))
    (hc : (q.map Prod.snd).Perm (cols100++cols100))
    (hd : ∀ k ∈ requiredD100, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS100, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows100 cols100 requiredD100 requiredS100
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem100_eq] at model
  exact MomentData.excluded100 ds ss model
def rows101 : List Int := [0,1,2,3,4,5,12,17,22,24,25,26,27,28,29]
def cols101 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def requiredD101 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS101 : List Int := [19,21,23,24,25,26,27,28,29,30,31,32,33,35,37]
theorem problem101_eq : pairedProblem rows101 cols101 requiredD101 requiredS101 =
    MomentData.problem101 := by rfl
theorem leaf101 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows101++rows101))
    (hc : (q.map Prod.snd).Perm (cols101++cols101))
    (hd : ∀ k ∈ requiredD101, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS101, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows101 cols101 requiredD101 requiredS101
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem101_eq] at model
  exact MomentData.excluded101 ds ss model
def rows102 : List Int := [0,1,2,3,4,5,6,13,18,23,25,26,27,28,29]
def cols102 : List Int := [0,1,2,3,4,5,7,12,17,24,25,26,27,28,29]
def requiredD102 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS102 : List Int := [21,23,25,26,27,28,29,30,31,32,33,34,35,37,39]
theorem problem102_eq : pairedProblem rows102 cols102 requiredD102 requiredS102 =
    MomentData.problem102 := by rfl
theorem leaf102 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows102++rows102))
    (hc : (q.map Prod.snd).Perm (cols102++cols102))
    (hd : ∀ k ∈ requiredD102, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS102, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows102 cols102 requiredD102 requiredS102
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem102_eq] at model
  exact MomentData.excluded102 ds ss model
def rows103 : List Int := [0,1,2,3,4,5,6,7,14,19,24,26,27,28,29]
def cols103 : List Int := [0,1,2,3,4,5,6,8,13,18,25,26,27,28,29]
def requiredD103 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,5,6,8,10]
def requiredS103 : List Int := [23,25,27,28,29,30,31,32,33,34,35,36,37,39,41]
theorem problem103_eq : pairedProblem rows103 cols103 requiredD103 requiredS103 =
    MomentData.problem103 := by rfl
theorem leaf103 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows103++rows103))
    (hc : (q.map Prod.snd).Perm (cols103++cols103))
    (hd : ∀ k ∈ requiredD103, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS103, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows103 cols103 requiredD103 requiredS103
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem103_eq] at model
  exact MomentData.excluded103 ds ss model
def rows104 : List Int := [0,1,2,3,4,10,17,20,23,24,25,26,27,28,29]
def cols104 : List Int := [0,1,2,3,4,10,17,20,23,24,25,26,27,28,29]
def requiredD104 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS104 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem104_eq : pairedProblem rows104 cols104 requiredD104 requiredS104 =
    MomentData.problem104 := by rfl
theorem leaf104 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows104++rows104))
    (hc : (q.map Prod.snd).Perm (cols104++cols104))
    (hd : ∀ k ∈ requiredD104, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS104, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows104 cols104 requiredD104 requiredS104
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem104_eq] at model
  exact MomentData.excluded104 ds ss model
def rows105 : List Int := [0,1,2,3,4,5,11,18,21,24,25,26,27,28,29]
def cols105 : List Int := [0,1,2,3,4,5,11,18,21,24,25,26,27,28,29]
def requiredD105 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS105 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem105_eq : pairedProblem rows105 cols105 requiredD105 requiredS105 =
    MomentData.problem105 := by rfl
theorem leaf105 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows105++rows105))
    (hc : (q.map Prod.snd).Perm (cols105++cols105))
    (hd : ∀ k ∈ requiredD105, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS105, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows105 cols105 requiredD105 requiredS105
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem105_eq] at model
  exact MomentData.excluded105 ds ss model
def rows106 : List Int := [0,1,2,3,4,5,6,12,19,22,25,26,27,28,29]
def cols106 : List Int := [0,1,2,3,4,5,6,12,19,22,25,26,27,28,29]
def requiredD106 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS106 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem106_eq : pairedProblem rows106 cols106 requiredD106 requiredS106 =
    MomentData.problem106 := by rfl
theorem leaf106 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows106++rows106))
    (hc : (q.map Prod.snd).Perm (cols106++cols106))
    (hd : ∀ k ∈ requiredD106, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS106, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows106 cols106 requiredD106 requiredS106
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem106_eq] at model
  exact MomentData.excluded106 ds ss model
def rows107 : List Int := [0,1,2,9,14,18,21,22,23,24,25,26,27,28,29]
def cols107 : List Int := [0,1,2,9,14,18,21,22,23,24,25,26,27,28,29]
def requiredD107 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS107 : List Int := [14,16,18,19,20,21,22,23,24,25,26,27,28,30,32]
theorem problem107_eq : pairedProblem rows107 cols107 requiredD107 requiredS107 =
    MomentData.problem107 := by rfl
theorem leaf107 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows107++rows107))
    (hc : (q.map Prod.snd).Perm (cols107++cols107))
    (hd : ∀ k ∈ requiredD107, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS107, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows107 cols107 requiredD107 requiredS107
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem107_eq] at model
  exact MomentData.excluded107 ds ss model
def rows108 : List Int := [0,1,2,3,10,15,19,22,23,24,25,26,27,28,29]
def cols108 : List Int := [0,1,2,3,10,15,19,22,23,24,25,26,27,28,29]
def requiredD108 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS108 : List Int := [16,18,20,21,22,23,24,25,26,27,28,29,30,32,34]
theorem problem108_eq : pairedProblem rows108 cols108 requiredD108 requiredS108 =
    MomentData.problem108 := by rfl
theorem leaf108 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows108++rows108))
    (hc : (q.map Prod.snd).Perm (cols108++cols108))
    (hd : ∀ k ∈ requiredD108, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS108, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows108 cols108 requiredD108 requiredS108
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem108_eq] at model
  exact MomentData.excluded108 ds ss model
def rows109 : List Int := [0,1,2,3,4,11,16,20,23,24,25,26,27,28,29]
def cols109 : List Int := [0,1,2,3,4,11,16,20,23,24,25,26,27,28,29]
def requiredD109 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS109 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem109_eq : pairedProblem rows109 cols109 requiredD109 requiredS109 =
    MomentData.problem109 := by rfl
theorem leaf109 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows109++rows109))
    (hc : (q.map Prod.snd).Perm (cols109++cols109))
    (hd : ∀ k ∈ requiredD109, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS109, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows109 cols109 requiredD109 requiredS109
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem109_eq] at model
  exact MomentData.excluded109 ds ss model
def rows110 : List Int := [0,1,2,3,4,5,12,17,21,24,25,26,27,28,29]
def cols110 : List Int := [0,1,2,3,4,5,12,17,21,24,25,26,27,28,29]
def requiredD110 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS110 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem110_eq : pairedProblem rows110 cols110 requiredD110 requiredS110 =
    MomentData.problem110 := by rfl
theorem leaf110 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows110++rows110))
    (hc : (q.map Prod.snd).Perm (cols110++cols110))
    (hd : ∀ k ∈ requiredD110, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS110, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows110 cols110 requiredD110 requiredS110
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem110_eq] at model
  exact MomentData.excluded110 ds ss model
def rows111 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def cols111 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def requiredD111 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS111 : List Int := [15,19,20,21,22,23,24,25,26,27,28,29,30,31,35]
theorem problem111_eq : pairedProblem rows111 cols111 requiredD111 requiredS111 =
    MomentData.problem111 := by rfl
theorem leaf111 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows111++rows111))
    (hc : (q.map Prod.snd).Perm (cols111++cols111))
    (hd : ∀ k ∈ requiredD111, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS111, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows111 cols111 requiredD111 requiredS111
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem111_eq] at model
  exact MomentData.excluded111 ds ss model
def rows112 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def cols112 : List Int := [0,1,2,3,12,13,18,22,23,24,25,26,27,28,29]
def requiredD112 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS112 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem112_eq : pairedProblem rows112 cols112 requiredD112 requiredS112 =
    MomentData.problem112 := by rfl
theorem leaf112 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows112++rows112))
    (hc : (q.map Prod.snd).Perm (cols112++cols112))
    (hd : ∀ k ∈ requiredD112, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS112, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows112 cols112 requiredD112 requiredS112
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem112_eq] at model
  exact MomentData.excluded112 ds ss model
def rows113 : List Int := [0,1,2,3,4,13,14,19,23,24,25,26,27,28,29]
def cols113 : List Int := [0,1,2,3,4,13,14,19,23,24,25,26,27,28,29]
def requiredD113 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS113 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem113_eq : pairedProblem rows113 cols113 requiredD113 requiredS113 =
    MomentData.problem113 := by rfl
theorem leaf113 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows113++rows113))
    (hc : (q.map Prod.snd).Perm (cols113++cols113))
    (hd : ∀ k ∈ requiredD113, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS113, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows113 cols113 requiredD113 requiredS113
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem113_eq] at model
  exact MomentData.excluded113 ds ss model
def rows114 : List Int := [0,1,2,3,4,5,14,15,20,24,25,26,27,28,29]
def cols114 : List Int := [0,1,2,3,4,5,14,15,20,24,25,26,27,28,29]
def requiredD114 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS114 : List Int := [19,23,24,25,26,27,28,29,30,31,32,33,34,35,39]
theorem problem114_eq : pairedProblem rows114 cols114 requiredD114 requiredS114 =
    MomentData.problem114 := by rfl
theorem leaf114 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows114++rows114))
    (hc : (q.map Prod.snd).Perm (cols114++cols114))
    (hd : ∀ k ∈ requiredD114, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS114, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows114 cols114 requiredD114 requiredS114
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem114_eq] at model
  exact MomentData.excluded114 ds ss model
def rows115 : List Int := [0,1,2,3,4,5,6,15,16,21,25,26,27,28,29]
def cols115 : List Int := [0,1,2,3,4,5,6,15,16,21,25,26,27,28,29]
def requiredD115 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS115 : List Int := [21,25,26,27,28,29,30,31,32,33,34,35,36,37,41]
theorem problem115_eq : pairedProblem rows115 cols115 requiredD115 requiredS115 =
    MomentData.problem115 := by rfl
theorem leaf115 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows115++rows115))
    (hc : (q.map Prod.snd).Perm (cols115++cols115))
    (hd : ∀ k ∈ requiredD115, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS115, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows115 cols115 requiredD115 requiredS115
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem115_eq] at model
  exact MomentData.excluded115 ds ss model
def rows116 : List Int := [0,1,2,3,4,8,14,19,23,24,25,26,27,28,29]
def cols116 : List Int := [0,1,2,3,4,8,14,19,23,24,25,26,27,28,29]
def requiredD116 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS116 : List Int := [15,17,19,21,23,25,26,27,28,29,31,33,35,37,39]
theorem problem116_eq : pairedProblem rows116 cols116 requiredD116 requiredS116 =
    MomentData.problem116 := by rfl
theorem leaf116 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows116++rows116))
    (hc : (q.map Prod.snd).Perm (cols116++cols116))
    (hd : ∀ k ∈ requiredD116, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS116, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows116 cols116 requiredD116 requiredS116
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem116_eq] at model
  exact MomentData.excluded116 ds ss model
def rows117 : List Int := [0,1,2,3,4,5,9,15,20,24,25,26,27,28,29]
def cols117 : List Int := [0,1,2,3,4,5,9,15,20,24,25,26,27,28,29]
def requiredD117 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS117 : List Int := [17,19,21,23,25,27,28,29,30,31,33,35,37,39,41]
theorem problem117_eq : pairedProblem rows117 cols117 requiredD117 requiredS117 =
    MomentData.problem117 := by rfl
theorem leaf117 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows117++rows117))
    (hc : (q.map Prod.snd).Perm (cols117++cols117))
    (hd : ∀ k ∈ requiredD117, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS117, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows117 cols117 requiredD117 requiredS117
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem117_eq] at model
  exact MomentData.excluded117 ds ss model
def rows118 : List Int := [0,1,2,3,4,5,6,10,16,21,25,26,27,28,29]
def cols118 : List Int := [0,1,2,3,4,5,6,10,16,21,25,26,27,28,29]
def requiredD118 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS118 : List Int := [19,21,23,25,27,29,30,31,32,33,35,37,39,41,43]
theorem problem118_eq : pairedProblem rows118 cols118 requiredD118 requiredS118 =
    MomentData.problem118 := by rfl
theorem leaf118 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows118++rows118))
    (hc : (q.map Prod.snd).Perm (cols118++cols118))
    (hd : ∀ k ∈ requiredD118, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS118, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows118 cols118 requiredD118 requiredS118
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem118_eq] at model
  exact MomentData.excluded118 ds ss model
def rows119 : List Int := [0,1,2,3,4,8,13,19,23,24,25,26,27,28,29]
def cols119 : List Int := [0,1,2,3,4,8,13,19,23,24,25,26,27,28,29]
def requiredD119 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS119 : List Int := [15,17,19,21,23,25,26,27,28,29,31,33,35,37,39]
theorem problem119_eq : pairedProblem rows119 cols119 requiredD119 requiredS119 =
    MomentData.problem119 := by rfl
theorem leaf119 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows119++rows119))
    (hc : (q.map Prod.snd).Perm (cols119++cols119))
    (hd : ∀ k ∈ requiredD119, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS119, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows119 cols119 requiredD119 requiredS119
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem119_eq] at model
  exact MomentData.excluded119 ds ss model
def rows120 : List Int := [0,1,2,3,4,5,9,14,20,24,25,26,27,28,29]
def cols120 : List Int := [0,1,2,3,4,5,9,14,20,24,25,26,27,28,29]
def requiredD120 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS120 : List Int := [17,19,21,23,25,27,28,29,30,31,33,35,37,39,41]
theorem problem120_eq : pairedProblem rows120 cols120 requiredD120 requiredS120 =
    MomentData.problem120 := by rfl
theorem leaf120 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows120++rows120))
    (hc : (q.map Prod.snd).Perm (cols120++cols120))
    (hd : ∀ k ∈ requiredD120, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS120, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows120 cols120 requiredD120 requiredS120
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem120_eq] at model
  exact MomentData.excluded120 ds ss model
def rows121 : List Int := [0,1,2,3,4,5,6,10,15,21,25,26,27,28,29]
def cols121 : List Int := [0,1,2,3,4,5,6,10,15,21,25,26,27,28,29]
def requiredD121 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS121 : List Int := [19,21,23,25,27,29,30,31,32,33,35,37,39,41,43]
theorem problem121_eq : pairedProblem rows121 cols121 requiredD121 requiredS121 =
    MomentData.problem121 := by rfl
theorem leaf121 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows121++rows121))
    (hc : (q.map Prod.snd).Perm (cols121++cols121))
    (hd : ∀ k ∈ requiredD121, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS121, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows121 cols121 requiredD121 requiredS121
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem121_eq] at model
  exact MomentData.excluded121 ds ss model
def rows122 : List Int := [0,1,2,3,4,10,17,18,23,24,25,26,27,28,29]
def cols122 : List Int := [0,1,2,3,4,10,17,18,23,24,25,26,27,28,29]
def requiredD122 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS122 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem122_eq : pairedProblem rows122 cols122 requiredD122 requiredS122 =
    MomentData.problem122 := by rfl
theorem leaf122 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows122++rows122))
    (hc : (q.map Prod.snd).Perm (cols122++cols122))
    (hd : ∀ k ∈ requiredD122, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS122, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows122 cols122 requiredD122 requiredS122
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem122_eq] at model
  exact MomentData.excluded122 ds ss model
def rows123 : List Int := [0,1,2,3,4,5,11,18,19,24,25,26,27,28,29]
def cols123 : List Int := [0,1,2,3,4,5,11,18,19,24,25,26,27,28,29]
def requiredD123 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS123 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem123_eq : pairedProblem rows123 cols123 requiredD123 requiredS123 =
    MomentData.problem123 := by rfl
theorem leaf123 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows123++rows123))
    (hc : (q.map Prod.snd).Perm (cols123++cols123))
    (hd : ∀ k ∈ requiredD123, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS123, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows123 cols123 requiredD123 requiredS123
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem123_eq] at model
  exact MomentData.excluded123 ds ss model
def rows124 : List Int := [0,1,2,3,4,5,6,12,19,20,25,26,27,28,29]
def cols124 : List Int := [0,1,2,3,4,5,6,12,19,20,25,26,27,28,29]
def requiredD124 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS124 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem124_eq : pairedProblem rows124 cols124 requiredD124 requiredS124 =
    MomentData.problem124 := by rfl
theorem leaf124 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows124++rows124))
    (hc : (q.map Prod.snd).Perm (cols124++cols124))
    (hd : ∀ k ∈ requiredD124, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS124, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows124 cols124 requiredD124 requiredS124
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem124_eq] at model
  exact MomentData.excluded124 ds ss model
def rows125 : List Int := [0,1,2,3,4,12,15,18,23,24,25,26,27,28,29]
def cols125 : List Int := [0,1,2,3,4,12,15,18,23,24,25,26,27,28,29]
def requiredD125 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS125 : List Int := [19,21,22,23,24,25,26,27,28,29,30,31,32,33,35]
theorem problem125_eq : pairedProblem rows125 cols125 requiredD125 requiredS125 =
    MomentData.problem125 := by rfl
theorem leaf125 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows125++rows125))
    (hc : (q.map Prod.snd).Perm (cols125++cols125))
    (hd : ∀ k ∈ requiredD125, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS125, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows125 cols125 requiredD125 requiredS125
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem125_eq] at model
  exact MomentData.excluded125 ds ss model
def rows126 : List Int := [0,1,2,3,4,5,13,16,19,24,25,26,27,28,29]
def cols126 : List Int := [0,1,2,3,4,5,13,16,19,24,25,26,27,28,29]
def requiredD126 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS126 : List Int := [21,23,24,25,26,27,28,29,30,31,32,33,34,35,37]
theorem problem126_eq : pairedProblem rows126 cols126 requiredD126 requiredS126 =
    MomentData.problem126 := by rfl
theorem leaf126 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows126++rows126))
    (hc : (q.map Prod.snd).Perm (cols126++cols126))
    (hd : ∀ k ∈ requiredD126, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS126, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows126 cols126 requiredD126 requiredS126
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem126_eq] at model
  exact MomentData.excluded126 ds ss model
def rows127 : List Int := [0,1,2,3,8,14,17,22,23,24,25,26,27,28,29]
def cols127 : List Int := [0,1,2,3,8,14,17,22,23,24,25,26,27,28,29]
def requiredD127 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS127 : List Int := [14,16,18,20,22,23,24,25,26,27,28,30,32,34,36]
theorem problem127_eq : pairedProblem rows127 cols127 requiredD127 requiredS127 =
    MomentData.problem127 := by rfl
theorem leaf127 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows127++rows127))
    (hc : (q.map Prod.snd).Perm (cols127++cols127))
    (hd : ∀ k ∈ requiredD127, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS127, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows127 cols127 requiredD127 requiredS127
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem127_eq] at model
  exact MomentData.excluded127 ds ss model
#print axioms leaf0
end Gardner.Kernel.MomentContexts
