import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1152 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1152 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1152 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1152 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43]
theorem problem1152_eq : pairedProblem rows1152 cols1152 requiredD1152 requiredS1152 =
    MomentData.problem1152 := by rfl
theorem leaf1152 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1152++rows1152))
    (hc : (q.map Prod.snd).Perm (cols1152++cols1152))
    (hd : ∀ k ∈ requiredD1152, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1152, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1152 cols1152 requiredD1152 requiredS1152
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1152_eq] at model
  exact MomentData.excluded1152 ds ss model
def rows1153 : List Int := [0,1,2,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1153 : List Int := [0,1,2,11,12,13,14,15,16,20,25,26,27,28,29]
def requiredD1153 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1153 : List Int := [13,21,22,23,24,25,26,27,28,29,30,31,32,33,41]
theorem problem1153_eq : pairedProblem rows1153 cols1153 requiredD1153 requiredS1153 =
    MomentData.problem1153 := by rfl
theorem leaf1153 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1153++rows1153))
    (hc : (q.map Prod.snd).Perm (cols1153++cols1153))
    (hd : ∀ k ∈ requiredD1153, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1153, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1153 cols1153 requiredD1153 requiredS1153
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1153_eq] at model
  exact MomentData.excluded1153 ds ss model
def rows1154 : List Int := [0,1,2,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1154 : List Int := [0,1,2,11,12,13,14,15,16,20,25,26,27,28,29]
def requiredD1154 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1154 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1154_eq : pairedProblem rows1154 cols1154 requiredD1154 requiredS1154 =
    MomentData.problem1154 := by rfl
theorem leaf1154 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1154++rows1154))
    (hc : (q.map Prod.snd).Perm (cols1154++cols1154))
    (hd : ∀ k ∈ requiredD1154, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1154, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1154 cols1154 requiredD1154 requiredS1154
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1154_eq] at model
  exact MomentData.excluded1154 ds ss model
def rows1155 : List Int := [0,1,2,11,12,13,14,15,16,21,25,26,27,28,29]
def cols1155 : List Int := [0,1,2,11,12,13,14,15,16,21,25,26,27,28,29]
def requiredD1155 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1155 : List Int := [13,21,22,23,24,25,26,27,28,29,30,31,32,33,41]
theorem problem1155_eq : pairedProblem rows1155 cols1155 requiredD1155 requiredS1155 =
    MomentData.problem1155 := by rfl
theorem leaf1155 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1155++rows1155))
    (hc : (q.map Prod.snd).Perm (cols1155++cols1155))
    (hd : ∀ k ∈ requiredD1155, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1155, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1155 cols1155 requiredD1155 requiredS1155
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1155_eq] at model
  exact MomentData.excluded1155 ds ss model
def rows1156 : List Int := [0,1,6,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1156 : List Int := [0,1,6,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1156 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1156 : List Int := [11,19,20,21,22,23,24,25,26,27,28,29,30,31,39]
theorem problem1156_eq : pairedProblem rows1156 cols1156 requiredD1156 requiredS1156 =
    MomentData.problem1156 := by rfl
theorem leaf1156 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1156++rows1156))
    (hc : (q.map Prod.snd).Perm (cols1156++cols1156))
    (hd : ∀ k ∈ requiredD1156, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1156, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1156 cols1156 requiredD1156 requiredS1156
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1156_eq] at model
  exact MomentData.excluded1156 ds ss model
def rows1157 : List Int := [0,1,7,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1157 : List Int := [0,1,7,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1157 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1157 : List Int := [11,19,20,21,22,23,24,25,26,27,28,29,30,31,39]
theorem problem1157_eq : pairedProblem rows1157 cols1157 requiredD1157 requiredS1157 =
    MomentData.problem1157 := by rfl
theorem leaf1157 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1157++rows1157))
    (hc : (q.map Prod.snd).Perm (cols1157++cols1157))
    (hd : ∀ k ∈ requiredD1157, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1157, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1157 cols1157 requiredD1157 requiredS1157
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1157_eq] at model
  exact MomentData.excluded1157 ds ss model
def rows1158 : List Int := [0,1,7,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1158 : List Int := [0,1,7,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1158 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1158 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1158_eq : pairedProblem rows1158 cols1158 requiredD1158 requiredS1158 =
    MomentData.problem1158 := by rfl
theorem leaf1158 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1158++rows1158))
    (hc : (q.map Prod.snd).Perm (cols1158++cols1158))
    (hd : ∀ k ∈ requiredD1158, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1158, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1158 cols1158 requiredD1158 requiredS1158
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1158_eq] at model
  exact MomentData.excluded1158 ds ss model
def rows1159 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1159 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1159 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1159 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem1159_eq : pairedProblem rows1159 cols1159 requiredD1159 requiredS1159 =
    MomentData.problem1159 := by rfl
theorem leaf1159 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1159++rows1159))
    (hc : (q.map Prod.snd).Perm (cols1159++cols1159))
    (hd : ∀ k ∈ requiredD1159, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1159, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1159 cols1159 requiredD1159 requiredS1159
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1159_eq] at model
  exact MomentData.excluded1159 ds ss model
def rows1160 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1160 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1160 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1160 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem1160_eq : pairedProblem rows1160 cols1160 requiredD1160 requiredS1160 =
    MomentData.problem1160 := by rfl
theorem leaf1160 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1160++rows1160))
    (hc : (q.map Prod.snd).Perm (cols1160++cols1160))
    (hd : ∀ k ∈ requiredD1160, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1160, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1160 cols1160 requiredD1160 requiredS1160
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1160_eq] at model
  exact MomentData.excluded1160 ds ss model
def rows1161 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1161 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1161 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1161 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1161_eq : pairedProblem rows1161 cols1161 requiredD1161 requiredS1161 =
    MomentData.problem1161 := by rfl
theorem leaf1161 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1161++rows1161))
    (hc : (q.map Prod.snd).Perm (cols1161++cols1161))
    (hd : ∀ k ∈ requiredD1161, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1161, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1161 cols1161 requiredD1161 requiredS1161
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1161_eq] at model
  exact MomentData.excluded1161 ds ss model
def rows1162 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1162 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1162 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1162 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem1162_eq : pairedProblem rows1162 cols1162 requiredD1162 requiredS1162 =
    MomentData.problem1162 := by rfl
theorem leaf1162 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1162++rows1162))
    (hc : (q.map Prod.snd).Perm (cols1162++cols1162))
    (hd : ∀ k ∈ requiredD1162, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1162, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1162 cols1162 requiredD1162 requiredS1162
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1162_eq] at model
  exact MomentData.excluded1162 ds ss model
def rows1163 : List Int := [0,1,3,5,7,12,18,20,22,24,25,26,27,28,29]
def cols1163 : List Int := [0,1,3,5,7,12,18,20,22,24,25,26,27,28,29]
def requiredD1163 : List Int := [-12,-10,-8,-7,-6,-4,-2,0,2,4,6,7,8,10,12]
def requiredS1163 : List Int := [13,15,17,18,19,21,23,25,27,29,31,32,33,35,37]
theorem problem1163_eq : pairedProblem rows1163 cols1163 requiredD1163 requiredS1163 =
    MomentData.problem1163 := by rfl
theorem leaf1163 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1163++rows1163))
    (hc : (q.map Prod.snd).Perm (cols1163++cols1163))
    (hd : ∀ k ∈ requiredD1163, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1163, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1163 cols1163 requiredD1163 requiredS1163
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1163_eq] at model
  exact MomentData.excluded1163 ds ss model
def rows1164 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1164 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1164 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1164 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem1164_eq : pairedProblem rows1164 cols1164 requiredD1164 requiredS1164 =
    MomentData.problem1164 := by rfl
theorem leaf1164 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1164++rows1164))
    (hc : (q.map Prod.snd).Perm (cols1164++cols1164))
    (hd : ∀ k ∈ requiredD1164, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1164, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1164 cols1164 requiredD1164 requiredS1164
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1164_eq] at model
  exact MomentData.excluded1164 ds ss model
def rows1165 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1165 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1165 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1165 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem1165_eq : pairedProblem rows1165 cols1165 requiredD1165 requiredS1165 =
    MomentData.problem1165 := by rfl
theorem leaf1165 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1165++rows1165))
    (hc : (q.map Prod.snd).Perm (cols1165++cols1165))
    (hd : ∀ k ∈ requiredD1165, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1165, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1165 cols1165 requiredD1165 requiredS1165
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1165_eq] at model
  exact MomentData.excluded1165 ds ss model
def rows1166 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1166 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1166 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1166 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem1166_eq : pairedProblem rows1166 cols1166 requiredD1166 requiredS1166 =
    MomentData.problem1166 := by rfl
theorem leaf1166 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1166++rows1166))
    (hc : (q.map Prod.snd).Perm (cols1166++cols1166))
    (hd : ∀ k ∈ requiredD1166, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1166, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1166 cols1166 requiredD1166 requiredS1166
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1166_eq] at model
  exact MomentData.excluded1166 ds ss model
def rows1167 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1167 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1167 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1167 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41]
theorem problem1167_eq : pairedProblem rows1167 cols1167 requiredD1167 requiredS1167 =
    MomentData.problem1167 := by rfl
theorem leaf1167 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1167++rows1167))
    (hc : (q.map Prod.snd).Perm (cols1167++cols1167))
    (hd : ∀ k ∈ requiredD1167, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1167, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1167 cols1167 requiredD1167 requiredS1167
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1167_eq] at model
  exact MomentData.excluded1167 ds ss model
def rows1168 : List Int := [0,1,10,11,12,13,14,15,19,24,25,26,27,28,29]
def cols1168 : List Int := [0,1,10,11,12,13,14,15,19,24,25,26,27,28,29]
def requiredD1168 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1168 : List Int := [11,19,20,21,22,23,24,25,26,27,28,29,30,31,39]
theorem problem1168_eq : pairedProblem rows1168 cols1168 requiredD1168 requiredS1168 =
    MomentData.problem1168 := by rfl
theorem leaf1168 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1168++rows1168))
    (hc : (q.map Prod.snd).Perm (cols1168++cols1168))
    (hd : ∀ k ∈ requiredD1168, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1168, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1168 cols1168 requiredD1168 requiredS1168
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1168_eq] at model
  exact MomentData.excluded1168 ds ss model
def rows1169 : List Int := [0,4,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1169 : List Int := [0,4,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1169 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1169 : List Int := [9,17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem1169_eq : pairedProblem rows1169 cols1169 requiredD1169 requiredS1169 =
    MomentData.problem1169 := by rfl
theorem leaf1169 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1169++rows1169))
    (hc : (q.map Prod.snd).Perm (cols1169++cols1169))
    (hd : ∀ k ∈ requiredD1169, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1169, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1169 cols1169 requiredD1169 requiredS1169
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1169_eq] at model
  exact MomentData.excluded1169 ds ss model
def rows1170 : List Int := [0,5,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1170 : List Int := [0,5,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1170 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1170 : List Int := [9,17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem1170_eq : pairedProblem rows1170 cols1170 requiredD1170 requiredS1170 =
    MomentData.problem1170 := by rfl
theorem leaf1170 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1170++rows1170))
    (hc : (q.map Prod.snd).Perm (cols1170++cols1170))
    (hd : ∀ k ∈ requiredD1170, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1170, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1170 cols1170 requiredD1170 requiredS1170
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1170_eq] at model
  exact MomentData.excluded1170 ds ss model
def rows1171 : List Int := [0,6,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1171 : List Int := [0,6,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1171 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1171 : List Int := [9,17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem1171_eq : pairedProblem rows1171 cols1171 requiredD1171 requiredS1171 =
    MomentData.problem1171 := by rfl
theorem leaf1171 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1171++rows1171))
    (hc : (q.map Prod.snd).Perm (cols1171++cols1171))
    (hd : ∀ k ∈ requiredD1171, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1171, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1171 cols1171 requiredD1171 requiredS1171
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1171_eq] at model
  exact MomentData.excluded1171 ds ss model
def rows1172 : List Int := [0,7,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1172 : List Int := [0,7,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1172 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1172 : List Int := [9,17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem1172_eq : pairedProblem rows1172 cols1172 requiredD1172 requiredS1172 =
    MomentData.problem1172 := by rfl
theorem leaf1172 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1172++rows1172))
    (hc : (q.map Prod.snd).Perm (cols1172++cols1172))
    (hd : ∀ k ∈ requiredD1172, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1172, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1172 cols1172 requiredD1172 requiredS1172
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1172_eq] at model
  exact MomentData.excluded1172 ds ss model
def rows1173 : List Int := [0,7,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1173 : List Int := [0,7,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1173 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1173 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1173_eq : pairedProblem rows1173 cols1173 requiredD1173 requiredS1173 =
    MomentData.problem1173 := by rfl
theorem leaf1173 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1173++rows1173))
    (hc : (q.map Prod.snd).Perm (cols1173++cols1173))
    (hd : ∀ k ∈ requiredD1173, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1173, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1173 cols1173 requiredD1173 requiredS1173
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1173_eq] at model
  exact MomentData.excluded1173 ds ss model
def rows1174 : List Int := [0,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def cols1174 : List Int := [0,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def requiredD1174 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1174 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43]
theorem problem1174_eq : pairedProblem rows1174 cols1174 requiredD1174 requiredS1174 =
    MomentData.problem1174 := by rfl
theorem leaf1174 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1174++rows1174))
    (hc : (q.map Prod.snd).Perm (cols1174++cols1174))
    (hd : ∀ k ∈ requiredD1174, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1174, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1174 cols1174 requiredD1174 requiredS1174
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1174_eq] at model
  exact MomentData.excluded1174 ds ss model
def rows1175 : List Int := [0,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1175 : List Int := [0,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1175 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS1175 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem1175_eq : pairedProblem rows1175 cols1175 requiredD1175 requiredS1175 =
    MomentData.problem1175 := by rfl
theorem leaf1175 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1175++rows1175))
    (hc : (q.map Prod.snd).Perm (cols1175++cols1175))
    (hd : ∀ k ∈ requiredD1175, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1175, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1175 cols1175 requiredD1175 requiredS1175
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1175_eq] at model
  exact MomentData.excluded1175 ds ss model
def rows1176 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols1176 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD1176 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1176 : List Int := [3,6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem1176_eq : pairedProblem rows1176 cols1176 requiredD1176 requiredS1176 =
    MomentData.problem1176 := by rfl
theorem leaf1176 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1176++rows1176))
    (hc : (q.map Prod.snd).Perm (cols1176++cols1176))
    (hd : ∀ k ∈ requiredD1176, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1176, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1176 cols1176 requiredD1176 requiredS1176
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1176_eq] at model
  exact MomentData.excluded1176 ds ss model
def rows1177 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols1177 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD1177 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1177 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem1177_eq : pairedProblem rows1177 cols1177 requiredD1177 requiredS1177 =
    MomentData.problem1177 := by rfl
theorem leaf1177 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1177++rows1177))
    (hc : (q.map Prod.snd).Perm (cols1177++cols1177))
    (hd : ∀ k ∈ requiredD1177, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1177, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1177 cols1177 requiredD1177 requiredS1177
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1177_eq] at model
  exact MomentData.excluded1177 ds ss model
def rows1178 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols1178 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD1178 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1178 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42]
theorem problem1178_eq : pairedProblem rows1178 cols1178 requiredD1178 requiredS1178 =
    MomentData.problem1178 := by rfl
theorem leaf1178 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1178++rows1178))
    (hc : (q.map Prod.snd).Perm (cols1178++cols1178))
    (hd : ∀ k ∈ requiredD1178, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1178, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1178 cols1178 requiredD1178 requiredS1178
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1178_eq] at model
  exact MomentData.excluded1178 ds ss model
def rows1179 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols1179 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD1179 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1179 : List Int := [3,6,9,12,15,18,21,23,24,27,30,33,36,39]
theorem problem1179_eq : pairedProblem rows1179 cols1179 requiredD1179 requiredS1179 =
    MomentData.problem1179 := by rfl
theorem leaf1179 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1179++rows1179))
    (hc : (q.map Prod.snd).Perm (cols1179++cols1179))
    (hd : ∀ k ∈ requiredD1179, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1179, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1179 cols1179 requiredD1179 requiredS1179
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1179_eq] at model
  exact MomentData.excluded1179 ds ss model
def rows1180 : List Int := [3,8,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1180 : List Int := [3,8,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1180 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1180 : List Int := [14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
theorem problem1180_eq : pairedProblem rows1180 cols1180 requiredD1180 requiredS1180 =
    MomentData.problem1180 := by rfl
theorem leaf1180 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1180++rows1180))
    (hc : (q.map Prod.snd).Perm (cols1180++cols1180))
    (hd : ∀ k ∈ requiredD1180, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1180, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1180 cols1180 requiredD1180 requiredS1180
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1180_eq] at model
  exact MomentData.excluded1180 ds ss model
def rows1181 : List Int := [4,8,9,10,11,12,13,22,23,24,25,26,27,28,29]
def cols1181 : List Int := [4,8,9,10,11,12,13,22,23,24,25,26,27,28,29]
def requiredD1181 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1181 : List Int := [14,15,16,17,18,19,20,21,22,23,24,25,26,27,28]
theorem problem1181_eq : pairedProblem rows1181 cols1181 requiredD1181 requiredS1181 =
    MomentData.problem1181 := by rfl
theorem leaf1181 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1181++rows1181))
    (hc : (q.map Prod.snd).Perm (cols1181++cols1181))
    (hd : ∀ k ∈ requiredD1181, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1181, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1181 cols1181 requiredD1181 requiredS1181
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1181_eq] at model
  exact MomentData.excluded1181 ds ss model
def rows1182 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols1182 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD1182 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1182 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem1182_eq : pairedProblem rows1182 cols1182 requiredD1182 requiredS1182 =
    MomentData.problem1182 := by rfl
theorem leaf1182 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1182++rows1182))
    (hc : (q.map Prod.snd).Perm (cols1182++cols1182))
    (hd : ∀ k ∈ requiredD1182, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1182, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1182 cols1182 requiredD1182 requiredS1182
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1182_eq] at model
  exact MomentData.excluded1182 ds ss model
def rows1183 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols1183 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD1183 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1183 : List Int := [13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem1183_eq : pairedProblem rows1183 cols1183 requiredD1183 requiredS1183 =
    MomentData.problem1183 := by rfl
theorem leaf1183 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1183++rows1183))
    (hc : (q.map Prod.snd).Perm (cols1183++cols1183))
    (hd : ∀ k ∈ requiredD1183, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1183, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1183 cols1183 requiredD1183 requiredS1183
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1183_eq] at model
  exact MomentData.excluded1183 ds ss model
def rows1184 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols1184 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD1184 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1184 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1184_eq : pairedProblem rows1184 cols1184 requiredD1184 requiredS1184 =
    MomentData.problem1184 := by rfl
theorem leaf1184 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1184++rows1184))
    (hc : (q.map Prod.snd).Perm (cols1184++cols1184))
    (hd : ∀ k ∈ requiredD1184, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1184, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1184 cols1184 requiredD1184 requiredS1184
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1184_eq] at model
  exact MomentData.excluded1184 ds ss model
def rows1185 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols1185 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD1185 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1185 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem1185_eq : pairedProblem rows1185 cols1185 requiredD1185 requiredS1185 =
    MomentData.problem1185 := by rfl
theorem leaf1185 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1185++rows1185))
    (hc : (q.map Prod.snd).Perm (cols1185++cols1185))
    (hd : ∀ k ∈ requiredD1185, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1185, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1185 cols1185 requiredD1185 requiredS1185
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1185_eq] at model
  exact MomentData.excluded1185 ds ss model
def rows1186 : List Int := [0,1,2,5,6,8,11,14,17,20,23,26,27,28,29]
def cols1186 : List Int := [0,1,2,5,6,8,11,14,17,20,23,26,27,28,29]
def requiredD1186 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1186 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1186_eq : pairedProblem rows1186 cols1186 requiredD1186 requiredS1186 =
    MomentData.problem1186 := by rfl
theorem leaf1186 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1186++rows1186))
    (hc : (q.map Prod.snd).Perm (cols1186++cols1186))
    (hd : ∀ k ∈ requiredD1186, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1186, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1186 cols1186 requiredD1186 requiredS1186
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1186_eq] at model
  exact MomentData.excluded1186 ds ss model
def rows1187 : List Int := [0,1,2,5,6,8,11,14,17,20,23,26,27,28,29]
def cols1187 : List Int := [0,1,2,5,6,8,11,14,17,20,23,26,27,28,29]
def requiredD1187 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1187 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1187_eq : pairedProblem rows1187 cols1187 requiredD1187 requiredS1187 =
    MomentData.problem1187 := by rfl
theorem leaf1187 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1187++rows1187))
    (hc : (q.map Prod.snd).Perm (cols1187++cols1187))
    (hd : ∀ k ∈ requiredD1187, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1187, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1187 cols1187 requiredD1187 requiredS1187
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1187_eq] at model
  exact MomentData.excluded1187 ds ss model
def rows1188 : List Int := [0,1,2,5,7,8,11,14,17,20,23,26,27,28,29]
def cols1188 : List Int := [0,1,2,5,7,8,11,14,17,20,23,26,27,28,29]
def requiredD1188 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1188 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1188_eq : pairedProblem rows1188 cols1188 requiredD1188 requiredS1188 =
    MomentData.problem1188 := by rfl
theorem leaf1188 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1188++rows1188))
    (hc : (q.map Prod.snd).Perm (cols1188++cols1188))
    (hd : ∀ k ∈ requiredD1188, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1188, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1188 cols1188 requiredD1188 requiredS1188
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1188_eq] at model
  exact MomentData.excluded1188 ds ss model
def rows1189 : List Int := [0,1,2,5,7,8,11,14,17,20,23,26,27,28,29]
def cols1189 : List Int := [0,1,2,5,7,8,11,14,17,20,23,26,27,28,29]
def requiredD1189 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1189 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1189_eq : pairedProblem rows1189 cols1189 requiredD1189 requiredS1189 =
    MomentData.problem1189 := by rfl
theorem leaf1189 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1189++rows1189))
    (hc : (q.map Prod.snd).Perm (cols1189++cols1189))
    (hd : ∀ k ∈ requiredD1189, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1189, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1189 cols1189 requiredD1189 requiredS1189
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1189_eq] at model
  exact MomentData.excluded1189 ds ss model
def rows1190 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def cols1190 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def requiredD1190 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1190 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1190_eq : pairedProblem rows1190 cols1190 requiredD1190 requiredS1190 =
    MomentData.problem1190 := by rfl
theorem leaf1190 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1190++rows1190))
    (hc : (q.map Prod.snd).Perm (cols1190++cols1190))
    (hd : ∀ k ∈ requiredD1190, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1190, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1190 cols1190 requiredD1190 requiredS1190
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1190_eq] at model
  exact MomentData.excluded1190 ds ss model
def rows1191 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def cols1191 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def requiredD1191 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1191 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1191_eq : pairedProblem rows1191 cols1191 requiredD1191 requiredS1191 =
    MomentData.problem1191 := by rfl
theorem leaf1191 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1191++rows1191))
    (hc : (q.map Prod.snd).Perm (cols1191++cols1191))
    (hd : ∀ k ∈ requiredD1191, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1191, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1191 cols1191 requiredD1191 requiredS1191
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1191_eq] at model
  exact MomentData.excluded1191 ds ss model
def rows1192 : List Int := [0,1,2,5,8,10,11,14,17,20,23,26,27,28,29]
def cols1192 : List Int := [0,1,2,5,8,10,11,14,17,20,23,26,27,28,29]
def requiredD1192 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1192 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1192_eq : pairedProblem rows1192 cols1192 requiredD1192 requiredS1192 =
    MomentData.problem1192 := by rfl
theorem leaf1192 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1192++rows1192))
    (hc : (q.map Prod.snd).Perm (cols1192++cols1192))
    (hd : ∀ k ∈ requiredD1192, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1192, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1192 cols1192 requiredD1192 requiredS1192
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1192_eq] at model
  exact MomentData.excluded1192 ds ss model
def rows1193 : List Int := [0,1,2,5,8,10,11,14,17,20,23,26,27,28,29]
def cols1193 : List Int := [0,1,2,5,8,10,11,14,17,20,23,26,27,28,29]
def requiredD1193 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1193 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1193_eq : pairedProblem rows1193 cols1193 requiredD1193 requiredS1193 =
    MomentData.problem1193 := by rfl
theorem leaf1193 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1193++rows1193))
    (hc : (q.map Prod.snd).Perm (cols1193++cols1193))
    (hd : ∀ k ∈ requiredD1193, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1193, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1193 cols1193 requiredD1193 requiredS1193
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1193_eq] at model
  exact MomentData.excluded1193 ds ss model
def rows1194 : List Int := [0,1,2,5,8,11,12,14,17,20,23,26,27,28,29]
def cols1194 : List Int := [0,1,2,5,8,11,12,14,17,20,23,26,27,28,29]
def requiredD1194 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1194 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1194_eq : pairedProblem rows1194 cols1194 requiredD1194 requiredS1194 =
    MomentData.problem1194 := by rfl
theorem leaf1194 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1194++rows1194))
    (hc : (q.map Prod.snd).Perm (cols1194++cols1194))
    (hd : ∀ k ∈ requiredD1194, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1194, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1194 cols1194 requiredD1194 requiredS1194
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1194_eq] at model
  exact MomentData.excluded1194 ds ss model
def rows1195 : List Int := [0,1,2,5,8,11,12,14,17,20,23,26,27,28,29]
def cols1195 : List Int := [0,1,2,5,8,11,12,14,17,20,23,26,27,28,29]
def requiredD1195 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1195 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1195_eq : pairedProblem rows1195 cols1195 requiredD1195 requiredS1195 =
    MomentData.problem1195 := by rfl
theorem leaf1195 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1195++rows1195))
    (hc : (q.map Prod.snd).Perm (cols1195++cols1195))
    (hd : ∀ k ∈ requiredD1195, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1195, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1195 cols1195 requiredD1195 requiredS1195
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1195_eq] at model
  exact MomentData.excluded1195 ds ss model
def rows1196 : List Int := [0,1,2,5,11,12,13,14,15,16,17,26,27,28,29]
def cols1196 : List Int := [0,1,2,5,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1196 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1196 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1196_eq : pairedProblem rows1196 cols1196 requiredD1196 requiredS1196 =
    MomentData.problem1196 := by rfl
theorem leaf1196 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1196++rows1196))
    (hc : (q.map Prod.snd).Perm (cols1196++cols1196))
    (hd : ∀ k ∈ requiredD1196, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1196, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1196 cols1196 requiredD1196 requiredS1196
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1196_eq] at model
  exact MomentData.excluded1196 ds ss model
def rows1197 : List Int := [0,1,2,6,11,12,13,14,15,16,17,26,27,28,29]
def cols1197 : List Int := [0,1,2,6,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1197 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1197 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1197_eq : pairedProblem rows1197 cols1197 requiredD1197 requiredS1197 =
    MomentData.problem1197 := by rfl
theorem leaf1197 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1197++rows1197))
    (hc : (q.map Prod.snd).Perm (cols1197++cols1197))
    (hd : ∀ k ∈ requiredD1197, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1197, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1197 cols1197 requiredD1197 requiredS1197
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1197_eq] at model
  exact MomentData.excluded1197 ds ss model
def rows1198 : List Int := [0,1,2,7,11,12,13,14,15,16,17,26,27,28,29]
def cols1198 : List Int := [0,1,2,7,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1198 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1198 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1198_eq : pairedProblem rows1198 cols1198 requiredD1198 requiredS1198 =
    MomentData.problem1198 := by rfl
theorem leaf1198 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1198++rows1198))
    (hc : (q.map Prod.snd).Perm (cols1198++cols1198))
    (hd : ∀ k ∈ requiredD1198, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1198, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1198 cols1198 requiredD1198 requiredS1198
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1198_eq] at model
  exact MomentData.excluded1198 ds ss model
def rows1199 : List Int := [0,1,2,7,11,12,13,14,15,16,17,26,27,28,29]
def cols1199 : List Int := [0,1,2,7,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1199 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1199 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1199_eq : pairedProblem rows1199 cols1199 requiredD1199 requiredS1199 =
    MomentData.problem1199 := by rfl
theorem leaf1199 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1199++rows1199))
    (hc : (q.map Prod.snd).Perm (cols1199++cols1199))
    (hd : ∀ k ∈ requiredD1199, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1199, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1199 cols1199 requiredD1199 requiredS1199
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1199_eq] at model
  exact MomentData.excluded1199 ds ss model
def rows1200 : List Int := [0,1,2,5,8,11,13,14,17,20,23,26,27,28,29]
def cols1200 : List Int := [0,1,2,5,8,11,13,14,17,20,23,26,27,28,29]
def requiredD1200 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1200 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1200_eq : pairedProblem rows1200 cols1200 requiredD1200 requiredS1200 =
    MomentData.problem1200 := by rfl
theorem leaf1200 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1200++rows1200))
    (hc : (q.map Prod.snd).Perm (cols1200++cols1200))
    (hd : ∀ k ∈ requiredD1200, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1200, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1200 cols1200 requiredD1200 requiredS1200
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1200_eq] at model
  exact MomentData.excluded1200 ds ss model
def rows1201 : List Int := [0,1,2,5,8,11,13,14,17,20,23,26,27,28,29]
def cols1201 : List Int := [0,1,2,5,8,11,13,14,17,20,23,26,27,28,29]
def requiredD1201 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1201 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1201_eq : pairedProblem rows1201 cols1201 requiredD1201 requiredS1201 =
    MomentData.problem1201 := by rfl
theorem leaf1201 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1201++rows1201))
    (hc : (q.map Prod.snd).Perm (cols1201++cols1201))
    (hd : ∀ k ∈ requiredD1201, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1201, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1201 cols1201 requiredD1201 requiredS1201
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1201_eq] at model
  exact MomentData.excluded1201 ds ss model
def rows1202 : List Int := [0,1,2,8,11,12,13,14,15,16,17,26,27,28,29]
def cols1202 : List Int := [0,1,2,8,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1202 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1202 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1202_eq : pairedProblem rows1202 cols1202 requiredD1202 requiredS1202 =
    MomentData.problem1202 := by rfl
theorem leaf1202 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1202++rows1202))
    (hc : (q.map Prod.snd).Perm (cols1202++cols1202))
    (hd : ∀ k ∈ requiredD1202, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1202, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1202 cols1202 requiredD1202 requiredS1202
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1202_eq] at model
  exact MomentData.excluded1202 ds ss model
def rows1203 : List Int := [0,1,2,8,11,12,13,14,15,16,17,26,27,28,29]
def cols1203 : List Int := [0,1,2,8,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1203 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1203 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1203_eq : pairedProblem rows1203 cols1203 requiredD1203 requiredS1203 =
    MomentData.problem1203 := by rfl
theorem leaf1203 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1203++rows1203))
    (hc : (q.map Prod.snd).Perm (cols1203++cols1203))
    (hd : ∀ k ∈ requiredD1203, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1203, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1203 cols1203 requiredD1203 requiredS1203
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1203_eq] at model
  exact MomentData.excluded1203 ds ss model
def rows1204 : List Int := [0,1,2,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1204 : List Int := [0,1,2,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1204 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1204 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1204_eq : pairedProblem rows1204 cols1204 requiredD1204 requiredS1204 =
    MomentData.problem1204 := by rfl
theorem leaf1204 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1204++rows1204))
    (hc : (q.map Prod.snd).Perm (cols1204++cols1204))
    (hd : ∀ k ∈ requiredD1204, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1204, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1204 cols1204 requiredD1204 requiredS1204
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1204_eq] at model
  exact MomentData.excluded1204 ds ss model
def rows1205 : List Int := [0,1,2,5,8,11,14,15,17,20,23,26,27,28,29]
def cols1205 : List Int := [0,1,2,5,8,11,14,15,17,20,23,26,27,28,29]
def requiredD1205 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1205 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1205_eq : pairedProblem rows1205 cols1205 requiredD1205 requiredS1205 =
    MomentData.problem1205 := by rfl
theorem leaf1205 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1205++rows1205))
    (hc : (q.map Prod.snd).Perm (cols1205++cols1205))
    (hd : ∀ k ∈ requiredD1205, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1205, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1205 cols1205 requiredD1205 requiredS1205
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1205_eq] at model
  exact MomentData.excluded1205 ds ss model
def rows1206 : List Int := [0,1,2,5,8,11,14,15,17,20,23,26,27,28,29]
def cols1206 : List Int := [0,1,2,5,8,11,14,15,17,20,23,26,27,28,29]
def requiredD1206 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1206 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1206_eq : pairedProblem rows1206 cols1206 requiredD1206 requiredS1206 =
    MomentData.problem1206 := by rfl
theorem leaf1206 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1206++rows1206))
    (hc : (q.map Prod.snd).Perm (cols1206++cols1206))
    (hd : ∀ k ∈ requiredD1206, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1206, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1206 cols1206 requiredD1206 requiredS1206
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1206_eq] at model
  exact MomentData.excluded1206 ds ss model
def rows1207 : List Int := [0,1,2,5,8,11,14,16,17,20,23,26,27,28,29]
def cols1207 : List Int := [0,1,2,5,8,11,14,16,17,20,23,26,27,28,29]
def requiredD1207 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1207 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1207_eq : pairedProblem rows1207 cols1207 requiredD1207 requiredS1207 =
    MomentData.problem1207 := by rfl
theorem leaf1207 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1207++rows1207))
    (hc : (q.map Prod.snd).Perm (cols1207++cols1207))
    (hd : ∀ k ∈ requiredD1207, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1207, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1207 cols1207 requiredD1207 requiredS1207
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1207_eq] at model
  exact MomentData.excluded1207 ds ss model
def rows1208 : List Int := [0,1,2,5,8,11,14,16,17,20,23,26,27,28,29]
def cols1208 : List Int := [0,1,2,5,8,11,14,16,17,20,23,26,27,28,29]
def requiredD1208 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1208 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1208_eq : pairedProblem rows1208 cols1208 requiredD1208 requiredS1208 =
    MomentData.problem1208 := by rfl
theorem leaf1208 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1208++rows1208))
    (hc : (q.map Prod.snd).Perm (cols1208++cols1208))
    (hd : ∀ k ∈ requiredD1208, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1208, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1208 cols1208 requiredD1208 requiredS1208
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1208_eq] at model
  exact MomentData.excluded1208 ds ss model
def rows1209 : List Int := [0,1,2,5,8,11,14,17,18,20,23,26,27,28,29]
def cols1209 : List Int := [0,1,2,5,8,11,14,17,18,20,23,26,27,28,29]
def requiredD1209 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1209 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1209_eq : pairedProblem rows1209 cols1209 requiredD1209 requiredS1209 =
    MomentData.problem1209 := by rfl
theorem leaf1209 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1209++rows1209))
    (hc : (q.map Prod.snd).Perm (cols1209++cols1209))
    (hd : ∀ k ∈ requiredD1209, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1209, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1209 cols1209 requiredD1209 requiredS1209
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1209_eq] at model
  exact MomentData.excluded1209 ds ss model
def rows1210 : List Int := [0,1,2,5,8,11,14,17,18,20,23,26,27,28,29]
def cols1210 : List Int := [0,1,2,5,8,11,14,17,18,20,23,26,27,28,29]
def requiredD1210 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1210 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1210_eq : pairedProblem rows1210 cols1210 requiredD1210 requiredS1210 =
    MomentData.problem1210 := by rfl
theorem leaf1210 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1210++rows1210))
    (hc : (q.map Prod.snd).Perm (cols1210++cols1210))
    (hd : ∀ k ∈ requiredD1210, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1210, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1210 cols1210 requiredD1210 requiredS1210
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1210_eq] at model
  exact MomentData.excluded1210 ds ss model
def rows1211 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1211 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1211 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1211 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44,47]
theorem problem1211_eq : pairedProblem rows1211 cols1211 requiredD1211 requiredS1211 =
    MomentData.problem1211 := by rfl
theorem leaf1211 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1211++rows1211))
    (hc : (q.map Prod.snd).Perm (cols1211++cols1211))
    (hd : ∀ k ∈ requiredD1211, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1211, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1211 cols1211 requiredD1211 requiredS1211
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1211_eq] at model
  exact MomentData.excluded1211 ds ss model
def rows1212 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1212 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1212 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1212 : List Int := [11,14,17,20,23,25,26,29,32,35,38,41,44,47]
theorem problem1212_eq : pairedProblem rows1212 cols1212 requiredD1212 requiredS1212 =
    MomentData.problem1212 := by rfl
theorem leaf1212 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1212++rows1212))
    (hc : (q.map Prod.snd).Perm (cols1212++cols1212))
    (hd : ∀ k ∈ requiredD1212, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1212, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1212 cols1212 requiredD1212 requiredS1212
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1212_eq] at model
  exact MomentData.excluded1212 ds ss model
def rows1213 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1213 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1213 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1213 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1213_eq : pairedProblem rows1213 cols1213 requiredD1213 requiredS1213 =
    MomentData.problem1213 := by rfl
theorem leaf1213 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1213++rows1213))
    (hc : (q.map Prod.snd).Perm (cols1213++cols1213))
    (hd : ∀ k ∈ requiredD1213, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1213, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1213 cols1213 requiredD1213 requiredS1213
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1213_eq] at model
  exact MomentData.excluded1213 ds ss model
def rows1214 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols1214 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1214 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1214 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem1214_eq : pairedProblem rows1214 cols1214 requiredD1214 requiredS1214 =
    MomentData.problem1214 := by rfl
theorem leaf1214 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1214++rows1214))
    (hc : (q.map Prod.snd).Perm (cols1214++cols1214))
    (hd : ∀ k ∈ requiredD1214, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1214, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1214 cols1214 requiredD1214 requiredS1214
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1214_eq] at model
  exact MomentData.excluded1214 ds ss model
def rows1215 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def cols1215 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def requiredD1215 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1215 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1215_eq : pairedProblem rows1215 cols1215 requiredD1215 requiredS1215 =
    MomentData.problem1215 := by rfl
theorem leaf1215 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1215++rows1215))
    (hc : (q.map Prod.snd).Perm (cols1215++cols1215))
    (hd : ∀ k ∈ requiredD1215, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1215, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1215 cols1215 requiredD1215 requiredS1215
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1215_eq] at model
  exact MomentData.excluded1215 ds ss model
def rows1216 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def cols1216 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def requiredD1216 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1216 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1216_eq : pairedProblem rows1216 cols1216 requiredD1216 requiredS1216 =
    MomentData.problem1216 := by rfl
theorem leaf1216 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1216++rows1216))
    (hc : (q.map Prod.snd).Perm (cols1216++cols1216))
    (hd : ∀ k ∈ requiredD1216, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1216, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1216 cols1216 requiredD1216 requiredS1216
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1216_eq] at model
  exact MomentData.excluded1216 ds ss model
def rows1217 : List Int := [0,1,2,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1217 : List Int := [0,1,2,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1217 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1217 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1217_eq : pairedProblem rows1217 cols1217 requiredD1217 requiredS1217 =
    MomentData.problem1217 := by rfl
theorem leaf1217 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1217++rows1217))
    (hc : (q.map Prod.snd).Perm (cols1217++cols1217))
    (hd : ∀ k ∈ requiredD1217, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1217, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1217 cols1217 requiredD1217 requiredS1217
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1217_eq] at model
  exact MomentData.excluded1217 ds ss model
def rows1218 : List Int := [0,1,4,5,7,10,13,16,19,22,25,26,27,28,29]
def cols1218 : List Int := [0,1,4,5,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1218 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1218 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1218_eq : pairedProblem rows1218 cols1218 requiredD1218 requiredS1218 =
    MomentData.problem1218 := by rfl
theorem leaf1218 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1218++rows1218))
    (hc : (q.map Prod.snd).Perm (cols1218++cols1218))
    (hd : ∀ k ∈ requiredD1218, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1218, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1218 cols1218 requiredD1218 requiredS1218
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1218_eq] at model
  exact MomentData.excluded1218 ds ss model
def rows1219 : List Int := [0,1,4,5,7,10,13,16,19,22,25,26,27,28,29]
def cols1219 : List Int := [0,1,4,5,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1219 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1219 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1219_eq : pairedProblem rows1219 cols1219 requiredD1219 requiredS1219 =
    MomentData.problem1219 := by rfl
theorem leaf1219 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1219++rows1219))
    (hc : (q.map Prod.snd).Perm (cols1219++cols1219))
    (hd : ∀ k ∈ requiredD1219, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1219, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1219 cols1219 requiredD1219 requiredS1219
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1219_eq] at model
  exact MomentData.excluded1219 ds ss model
def rows1220 : List Int := [0,1,2,5,8,11,14,17,20,21,23,26,27,28,29]
def cols1220 : List Int := [0,1,2,5,8,11,14,17,20,21,23,26,27,28,29]
def requiredD1220 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1220 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1220_eq : pairedProblem rows1220 cols1220 requiredD1220 requiredS1220 =
    MomentData.problem1220 := by rfl
theorem leaf1220 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1220++rows1220))
    (hc : (q.map Prod.snd).Perm (cols1220++cols1220))
    (hd : ∀ k ∈ requiredD1220, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1220, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1220 cols1220 requiredD1220 requiredS1220
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1220_eq] at model
  exact MomentData.excluded1220 ds ss model
def rows1221 : List Int := [0,1,2,5,8,11,14,17,20,21,23,26,27,28,29]
def cols1221 : List Int := [0,1,2,5,8,11,14,17,20,21,23,26,27,28,29]
def requiredD1221 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1221 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1221_eq : pairedProblem rows1221 cols1221 requiredD1221 requiredS1221 =
    MomentData.problem1221 := by rfl
theorem leaf1221 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1221++rows1221))
    (hc : (q.map Prod.snd).Perm (cols1221++cols1221))
    (hd : ∀ k ∈ requiredD1221, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1221, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1221 cols1221 requiredD1221 requiredS1221
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1221_eq] at model
  exact MomentData.excluded1221 ds ss model
def rows1222 : List Int := [0,1,4,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1222 : List Int := [0,1,4,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1222 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1222 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1222_eq : pairedProblem rows1222 cols1222 requiredD1222 requiredS1222 =
    MomentData.problem1222 := by rfl
theorem leaf1222 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1222++rows1222))
    (hc : (q.map Prod.snd).Perm (cols1222++cols1222))
    (hd : ∀ k ∈ requiredD1222, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1222, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1222 cols1222 requiredD1222 requiredS1222
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1222_eq] at model
  exact MomentData.excluded1222 ds ss model
def rows1223 : List Int := [0,1,2,5,8,11,14,17,20,22,23,26,27,28,29]
def cols1223 : List Int := [0,1,2,5,8,11,14,17,20,22,23,26,27,28,29]
def requiredD1223 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1223 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1223_eq : pairedProblem rows1223 cols1223 requiredD1223 requiredS1223 =
    MomentData.problem1223 := by rfl
theorem leaf1223 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1223++rows1223))
    (hc : (q.map Prod.snd).Perm (cols1223++cols1223))
    (hd : ∀ k ∈ requiredD1223, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1223, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1223 cols1223 requiredD1223 requiredS1223
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1223_eq] at model
  exact MomentData.excluded1223 ds ss model
def rows1224 : List Int := [0,1,2,5,8,11,14,17,20,22,23,26,27,28,29]
def cols1224 : List Int := [0,1,2,5,8,11,14,17,20,22,23,26,27,28,29]
def requiredD1224 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1224 : List Int := [10,13,16,19,22,25,27,28,29,31,34,37,40,43,46]
theorem problem1224_eq : pairedProblem rows1224 cols1224 requiredD1224 requiredS1224 =
    MomentData.problem1224 := by rfl
theorem leaf1224 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1224++rows1224))
    (hc : (q.map Prod.snd).Perm (cols1224++cols1224))
    (hd : ∀ k ∈ requiredD1224, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1224, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1224 cols1224 requiredD1224 requiredS1224
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1224_eq] at model
  exact MomentData.excluded1224 ds ss model
def rows1225 : List Int := [0,1,2,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1225 : List Int := [0,1,2,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1225 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1225 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1225_eq : pairedProblem rows1225 cols1225 requiredD1225 requiredS1225 =
    MomentData.problem1225 := by rfl
theorem leaf1225 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1225++rows1225))
    (hc : (q.map Prod.snd).Perm (cols1225++cols1225))
    (hd : ∀ k ∈ requiredD1225, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1225, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1225 cols1225 requiredD1225 requiredS1225
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1225_eq] at model
  exact MomentData.excluded1225 ds ss model
def rows1226 : List Int := [0,1,2,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1226 : List Int := [0,1,2,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1226 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1226 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1226_eq : pairedProblem rows1226 cols1226 requiredD1226 requiredS1226 =
    MomentData.problem1226 := by rfl
theorem leaf1226 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1226++rows1226))
    (hc : (q.map Prod.snd).Perm (cols1226++cols1226))
    (hd : ∀ k ∈ requiredD1226, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1226, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1226 cols1226 requiredD1226 requiredS1226
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1226_eq] at model
  exact MomentData.excluded1226 ds ss model
def rows1227 : List Int := [0,1,4,6,7,10,13,16,19,22,25,26,27,28,29]
def cols1227 : List Int := [0,1,4,6,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1227 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1227 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1227_eq : pairedProblem rows1227 cols1227 requiredD1227 requiredS1227 =
    MomentData.problem1227 := by rfl
theorem leaf1227 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1227++rows1227))
    (hc : (q.map Prod.snd).Perm (cols1227++cols1227))
    (hd : ∀ k ∈ requiredD1227, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1227, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1227 cols1227 requiredD1227 requiredS1227
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1227_eq] at model
  exact MomentData.excluded1227 ds ss model
def rows1228 : List Int := [0,1,4,6,7,10,13,16,19,22,25,26,27,28,29]
def cols1228 : List Int := [0,1,4,6,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1228 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1228 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1228_eq : pairedProblem rows1228 cols1228 requiredD1228 requiredS1228 =
    MomentData.problem1228 := by rfl
theorem leaf1228 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1228++rows1228))
    (hc : (q.map Prod.snd).Perm (cols1228++cols1228))
    (hd : ∀ k ∈ requiredD1228, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1228, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1228 cols1228 requiredD1228 requiredS1228
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1228_eq] at model
  exact MomentData.excluded1228 ds ss model
def rows1229 : List Int := [0,1,5,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1229 : List Int := [0,1,5,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1229 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1229 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1229_eq : pairedProblem rows1229 cols1229 requiredD1229 requiredS1229 =
    MomentData.problem1229 := by rfl
theorem leaf1229 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1229++rows1229))
    (hc : (q.map Prod.snd).Perm (cols1229++cols1229))
    (hd : ∀ k ∈ requiredD1229, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1229, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1229 cols1229 requiredD1229 requiredS1229
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1229_eq] at model
  exact MomentData.excluded1229 ds ss model
def rows1230 : List Int := [0,1,2,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1230 : List Int := [0,1,2,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1230 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1230 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1230_eq : pairedProblem rows1230 cols1230 requiredD1230 requiredS1230 =
    MomentData.problem1230 := by rfl
theorem leaf1230 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1230++rows1230))
    (hc : (q.map Prod.snd).Perm (cols1230++cols1230))
    (hd : ∀ k ∈ requiredD1230, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1230, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1230 cols1230 requiredD1230 requiredS1230
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1230_eq] at model
  exact MomentData.excluded1230 ds ss model
def rows1231 : List Int := [0,1,2,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1231 : List Int := [0,1,2,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1231 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1231 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1231_eq : pairedProblem rows1231 cols1231 requiredD1231 requiredS1231 =
    MomentData.problem1231 := by rfl
theorem leaf1231 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1231++rows1231))
    (hc : (q.map Prod.snd).Perm (cols1231++cols1231))
    (hd : ∀ k ∈ requiredD1231, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1231, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1231 cols1231 requiredD1231 requiredS1231
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1231_eq] at model
  exact MomentData.excluded1231 ds ss model
def rows1232 : List Int := [0,1,2,11,12,13,14,15,16,17,22,26,27,28,29]
def cols1232 : List Int := [0,1,2,11,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1232 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1232 : List Int := [13,22,23,24,25,26,27,28,29,30,31,32,33,34,43]
theorem problem1232_eq : pairedProblem rows1232 cols1232 requiredD1232 requiredS1232 =
    MomentData.problem1232 := by rfl
theorem leaf1232 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1232++rows1232))
    (hc : (q.map Prod.snd).Perm (cols1232++cols1232))
    (hd : ∀ k ∈ requiredD1232, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1232, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1232 cols1232 requiredD1232 requiredS1232
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1232_eq] at model
  exact MomentData.excluded1232 ds ss model
def rows1233 : List Int := [0,1,6,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1233 : List Int := [0,1,6,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1233 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1233 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1233_eq : pairedProblem rows1233 cols1233 requiredD1233 requiredS1233 =
    MomentData.problem1233 := by rfl
theorem leaf1233 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1233++rows1233))
    (hc : (q.map Prod.snd).Perm (cols1233++cols1233))
    (hd : ∀ k ∈ requiredD1233, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1233, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1233 cols1233 requiredD1233 requiredS1233
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1233_eq] at model
  exact MomentData.excluded1233 ds ss model
def rows1234 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1234 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1234 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1234 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43,46]
theorem problem1234_eq : pairedProblem rows1234 cols1234 requiredD1234 requiredS1234 =
    MomentData.problem1234 := by rfl
theorem leaf1234 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1234++rows1234))
    (hc : (q.map Prod.snd).Perm (cols1234++cols1234))
    (hd : ∀ k ∈ requiredD1234, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1234, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1234 cols1234 requiredD1234 requiredS1234
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1234_eq] at model
  exact MomentData.excluded1234 ds ss model
def rows1235 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1235 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1235 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1235 : List Int := [10,13,16,19,22,25,28,29,31,34,37,40,43,46]
theorem problem1235_eq : pairedProblem rows1235 cols1235 requiredD1235 requiredS1235 =
    MomentData.problem1235 := by rfl
theorem leaf1235 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1235++rows1235))
    (hc : (q.map Prod.snd).Perm (cols1235++cols1235))
    (hd : ∀ k ∈ requiredD1235, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1235, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1235 cols1235 requiredD1235 requiredS1235
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1235_eq] at model
  exact MomentData.excluded1235 ds ss model
def rows1236 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1236 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1236 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1236 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1236_eq : pairedProblem rows1236 cols1236 requiredD1236 requiredS1236 =
    MomentData.problem1236 := by rfl
theorem leaf1236 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1236++rows1236))
    (hc : (q.map Prod.snd).Perm (cols1236++cols1236))
    (hd : ∀ k ∈ requiredD1236, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1236, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1236 cols1236 requiredD1236 requiredS1236
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1236_eq] at model
  exact MomentData.excluded1236 ds ss model
def rows1237 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1237 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1237 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1237 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43]
theorem problem1237_eq : pairedProblem rows1237 cols1237 requiredD1237 requiredS1237 =
    MomentData.problem1237 := by rfl
theorem leaf1237 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1237++rows1237))
    (hc : (q.map Prod.snd).Perm (cols1237++cols1237))
    (hd : ∀ k ∈ requiredD1237, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1237, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1237 cols1237 requiredD1237 requiredS1237
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1237_eq] at model
  exact MomentData.excluded1237 ds ss model
def rows1238 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def cols1238 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def requiredD1238 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1238 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1238_eq : pairedProblem rows1238 cols1238 requiredD1238 requiredS1238 =
    MomentData.problem1238 := by rfl
theorem leaf1238 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1238++rows1238))
    (hc : (q.map Prod.snd).Perm (cols1238++cols1238))
    (hd : ∀ k ∈ requiredD1238, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1238, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1238 cols1238 requiredD1238 requiredS1238
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1238_eq] at model
  exact MomentData.excluded1238 ds ss model
def rows1239 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def cols1239 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def requiredD1239 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1239 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1239_eq : pairedProblem rows1239 cols1239 requiredD1239 requiredS1239 =
    MomentData.problem1239 := by rfl
theorem leaf1239 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1239++rows1239))
    (hc : (q.map Prod.snd).Perm (cols1239++cols1239))
    (hd : ∀ k ∈ requiredD1239, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1239, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1239 cols1239 requiredD1239 requiredS1239
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1239_eq] at model
  exact MomentData.excluded1239 ds ss model
def rows1240 : List Int := [0,1,7,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1240 : List Int := [0,1,7,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1240 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1240 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1240_eq : pairedProblem rows1240 cols1240 requiredD1240 requiredS1240 =
    MomentData.problem1240 := by rfl
theorem leaf1240 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1240++rows1240))
    (hc : (q.map Prod.snd).Perm (cols1240++cols1240))
    (hd : ∀ k ∈ requiredD1240, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1240, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1240 cols1240 requiredD1240 requiredS1240
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1240_eq] at model
  exact MomentData.excluded1240 ds ss model
def rows1241 : List Int := [0,1,7,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1241 : List Int := [0,1,7,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1241 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1241 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1241_eq : pairedProblem rows1241 cols1241 requiredD1241 requiredS1241 =
    MomentData.problem1241 := by rfl
theorem leaf1241 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1241++rows1241))
    (hc : (q.map Prod.snd).Perm (cols1241++cols1241))
    (hd : ∀ k ∈ requiredD1241, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1241, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1241 cols1241 requiredD1241 requiredS1241
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1241_eq] at model
  exact MomentData.excluded1241 ds ss model
def rows1242 : List Int := [0,1,4,7,9,10,13,16,19,22,25,26,27,28,29]
def cols1242 : List Int := [0,1,4,7,9,10,13,16,19,22,25,26,27,28,29]
def requiredD1242 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1242 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1242_eq : pairedProblem rows1242 cols1242 requiredD1242 requiredS1242 =
    MomentData.problem1242 := by rfl
theorem leaf1242 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1242++rows1242))
    (hc : (q.map Prod.snd).Perm (cols1242++cols1242))
    (hd : ∀ k ∈ requiredD1242, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1242, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1242 cols1242 requiredD1242 requiredS1242
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1242_eq] at model
  exact MomentData.excluded1242 ds ss model
def rows1243 : List Int := [0,1,4,7,9,10,13,16,19,22,25,26,27,28,29]
def cols1243 : List Int := [0,1,4,7,9,10,13,16,19,22,25,26,27,28,29]
def requiredD1243 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1243 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1243_eq : pairedProblem rows1243 cols1243 requiredD1243 requiredS1243 =
    MomentData.problem1243 := by rfl
theorem leaf1243 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1243++rows1243))
    (hc : (q.map Prod.snd).Perm (cols1243++cols1243))
    (hd : ∀ k ∈ requiredD1243, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1243, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1243 cols1243 requiredD1243 requiredS1243
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1243_eq] at model
  exact MomentData.excluded1243 ds ss model
def rows1244 : List Int := [0,1,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1244 : List Int := [0,1,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1244 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1244 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1244_eq : pairedProblem rows1244 cols1244 requiredD1244 requiredS1244 =
    MomentData.problem1244 := by rfl
theorem leaf1244 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1244++rows1244))
    (hc : (q.map Prod.snd).Perm (cols1244++cols1244))
    (hd : ∀ k ∈ requiredD1244, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1244, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1244 cols1244 requiredD1244 requiredS1244
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1244_eq] at model
  exact MomentData.excluded1244 ds ss model
def rows1245 : List Int := [0,1,4,7,10,11,13,16,19,22,25,26,27,28,29]
def cols1245 : List Int := [0,1,4,7,10,11,13,16,19,22,25,26,27,28,29]
def requiredD1245 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1245 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1245_eq : pairedProblem rows1245 cols1245 requiredD1245 requiredS1245 =
    MomentData.problem1245 := by rfl
theorem leaf1245 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1245++rows1245))
    (hc : (q.map Prod.snd).Perm (cols1245++cols1245))
    (hd : ∀ k ∈ requiredD1245, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1245, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1245 cols1245 requiredD1245 requiredS1245
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1245_eq] at model
  exact MomentData.excluded1245 ds ss model
def rows1246 : List Int := [0,1,4,7,10,11,13,16,19,22,25,26,27,28,29]
def cols1246 : List Int := [0,1,4,7,10,11,13,16,19,22,25,26,27,28,29]
def requiredD1246 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1246 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1246_eq : pairedProblem rows1246 cols1246 requiredD1246 requiredS1246 =
    MomentData.problem1246 := by rfl
theorem leaf1246 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1246++rows1246))
    (hc : (q.map Prod.snd).Perm (cols1246++cols1246))
    (hd : ∀ k ∈ requiredD1246, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1246, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1246 cols1246 requiredD1246 requiredS1246
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1246_eq] at model
  exact MomentData.excluded1246 ds ss model
def rows1247 : List Int := [0,1,4,7,10,12,13,16,19,22,25,26,27,28,29]
def cols1247 : List Int := [0,1,4,7,10,12,13,16,19,22,25,26,27,28,29]
def requiredD1247 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1247 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1247_eq : pairedProblem rows1247 cols1247 requiredD1247 requiredS1247 =
    MomentData.problem1247 := by rfl
theorem leaf1247 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1247++rows1247))
    (hc : (q.map Prod.snd).Perm (cols1247++cols1247))
    (hd : ∀ k ∈ requiredD1247, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1247, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1247 cols1247 requiredD1247 requiredS1247
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1247_eq] at model
  exact MomentData.excluded1247 ds ss model
def rows1248 : List Int := [0,1,4,7,10,12,13,16,19,22,25,26,27,28,29]
def cols1248 : List Int := [0,1,4,7,10,12,13,16,19,22,25,26,27,28,29]
def requiredD1248 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1248 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1248_eq : pairedProblem rows1248 cols1248 requiredD1248 requiredS1248 =
    MomentData.problem1248 := by rfl
theorem leaf1248 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1248++rows1248))
    (hc : (q.map Prod.snd).Perm (cols1248++cols1248))
    (hd : ∀ k ∈ requiredD1248, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1248, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1248 cols1248 requiredD1248 requiredS1248
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1248_eq] at model
  exact MomentData.excluded1248 ds ss model
def rows1249 : List Int := [0,1,4,7,10,13,14,16,19,22,25,26,27,28,29]
def cols1249 : List Int := [0,1,4,7,10,13,14,16,19,22,25,26,27,28,29]
def requiredD1249 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1249 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1249_eq : pairedProblem rows1249 cols1249 requiredD1249 requiredS1249 =
    MomentData.problem1249 := by rfl
theorem leaf1249 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1249++rows1249))
    (hc : (q.map Prod.snd).Perm (cols1249++cols1249))
    (hd : ∀ k ∈ requiredD1249, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1249, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1249 cols1249 requiredD1249 requiredS1249
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1249_eq] at model
  exact MomentData.excluded1249 ds ss model
def rows1250 : List Int := [0,1,4,7,10,13,14,16,19,22,25,26,27,28,29]
def cols1250 : List Int := [0,1,4,7,10,13,14,16,19,22,25,26,27,28,29]
def requiredD1250 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1250 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1250_eq : pairedProblem rows1250 cols1250 requiredD1250 requiredS1250 =
    MomentData.problem1250 := by rfl
theorem leaf1250 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1250++rows1250))
    (hc : (q.map Prod.snd).Perm (cols1250++cols1250))
    (hd : ∀ k ∈ requiredD1250, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1250, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1250 cols1250 requiredD1250 requiredS1250
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1250_eq] at model
  exact MomentData.excluded1250 ds ss model
def rows1251 : List Int := [0,1,4,7,10,13,15,16,19,22,25,26,27,28,29]
def cols1251 : List Int := [0,1,4,7,10,13,15,16,19,22,25,26,27,28,29]
def requiredD1251 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1251 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1251_eq : pairedProblem rows1251 cols1251 requiredD1251 requiredS1251 =
    MomentData.problem1251 := by rfl
theorem leaf1251 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1251++rows1251))
    (hc : (q.map Prod.snd).Perm (cols1251++cols1251))
    (hd : ∀ k ∈ requiredD1251, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1251, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1251 cols1251 requiredD1251 requiredS1251
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1251_eq] at model
  exact MomentData.excluded1251 ds ss model
def rows1252 : List Int := [0,1,4,7,10,13,15,16,19,22,25,26,27,28,29]
def cols1252 : List Int := [0,1,4,7,10,13,15,16,19,22,25,26,27,28,29]
def requiredD1252 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1252 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1252_eq : pairedProblem rows1252 cols1252 requiredD1252 requiredS1252 =
    MomentData.problem1252 := by rfl
theorem leaf1252 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1252++rows1252))
    (hc : (q.map Prod.snd).Perm (cols1252++cols1252))
    (hd : ∀ k ∈ requiredD1252, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1252, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1252 cols1252 requiredD1252 requiredS1252
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1252_eq] at model
  exact MomentData.excluded1252 ds ss model
def rows1253 : List Int := [0,7,8,9,10,11,12,13,14,24,25,26,27,28,29]
def cols1253 : List Int := [0,7,8,9,10,11,12,13,14,24,25,26,27,28,29]
def requiredD1253 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1253 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,38]
theorem problem1253_eq : pairedProblem rows1253 cols1253 requiredD1253 requiredS1253 =
    MomentData.problem1253 := by rfl
theorem leaf1253 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1253++rows1253))
    (hc : (q.map Prod.snd).Perm (cols1253++cols1253))
    (hd : ∀ k ∈ requiredD1253, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1253, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1253 cols1253 requiredD1253 requiredS1253
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1253_eq] at model
  exact MomentData.excluded1253 ds ss model
def rows1254 : List Int := [0,1,4,7,10,13,16,17,19,22,25,26,27,28,29]
def cols1254 : List Int := [0,1,4,7,10,13,16,17,19,22,25,26,27,28,29]
def requiredD1254 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1254 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1254_eq : pairedProblem rows1254 cols1254 requiredD1254 requiredS1254 =
    MomentData.problem1254 := by rfl
theorem leaf1254 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1254++rows1254))
    (hc : (q.map Prod.snd).Perm (cols1254++cols1254))
    (hd : ∀ k ∈ requiredD1254, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1254, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1254 cols1254 requiredD1254 requiredS1254
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1254_eq] at model
  exact MomentData.excluded1254 ds ss model
def rows1255 : List Int := [0,1,4,7,10,13,16,17,19,22,25,26,27,28,29]
def cols1255 : List Int := [0,1,4,7,10,13,16,17,19,22,25,26,27,28,29]
def requiredD1255 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1255 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1255_eq : pairedProblem rows1255 cols1255 requiredD1255 requiredS1255 =
    MomentData.problem1255 := by rfl
theorem leaf1255 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1255++rows1255))
    (hc : (q.map Prod.snd).Perm (cols1255++cols1255))
    (hd : ∀ k ∈ requiredD1255, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1255, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1255 cols1255 requiredD1255 requiredS1255
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1255_eq] at model
  exact MomentData.excluded1255 ds ss model
def rows1256 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1256 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1256 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1256 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem1256_eq : pairedProblem rows1256 cols1256 requiredD1256 requiredS1256 =
    MomentData.problem1256 := by rfl
theorem leaf1256 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1256++rows1256))
    (hc : (q.map Prod.snd).Perm (cols1256++cols1256))
    (hd : ∀ k ∈ requiredD1256, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1256, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1256 cols1256 requiredD1256 requiredS1256
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1256_eq] at model
  exact MomentData.excluded1256 ds ss model
def rows1257 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1257 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1257 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1257 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem1257_eq : pairedProblem rows1257 cols1257 requiredD1257 requiredS1257 =
    MomentData.problem1257 := by rfl
theorem leaf1257 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1257++rows1257))
    (hc : (q.map Prod.snd).Perm (cols1257++cols1257))
    (hd : ∀ k ∈ requiredD1257, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1257, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1257 cols1257 requiredD1257 requiredS1257
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1257_eq] at model
  exact MomentData.excluded1257 ds ss model
def rows1258 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1258 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1258 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1258 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1258_eq : pairedProblem rows1258 cols1258 requiredD1258 requiredS1258 =
    MomentData.problem1258 := by rfl
theorem leaf1258 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1258++rows1258))
    (hc : (q.map Prod.snd).Perm (cols1258++cols1258))
    (hd : ∀ k ∈ requiredD1258, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1258, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1258 cols1258 requiredD1258 requiredS1258
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1258_eq] at model
  exact MomentData.excluded1258 ds ss model
def rows1259 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1259 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1259 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1259 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem1259_eq : pairedProblem rows1259 cols1259 requiredD1259 requiredS1259 =
    MomentData.problem1259 := by rfl
theorem leaf1259 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1259++rows1259))
    (hc : (q.map Prod.snd).Perm (cols1259++cols1259))
    (hd : ∀ k ∈ requiredD1259, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1259, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1259 cols1259 requiredD1259 requiredS1259
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1259_eq] at model
  exact MomentData.excluded1259 ds ss model
def rows1260 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def cols1260 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def requiredD1260 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1260 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1260_eq : pairedProblem rows1260 cols1260 requiredD1260 requiredS1260 =
    MomentData.problem1260 := by rfl
theorem leaf1260 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1260++rows1260))
    (hc : (q.map Prod.snd).Perm (cols1260++cols1260))
    (hd : ∀ k ∈ requiredD1260, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1260, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1260 cols1260 requiredD1260 requiredS1260
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1260_eq] at model
  exact MomentData.excluded1260 ds ss model
def rows1261 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def cols1261 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def requiredD1261 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1261 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1261_eq : pairedProblem rows1261 cols1261 requiredD1261 requiredS1261 =
    MomentData.problem1261 := by rfl
theorem leaf1261 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1261++rows1261))
    (hc : (q.map Prod.snd).Perm (cols1261++cols1261))
    (hd : ∀ k ∈ requiredD1261, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1261, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1261 cols1261 requiredD1261 requiredS1261
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1261_eq] at model
  exact MomentData.excluded1261 ds ss model
def rows1262 : List Int := [0,1,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1262 : List Int := [0,1,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1262 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1262 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1262_eq : pairedProblem rows1262 cols1262 requiredD1262 requiredS1262 =
    MomentData.problem1262 := by rfl
theorem leaf1262 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1262++rows1262))
    (hc : (q.map Prod.snd).Perm (cols1262++cols1262))
    (hd : ∀ k ∈ requiredD1262, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1262, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1262 cols1262 requiredD1262 requiredS1262
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1262_eq] at model
  exact MomentData.excluded1262 ds ss model
def rows1263 : List Int := [0,3,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1263 : List Int := [0,3,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1263 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1263 : List Int := [9,18,19,20,21,22,23,24,25,26,27,28,29,30,39]
theorem problem1263_eq : pairedProblem rows1263 cols1263 requiredD1263 requiredS1263 =
    MomentData.problem1263 := by rfl
theorem leaf1263 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1263++rows1263))
    (hc : (q.map Prod.snd).Perm (cols1263++cols1263))
    (hd : ∀ k ∈ requiredD1263, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1263, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1263 cols1263 requiredD1263 requiredS1263
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1263_eq] at model
  exact MomentData.excluded1263 ds ss model
def rows1264 : List Int := [0,3,4,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1264 : List Int := [0,3,4,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1264 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1264 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1264_eq : pairedProblem rows1264 cols1264 requiredD1264 requiredS1264 =
    MomentData.problem1264 := by rfl
theorem leaf1264 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1264++rows1264))
    (hc : (q.map Prod.snd).Perm (cols1264++cols1264))
    (hd : ∀ k ∈ requiredD1264, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1264, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1264 cols1264 requiredD1264 requiredS1264
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1264_eq] at model
  exact MomentData.excluded1264 ds ss model
def rows1265 : List Int := [0,1,10,11,12,13,14,15,16,19,25,26,27,28,29]
def cols1265 : List Int := [0,1,10,11,12,13,14,15,16,19,25,26,27,28,29]
def requiredD1265 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1265 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1265_eq : pairedProblem rows1265 cols1265 requiredD1265 requiredS1265 =
    MomentData.problem1265 := by rfl
theorem leaf1265 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1265++rows1265))
    (hc : (q.map Prod.snd).Perm (cols1265++cols1265))
    (hd : ∀ k ∈ requiredD1265, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1265, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1265 cols1265 requiredD1265 requiredS1265
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1265_eq] at model
  exact MomentData.excluded1265 ds ss model
def rows1266 : List Int := [0,1,10,11,12,13,14,15,16,19,25,26,27,28,29]
def cols1266 : List Int := [0,1,10,11,12,13,14,15,16,19,25,26,27,28,29]
def requiredD1266 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1266 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1266_eq : pairedProblem rows1266 cols1266 requiredD1266 requiredS1266 =
    MomentData.problem1266 := by rfl
theorem leaf1266 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1266++rows1266))
    (hc : (q.map Prod.snd).Perm (cols1266++cols1266))
    (hd : ∀ k ∈ requiredD1266, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1266, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1266 cols1266 requiredD1266 requiredS1266
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1266_eq] at model
  exact MomentData.excluded1266 ds ss model
def rows1267 : List Int := [0,1,4,7,10,13,16,19,20,22,25,26,27,28,29]
def cols1267 : List Int := [0,1,4,7,10,13,16,19,20,22,25,26,27,28,29]
def requiredD1267 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1267 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1267_eq : pairedProblem rows1267 cols1267 requiredD1267 requiredS1267 =
    MomentData.problem1267 := by rfl
theorem leaf1267 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1267++rows1267))
    (hc : (q.map Prod.snd).Perm (cols1267++cols1267))
    (hd : ∀ k ∈ requiredD1267, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1267, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1267 cols1267 requiredD1267 requiredS1267
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1267_eq] at model
  exact MomentData.excluded1267 ds ss model
def rows1268 : List Int := [0,1,4,7,10,13,16,19,20,22,25,26,27,28,29]
def cols1268 : List Int := [0,1,4,7,10,13,16,19,20,22,25,26,27,28,29]
def requiredD1268 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1268 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1268_eq : pairedProblem rows1268 cols1268 requiredD1268 requiredS1268 =
    MomentData.problem1268 := by rfl
theorem leaf1268 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1268++rows1268))
    (hc : (q.map Prod.snd).Perm (cols1268++cols1268))
    (hd : ∀ k ∈ requiredD1268, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1268, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1268 cols1268 requiredD1268 requiredS1268
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1268_eq] at model
  exact MomentData.excluded1268 ds ss model
def rows1269 : List Int := [0,4,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1269 : List Int := [0,4,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1269 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1269 : List Int := [9,18,19,20,21,22,23,24,25,26,27,28,29,30,39]
theorem problem1269_eq : pairedProblem rows1269 cols1269 requiredD1269 requiredS1269 =
    MomentData.problem1269 := by rfl
theorem leaf1269 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1269++rows1269))
    (hc : (q.map Prod.snd).Perm (cols1269++cols1269))
    (hd : ∀ k ∈ requiredD1269, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1269, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1269 cols1269 requiredD1269 requiredS1269
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1269_eq] at model
  exact MomentData.excluded1269 ds ss model
def rows1270 : List Int := [0,1,10,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1270 : List Int := [0,1,10,11,12,13,14,15,16,20,25,26,27,28,29]
def requiredD1270 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1270 : List Int := [11,20,21,22,23,24,25,26,27,28,29,30,31,32,41]
theorem problem1270_eq : pairedProblem rows1270 cols1270 requiredD1270 requiredS1270 =
    MomentData.problem1270 := by rfl
theorem leaf1270 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1270++rows1270))
    (hc : (q.map Prod.snd).Perm (cols1270++cols1270))
    (hd : ∀ k ∈ requiredD1270, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1270, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1270 cols1270 requiredD1270 requiredS1270
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1270_eq] at model
  exact MomentData.excluded1270 ds ss model
def rows1271 : List Int := [0,1,4,7,10,13,16,19,21,22,25,26,27,28,29]
def cols1271 : List Int := [0,1,4,7,10,13,16,19,21,22,25,26,27,28,29]
def requiredD1271 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1271 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1271_eq : pairedProblem rows1271 cols1271 requiredD1271 requiredS1271 =
    MomentData.problem1271 := by rfl
theorem leaf1271 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1271++rows1271))
    (hc : (q.map Prod.snd).Perm (cols1271++cols1271))
    (hd : ∀ k ∈ requiredD1271, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1271, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1271 cols1271 requiredD1271 requiredS1271
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1271_eq] at model
  exact MomentData.excluded1271 ds ss model
def rows1272 : List Int := [0,1,4,7,10,13,16,19,21,22,25,26,27,28,29]
def cols1272 : List Int := [0,1,4,7,10,13,16,19,21,22,25,26,27,28,29]
def requiredD1272 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1272 : List Int := [8,11,14,17,20,23,25,26,27,29,32,35,38,41,44]
theorem problem1272_eq : pairedProblem rows1272 cols1272 requiredD1272 requiredS1272 =
    MomentData.problem1272 := by rfl
theorem leaf1272 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1272++rows1272))
    (hc : (q.map Prod.snd).Perm (cols1272++cols1272))
    (hd : ∀ k ∈ requiredD1272, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1272, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1272 cols1272 requiredD1272 requiredS1272
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1272_eq] at model
  exact MomentData.excluded1272 ds ss model
def rows1273 : List Int := [0,3,5,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1273 : List Int := [0,3,5,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1273 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1273 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1273_eq : pairedProblem rows1273 cols1273 requiredD1273 requiredS1273 =
    MomentData.problem1273 := by rfl
theorem leaf1273 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1273++rows1273))
    (hc : (q.map Prod.snd).Perm (cols1273++cols1273))
    (hd : ∀ k ∈ requiredD1273, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1273, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1273 cols1273 requiredD1273 requiredS1273
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1273_eq] at model
  exact MomentData.excluded1273 ds ss model
def rows1274 : List Int := [0,3,5,6,9,12,15,18,21,24,25,26,27,28,29]
def cols1274 : List Int := [0,3,5,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1274 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1274 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1274_eq : pairedProblem rows1274 cols1274 requiredD1274 requiredS1274 =
    MomentData.problem1274 := by rfl
theorem leaf1274 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1274++rows1274))
    (hc : (q.map Prod.snd).Perm (cols1274++cols1274))
    (hd : ∀ k ∈ requiredD1274, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1274, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1274 cols1274 requiredD1274 requiredS1274
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1274_eq] at model
  exact MomentData.excluded1274 ds ss model
def rows1275 : List Int := [0,5,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1275 : List Int := [0,5,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1275 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1275 : List Int := [9,18,19,20,21,22,23,24,25,26,27,28,29,30,39]
theorem problem1275_eq : pairedProblem rows1275 cols1275 requiredD1275 requiredS1275 =
    MomentData.problem1275 := by rfl
theorem leaf1275 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1275++rows1275))
    (hc : (q.map Prod.snd).Perm (cols1275++cols1275))
    (hd : ∀ k ∈ requiredD1275, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1275, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1275 cols1275 requiredD1275 requiredS1275
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1275_eq] at model
  exact MomentData.excluded1275 ds ss model
def rows1276 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols1276 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD1276 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1276 : List Int := [5,8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem1276_eq : pairedProblem rows1276 cols1276 requiredD1276 requiredS1276 =
    MomentData.problem1276 := by rfl
theorem leaf1276 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1276++rows1276))
    (hc : (q.map Prod.snd).Perm (cols1276++cols1276))
    (hd : ∀ k ∈ requiredD1276, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1276, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1276 cols1276 requiredD1276 requiredS1276
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1276_eq] at model
  exact MomentData.excluded1276 ds ss model
def rows1277 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols1277 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD1277 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1277 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem1277_eq : pairedProblem rows1277 cols1277 requiredD1277 requiredS1277 =
    MomentData.problem1277 := by rfl
theorem leaf1277 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1277++rows1277))
    (hc : (q.map Prod.snd).Perm (cols1277++cols1277))
    (hd : ∀ k ∈ requiredD1277, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1277, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1277 cols1277 requiredD1277 requiredS1277
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1277_eq] at model
  exact MomentData.excluded1277 ds ss model
def rows1278 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols1278 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD1278 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1278 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem1278_eq : pairedProblem rows1278 cols1278 requiredD1278 requiredS1278 =
    MomentData.problem1278 := by rfl
theorem leaf1278 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1278++rows1278))
    (hc : (q.map Prod.snd).Perm (cols1278++cols1278))
    (hd : ∀ k ∈ requiredD1278, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1278, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1278 cols1278 requiredD1278 requiredS1278
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1278_eq] at model
  exact MomentData.excluded1278 ds ss model
def rows1279 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols1279 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD1279 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1279 : List Int := [5,8,11,14,17,20,23,26,27,29,32,35,38,41]
theorem problem1279_eq : pairedProblem rows1279 cols1279 requiredD1279 requiredS1279 =
    MomentData.problem1279 := by rfl
theorem leaf1279 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1279++rows1279))
    (hc : (q.map Prod.snd).Perm (cols1279++cols1279))
    (hd : ∀ k ∈ requiredD1279, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1279, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1279 cols1279 requiredD1279 requiredS1279
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1279_eq] at model
  exact MomentData.excluded1279 ds ss model
#print axioms leaf1152
end Gardner.Kernel.MomentContexts
