import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows128 : List Int := [0,1,2,3,4,9,15,18,23,24,25,26,27,28,29]
def cols128 : List Int := [0,1,2,3,4,9,15,18,23,24,25,26,27,28,29]
def requiredD128 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS128 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem128_eq : pairedProblem rows128 cols128 requiredD128 requiredS128 =
    MomentData.problem128 := by rfl
theorem leaf128 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows128++rows128))
    (hc : (q.map Prod.snd).Perm (cols128++cols128))
    (hd : ∀ k ∈ requiredD128, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS128, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows128 cols128 requiredD128 requiredS128
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem128_eq] at model
  exact MomentData.excluded128 ds ss model
def rows129 : List Int := [0,1,2,3,4,5,10,16,19,24,25,26,27,28,29]
def cols129 : List Int := [0,1,2,3,4,5,10,16,19,24,25,26,27,28,29]
def requiredD129 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS129 : List Int := [18,20,22,24,26,27,28,29,30,31,32,34,36,38,40]
theorem problem129_eq : pairedProblem rows129 cols129 requiredD129 requiredS129 =
    MomentData.problem129 := by rfl
theorem leaf129 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows129++rows129))
    (hc : (q.map Prod.snd).Perm (cols129++cols129))
    (hd : ∀ k ∈ requiredD129, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS129, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows129 cols129 requiredD129 requiredS129
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem129_eq] at model
  exact MomentData.excluded129 ds ss model
def rows130 : List Int := [0,1,2,3,4,5,6,11,17,20,25,26,27,28,29]
def cols130 : List Int := [0,1,2,3,4,5,6,11,17,20,25,26,27,28,29]
def requiredD130 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS130 : List Int := [20,22,24,26,28,29,30,31,32,33,34,36,38,40,42]
theorem problem130_eq : pairedProblem rows130 cols130 requiredD130 requiredS130 =
    MomentData.problem130 := by rfl
theorem leaf130 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows130++rows130))
    (hc : (q.map Prod.snd).Perm (cols130++cols130))
    (hd : ∀ k ∈ requiredD130, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS130, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows130 cols130 requiredD130 requiredS130
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem130_eq] at model
  exact MomentData.excluded130 ds ss model
def rows131 : List Int := [0,1,2,3,4,9,12,18,23,24,25,26,27,28,29]
def cols131 : List Int := [0,1,2,3,4,9,12,18,23,24,25,26,27,28,29]
def requiredD131 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS131 : List Int := [16,18,20,22,24,25,26,27,28,29,30,32,34,36,38]
theorem problem131_eq : pairedProblem rows131 cols131 requiredD131 requiredS131 =
    MomentData.problem131 := by rfl
theorem leaf131 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows131++rows131))
    (hc : (q.map Prod.snd).Perm (cols131++cols131))
    (hd : ∀ k ∈ requiredD131, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS131, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows131 cols131 requiredD131 requiredS131
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem131_eq] at model
  exact MomentData.excluded131 ds ss model
def rows132 : List Int := [0,1,2,3,4,5,10,13,19,24,25,26,27,28,29]
def cols132 : List Int := [0,1,2,3,4,5,10,13,19,24,25,26,27,28,29]
def requiredD132 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS132 : List Int := [18,20,22,24,26,27,28,29,30,31,32,34,36,38,40]
theorem problem132_eq : pairedProblem rows132 cols132 requiredD132 requiredS132 =
    MomentData.problem132 := by rfl
theorem leaf132 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows132++rows132))
    (hc : (q.map Prod.snd).Perm (cols132++cols132))
    (hd : ∀ k ∈ requiredD132, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS132, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows132 cols132 requiredD132 requiredS132
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem132_eq] at model
  exact MomentData.excluded132 ds ss model
def rows133 : List Int := [0,1,2,3,4,5,6,11,14,20,25,26,27,28,29]
def cols133 : List Int := [0,1,2,3,4,5,6,11,14,20,25,26,27,28,29]
def requiredD133 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS133 : List Int := [20,22,24,26,28,29,30,31,32,33,34,36,38,40,42]
theorem problem133_eq : pairedProblem rows133 cols133 requiredD133 requiredS133 =
    MomentData.problem133 := by rfl
theorem leaf133 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows133++rows133))
    (hc : (q.map Prod.snd).Perm (cols133++cols133))
    (hd : ∀ k ∈ requiredD133, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS133, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows133 cols133 requiredD133 requiredS133
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem133_eq] at model
  exact MomentData.excluded133 ds ss model
def rows134 : List Int := [0,1,2,3,4,5,6,7,12,15,21,26,27,28,29]
def cols134 : List Int := [0,1,2,3,4,5,6,7,12,15,21,26,27,28,29]
def requiredD134 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS134 : List Int := [22,24,26,28,30,31,32,33,34,35,36,38,40,42,44]
theorem problem134_eq : pairedProblem rows134 cols134 requiredD134 requiredS134 =
    MomentData.problem134 := by rfl
theorem leaf134 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows134++rows134))
    (hc : (q.map Prod.snd).Perm (cols134++cols134))
    (hd : ∀ k ∈ requiredD134, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS134, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows134 cols134 requiredD134 requiredS134
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem134_eq] at model
  exact MomentData.excluded134 ds ss model
def rows135 : List Int := [0,1,2,3,4,9,10,17,23,24,25,26,27,28,29]
def cols135 : List Int := [0,1,2,3,4,9,10,17,23,24,25,26,27,28,29]
def requiredD135 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS135 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem135_eq : pairedProblem rows135 cols135 requiredD135 requiredS135 =
    MomentData.problem135 := by rfl
theorem leaf135 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows135++rows135))
    (hc : (q.map Prod.snd).Perm (cols135++cols135))
    (hd : ∀ k ∈ requiredD135, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS135, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows135 cols135 requiredD135 requiredS135
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem135_eq] at model
  exact MomentData.excluded135 ds ss model
def rows136 : List Int := [0,1,2,3,4,5,10,11,18,24,25,26,27,28,29]
def cols136 : List Int := [0,1,2,3,4,5,10,11,18,24,25,26,27,28,29]
def requiredD136 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS136 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem136_eq : pairedProblem rows136 cols136 requiredD136 requiredS136 =
    MomentData.problem136 := by rfl
theorem leaf136 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows136++rows136))
    (hc : (q.map Prod.snd).Perm (cols136++cols136))
    (hd : ∀ k ∈ requiredD136, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS136, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows136 cols136 requiredD136 requiredS136
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem136_eq] at model
  exact MomentData.excluded136 ds ss model
def rows137 : List Int := [0,1,2,3,4,5,6,11,12,19,25,26,27,28,29]
def cols137 : List Int := [0,1,2,3,4,5,6,11,12,19,25,26,27,28,29]
def requiredD137 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS137 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem137_eq : pairedProblem rows137 cols137 requiredD137 requiredS137 =
    MomentData.problem137 := by rfl
theorem leaf137 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows137++rows137))
    (hc : (q.map Prod.snd).Perm (cols137++cols137))
    (hd : ∀ k ∈ requiredD137, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS137, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows137 cols137 requiredD137 requiredS137
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem137_eq] at model
  exact MomentData.excluded137 ds ss model
def rows138 : List Int := [0,1,2,3,4,7,10,17,23,24,25,26,27,28,29]
def cols138 : List Int := [0,1,2,3,4,7,10,17,23,24,25,26,27,28,29]
def requiredD138 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS138 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem138_eq : pairedProblem rows138 cols138 requiredD138 requiredS138 =
    MomentData.problem138 := by rfl
theorem leaf138 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows138++rows138))
    (hc : (q.map Prod.snd).Perm (cols138++cols138))
    (hd : ∀ k ∈ requiredD138, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS138, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows138 cols138 requiredD138 requiredS138
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem138_eq] at model
  exact MomentData.excluded138 ds ss model
def rows139 : List Int := [0,1,2,3,4,5,8,11,18,24,25,26,27,28,29]
def cols139 : List Int := [0,1,2,3,4,5,8,11,18,24,25,26,27,28,29]
def requiredD139 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS139 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem139_eq : pairedProblem rows139 cols139 requiredD139 requiredS139 =
    MomentData.problem139 := by rfl
theorem leaf139 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows139++rows139))
    (hc : (q.map Prod.snd).Perm (cols139++cols139))
    (hd : ∀ k ∈ requiredD139, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS139, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows139 cols139 requiredD139 requiredS139
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem139_eq] at model
  exact MomentData.excluded139 ds ss model
def rows140 : List Int := [0,1,2,3,4,5,6,9,12,19,25,26,27,28,29]
def cols140 : List Int := [0,1,2,3,4,5,6,9,12,19,25,26,27,28,29]
def requiredD140 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS140 : List Int := [21,23,25,27,28,29,30,31,32,33,34,35,37,39,41]
theorem problem140_eq : pairedProblem rows140 cols140 requiredD140 requiredS140 =
    MomentData.problem140 := by rfl
theorem leaf140 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows140++rows140))
    (hc : (q.map Prod.snd).Perm (cols140++cols140))
    (hd : ∀ k ∈ requiredD140, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS140, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows140 cols140 requiredD140 requiredS140
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem140_eq] at model
  exact MomentData.excluded140 ds ss model
def rows141 : List Int := [0,1,2,3,4,5,8,12,17,24,25,26,27,28,29]
def cols141 : List Int := [0,1,2,3,4,5,8,12,17,24,25,26,27,28,29]
def requiredD141 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS141 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem141_eq : pairedProblem rows141 cols141 requiredD141 requiredS141 =
    MomentData.problem141 := by rfl
theorem leaf141 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows141++rows141))
    (hc : (q.map Prod.snd).Perm (cols141++cols141))
    (hd : ∀ k ∈ requiredD141, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS141, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows141 cols141 requiredD141 requiredS141
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem141_eq] at model
  exact MomentData.excluded141 ds ss model
def rows142 : List Int := [0,1,2,3,4,5,6,9,13,18,25,26,27,28,29]
def cols142 : List Int := [0,1,2,3,4,5,6,9,13,18,25,26,27,28,29]
def requiredD142 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS142 : List Int := [22,24,26,27,28,29,30,31,32,33,34,35,36,38,40]
theorem problem142_eq : pairedProblem rows142 cols142 requiredD142 requiredS142 =
    MomentData.problem142 := by rfl
theorem leaf142 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows142++rows142))
    (hc : (q.map Prod.snd).Perm (cols142++cols142))
    (hd : ∀ k ∈ requiredD142, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS142, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows142 cols142 requiredD142 requiredS142
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem142_eq] at model
  exact MomentData.excluded142 ds ss model
def rows143 : List Int := [0,1,2,3,4,5,6,7,10,14,19,26,27,28,29]
def cols143 : List Int := [0,1,2,3,4,5,6,7,10,14,19,26,27,28,29]
def requiredD143 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS143 : List Int := [24,26,28,29,30,31,32,33,34,35,36,37,38,40,42]
theorem problem143_eq : pairedProblem rows143 cols143 requiredD143 requiredS143 =
    MomentData.problem143 := by rfl
theorem leaf143 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows143++rows143))
    (hc : (q.map Prod.snd).Perm (cols143++cols143))
    (hd : ∀ k ∈ requiredD143, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS143, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows143 cols143 requiredD143 requiredS143
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem143_eq] at model
  exact MomentData.excluded143 ds ss model
def rows144 : List Int := [0,1,2,3,4,5,6,7,8,11,15,20,27,28,29]
def cols144 : List Int := [0,1,2,3,4,5,6,7,8,11,15,20,27,28,29]
def requiredD144 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS144 : List Int := [26,28,30,31,32,33,34,35,36,37,38,39,40,42,44]
theorem problem144_eq : pairedProblem rows144 cols144 requiredD144 requiredS144 =
    MomentData.problem144 := by rfl
theorem leaf144 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows144++rows144))
    (hc : (q.map Prod.snd).Perm (cols144++cols144))
    (hd : ∀ k ∈ requiredD144, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS144, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows144 cols144 requiredD144 requiredS144
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem144_eq] at model
  exact MomentData.excluded144 ds ss model
def rows145 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def cols145 : List Int := [0,1,2,3,4,6,11,16,23,24,25,26,27,28,29]
def requiredD145 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS145 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem145_eq : pairedProblem rows145 cols145 requiredD145 requiredS145 =
    MomentData.problem145 := by rfl
theorem leaf145 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows145++rows145))
    (hc : (q.map Prod.snd).Perm (cols145++cols145))
    (hd : ∀ k ∈ requiredD145, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS145, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows145 cols145 requiredD145 requiredS145
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem145_eq] at model
  exact MomentData.excluded145 ds ss model
def rows146 : List Int := [0,1,2,3,4,5,7,12,17,24,25,26,27,28,29]
def cols146 : List Int := [0,1,2,3,4,5,7,12,17,24,25,26,27,28,29]
def requiredD146 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS146 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem146_eq : pairedProblem rows146 cols146 requiredD146 requiredS146 =
    MomentData.problem146 := by rfl
theorem leaf146 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows146++rows146))
    (hc : (q.map Prod.snd).Perm (cols146++cols146))
    (hd : ∀ k ∈ requiredD146, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS146, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows146 cols146 requiredD146 requiredS146
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem146_eq] at model
  exact MomentData.excluded146 ds ss model
def rows147 : List Int := [0,1,2,3,4,5,6,8,13,18,25,26,27,28,29]
def cols147 : List Int := [0,1,2,3,4,5,6,8,13,18,25,26,27,28,29]
def requiredD147 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS147 : List Int := [22,24,26,27,28,29,30,31,32,33,34,35,36,38,40]
theorem problem147_eq : pairedProblem rows147 cols147 requiredD147 requiredS147 =
    MomentData.problem147 := by rfl
theorem leaf147 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows147++rows147))
    (hc : (q.map Prod.snd).Perm (cols147++cols147))
    (hd : ∀ k ∈ requiredD147, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS147, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows147 cols147 requiredD147 requiredS147
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem147_eq] at model
  exact MomentData.excluded147 ds ss model
def rows148 : List Int := [0,1,2,3,4,5,6,7,9,14,19,26,27,28,29]
def cols148 : List Int := [0,1,2,3,4,5,6,7,9,14,19,26,27,28,29]
def requiredD148 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS148 : List Int := [24,26,28,29,30,31,32,33,34,35,36,37,38,40,42]
theorem problem148_eq : pairedProblem rows148 cols148 requiredD148 requiredS148 =
    MomentData.problem148 := by rfl
theorem leaf148 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows148++rows148))
    (hc : (q.map Prod.snd).Perm (cols148++cols148))
    (hd : ∀ k ∈ requiredD148, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS148, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows148 cols148 requiredD148 requiredS148
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem148_eq] at model
  exact MomentData.excluded148 ds ss model
def rows149 : List Int := [0,1,2,3,4,5,10,13,16,24,25,26,27,28,29]
def cols149 : List Int := [0,1,2,3,4,5,10,13,16,24,25,26,27,28,29]
def requiredD149 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS149 : List Int := [21,23,24,25,26,27,28,29,30,31,32,33,34,35,37]
theorem problem149_eq : pairedProblem rows149 cols149 requiredD149 requiredS149 =
    MomentData.problem149 := by rfl
theorem leaf149 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows149++rows149))
    (hc : (q.map Prod.snd).Perm (cols149++cols149))
    (hd : ∀ k ∈ requiredD149, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS149, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows149 cols149 requiredD149 requiredS149
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem149_eq] at model
  exact MomentData.excluded149 ds ss model
def rows150 : List Int := [0,1,2,3,4,5,6,11,14,17,25,26,27,28,29]
def cols150 : List Int := [0,1,2,3,4,5,6,11,14,17,25,26,27,28,29]
def requiredD150 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS150 : List Int := [23,25,26,27,28,29,30,31,32,33,34,35,36,37,39]
theorem problem150_eq : pairedProblem rows150 cols150 requiredD150 requiredS150 =
    MomentData.problem150 := by rfl
theorem leaf150 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows150++rows150))
    (hc : (q.map Prod.snd).Perm (cols150++cols150))
    (hd : ∀ k ∈ requiredD150, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS150, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows150 cols150 requiredD150 requiredS150
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem150_eq] at model
  exact MomentData.excluded150 ds ss model
def rows151 : List Int := [0,1,2,3,4,8,13,14,23,24,25,26,27,28,29]
def cols151 : List Int := [0,1,2,3,4,8,13,14,23,24,25,26,27,28,29]
def requiredD151 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS151 : List Int := [17,21,22,23,24,25,26,27,28,29,30,31,32,33,37]
theorem problem151_eq : pairedProblem rows151 cols151 requiredD151 requiredS151 =
    MomentData.problem151 := by rfl
theorem leaf151 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows151++rows151))
    (hc : (q.map Prod.snd).Perm (cols151++cols151))
    (hd : ∀ k ∈ requiredD151, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS151, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows151 cols151 requiredD151 requiredS151
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem151_eq] at model
  exact MomentData.excluded151 ds ss model
def rows152 : List Int := [0,1,2,3,4,5,9,14,15,24,25,26,27,28,29]
def cols152 : List Int := [0,1,2,3,4,5,9,14,15,24,25,26,27,28,29]
def requiredD152 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS152 : List Int := [19,23,24,25,26,27,28,29,30,31,32,33,34,35,39]
theorem problem152_eq : pairedProblem rows152 cols152 requiredD152 requiredS152 =
    MomentData.problem152 := by rfl
theorem leaf152 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows152++rows152))
    (hc : (q.map Prod.snd).Perm (cols152++cols152))
    (hd : ∀ k ∈ requiredD152, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS152, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows152 cols152 requiredD152 requiredS152
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem152_eq] at model
  exact MomentData.excluded152 ds ss model
def rows153 : List Int := [0,1,2,3,4,5,6,10,15,16,25,26,27,28,29]
def cols153 : List Int := [0,1,2,3,4,5,6,10,15,16,25,26,27,28,29]
def requiredD153 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS153 : List Int := [21,25,26,27,28,29,30,31,32,33,34,35,36,37,41]
theorem problem153_eq : pairedProblem rows153 cols153 requiredD153 requiredS153 =
    MomentData.problem153 := by rfl
theorem leaf153 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows153++rows153))
    (hc : (q.map Prod.snd).Perm (cols153++cols153))
    (hd : ∀ k ∈ requiredD153, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS153, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows153 cols153 requiredD153 requiredS153
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem153_eq] at model
  exact MomentData.excluded153 ds ss model
def rows154 : List Int := [0,1,2,3,4,5,6,7,11,16,17,26,27,28,29]
def cols154 : List Int := [0,1,2,3,4,5,6,7,11,16,17,26,27,28,29]
def requiredD154 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS154 : List Int := [23,27,28,29,30,31,32,33,34,35,36,37,38,39,43]
theorem problem154_eq : pairedProblem rows154 cols154 requiredD154 requiredS154 =
    MomentData.problem154 := by rfl
theorem leaf154 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows154++rows154))
    (hc : (q.map Prod.snd).Perm (cols154++cols154))
    (hd : ∀ k ∈ requiredD154, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS154, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows154 cols154 requiredD154 requiredS154
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem154_eq] at model
  exact MomentData.excluded154 ds ss model
def rows155 : List Int := [0,1,2,3,4,5,6,7,11,16,17,26,27,28,29]
def cols155 : List Int := [0,1,2,3,4,5,6,7,11,16,17,26,27,28,29]
def requiredD155 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS155 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem155_eq : pairedProblem rows155 cols155 requiredD155 requiredS155 =
    MomentData.problem155 := by rfl
theorem leaf155 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows155++rows155))
    (hc : (q.map Prod.snd).Perm (cols155++cols155))
    (hd : ∀ k ∈ requiredD155, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS155, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows155 cols155 requiredD155 requiredS155
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem155_eq] at model
  exact MomentData.excluded155 ds ss model
def rows156 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def cols156 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def requiredD156 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS156 : List Int := [15,20,21,22,23,24,25,26,27,28,29,30,31,32,37]
theorem problem156_eq : pairedProblem rows156 cols156 requiredD156 requiredS156 =
    MomentData.problem156 := by rfl
theorem leaf156 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows156++rows156))
    (hc : (q.map Prod.snd).Perm (cols156++cols156))
    (hd : ∀ k ∈ requiredD156, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS156, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows156 cols156 requiredD156 requiredS156
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem156_eq] at model
  exact MomentData.excluded156 ds ss model
def rows157 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def cols157 : List Int := [0,1,2,3,12,13,14,19,23,24,25,26,27,28,29]
def requiredD157 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS157 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem157_eq : pairedProblem rows157 cols157 requiredD157 requiredS157 =
    MomentData.problem157 := by rfl
theorem leaf157 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows157++rows157))
    (hc : (q.map Prod.snd).Perm (cols157++cols157))
    (hd : ∀ k ∈ requiredD157, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS157, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows157 cols157 requiredD157 requiredS157
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem157_eq] at model
  exact MomentData.excluded157 ds ss model
def rows158 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def cols158 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def requiredD158 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS158 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem158_eq : pairedProblem rows158 cols158 requiredD158 requiredS158 =
    MomentData.problem158 := by rfl
theorem leaf158 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows158++rows158))
    (hc : (q.map Prod.snd).Perm (cols158++cols158))
    (hd : ∀ k ∈ requiredD158, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS158, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows158 cols158 requiredD158 requiredS158
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem158_eq] at model
  exact MomentData.excluded158 ds ss model
def rows159 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def cols159 : List Int := [0,1,2,3,4,13,14,15,20,24,25,26,27,28,29]
def requiredD159 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS159 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem159_eq : pairedProblem rows159 cols159 requiredD159 requiredS159 =
    MomentData.problem159 := by rfl
theorem leaf159 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows159++rows159))
    (hc : (q.map Prod.snd).Perm (cols159++cols159))
    (hd : ∀ k ∈ requiredD159, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS159, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows159 cols159 requiredD159 requiredS159
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem159_eq] at model
  exact MomentData.excluded159 ds ss model
def rows160 : List Int := [0,1,2,3,4,5,14,15,16,21,25,26,27,28,29]
def cols160 : List Int := [0,1,2,3,4,5,14,15,16,21,25,26,27,28,29]
def requiredD160 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS160 : List Int := [19,24,25,26,27,28,29,30,31,32,33,34,35,36,41]
theorem problem160_eq : pairedProblem rows160 cols160 requiredD160 requiredS160 =
    MomentData.problem160 := by rfl
theorem leaf160 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows160++rows160))
    (hc : (q.map Prod.snd).Perm (cols160++cols160))
    (hd : ∀ k ∈ requiredD160, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS160, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows160 cols160 requiredD160 requiredS160
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem160_eq] at model
  exact MomentData.excluded160 ds ss model
def rows161 : List Int := [0,1,2,3,4,5,14,15,16,21,25,26,27,28,29]
def cols161 : List Int := [0,1,2,3,4,5,14,15,16,21,25,26,27,28,29]
def requiredD161 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS161 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem161_eq : pairedProblem rows161 cols161 requiredD161 requiredS161 =
    MomentData.problem161 := by rfl
theorem leaf161 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows161++rows161))
    (hc : (q.map Prod.snd).Perm (cols161++cols161))
    (hd : ∀ k ∈ requiredD161, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS161, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows161 cols161 requiredD161 requiredS161
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem161_eq] at model
  exact MomentData.excluded161 ds ss model
def rows162 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def cols162 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def requiredD162 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS162 : List Int := [17,22,23,24,25,26,27,28,29,30,31,32,33,34,39]
theorem problem162_eq : pairedProblem rows162 cols162 requiredD162 requiredS162 =
    MomentData.problem162 := by rfl
theorem leaf162 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows162++rows162))
    (hc : (q.map Prod.snd).Perm (cols162++cols162))
    (hd : ∀ k ∈ requiredD162, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS162, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows162 cols162 requiredD162 requiredS162
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem162_eq] at model
  exact MomentData.excluded162 ds ss model
def rows163 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def cols163 : List Int := [0,1,2,3,4,8,13,14,15,24,25,26,27,28,29]
def requiredD163 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS163 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem163_eq : pairedProblem rows163 cols163 requiredD163 requiredS163 =
    MomentData.problem163 := by rfl
theorem leaf163 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows163++rows163))
    (hc : (q.map Prod.snd).Perm (cols163++cols163))
    (hd : ∀ k ∈ requiredD163, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS163, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows163 cols163 requiredD163 requiredS163
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem163_eq] at model
  exact MomentData.excluded163 ds ss model
def rows164 : List Int := [0,1,2,3,4,5,9,14,15,16,25,26,27,28,29]
def cols164 : List Int := [0,1,2,3,4,5,9,14,15,16,25,26,27,28,29]
def requiredD164 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS164 : List Int := [19,24,25,26,27,28,29,30,31,32,33,34,35,36,41]
theorem problem164_eq : pairedProblem rows164 cols164 requiredD164 requiredS164 =
    MomentData.problem164 := by rfl
theorem leaf164 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows164++rows164))
    (hc : (q.map Prod.snd).Perm (cols164++cols164))
    (hd : ∀ k ∈ requiredD164, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS164, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows164 cols164 requiredD164 requiredS164
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem164_eq] at model
  exact MomentData.excluded164 ds ss model
def rows165 : List Int := [0,1,2,3,4,5,9,14,15,16,25,26,27,28,29]
def cols165 : List Int := [0,1,2,3,4,5,9,14,15,16,25,26,27,28,29]
def requiredD165 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS165 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem165_eq : pairedProblem rows165 cols165 requiredD165 requiredS165 =
    MomentData.problem165 := by rfl
theorem leaf165 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows165++rows165))
    (hc : (q.map Prod.snd).Perm (cols165++cols165))
    (hd : ∀ k ∈ requiredD165, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS165, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows165 cols165 requiredD165 requiredS165
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem165_eq] at model
  exact MomentData.excluded165 ds ss model
def rows166 : List Int := [0,1,2,3,4,5,6,10,15,16,17,26,27,28,29]
def cols166 : List Int := [0,1,2,3,4,5,6,10,15,16,17,26,27,28,29]
def requiredD166 : List Int := [-11,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,11]
def requiredS166 : List Int := [21,26,27,28,29,30,31,32,33,34,35,36,37,38,43]
theorem problem166_eq : pairedProblem rows166 cols166 requiredD166 requiredS166 =
    MomentData.problem166 := by rfl
theorem leaf166 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows166++rows166))
    (hc : (q.map Prod.snd).Perm (cols166++cols166))
    (hd : ∀ k ∈ requiredD166, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS166, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows166 cols166 requiredD166 requiredS166
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem166_eq] at model
  exact MomentData.excluded166 ds ss model
def rows167 : List Int := [0,1,2,3,4,5,6,10,15,16,17,26,27,28,29]
def cols167 : List Int := [0,1,2,3,4,5,6,10,15,16,17,26,27,28,29]
def requiredD167 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS167 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem167_eq : pairedProblem rows167 cols167 requiredD167 requiredS167 =
    MomentData.problem167 := by rfl
theorem leaf167 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows167++rows167))
    (hc : (q.map Prod.snd).Perm (cols167++cols167))
    (hd : ∀ k ∈ requiredD167, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS167, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows167 cols167 requiredD167 requiredS167
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem167_eq] at model
  exact MomentData.excluded167 ds ss model
def rows168 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols168 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD168 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS168 : List Int := [3,6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem168_eq : pairedProblem rows168 cols168 requiredD168 requiredS168 =
    MomentData.problem168 := by rfl
theorem leaf168 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows168++rows168))
    (hc : (q.map Prod.snd).Perm (cols168++cols168))
    (hd : ∀ k ∈ requiredD168, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS168, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows168 cols168 requiredD168 requiredS168
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem168_eq] at model
  exact MomentData.excluded168 ds ss model
def rows169 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols169 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD169 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS169 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem169_eq : pairedProblem rows169 cols169 requiredD169 requiredS169 =
    MomentData.problem169 := by rfl
theorem leaf169 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows169++rows169))
    (hc : (q.map Prod.snd).Perm (cols169++cols169))
    (hd : ∀ k ∈ requiredD169, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS169, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows169 cols169 requiredD169 requiredS169
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem169_eq] at model
  exact MomentData.excluded169 ds ss model
def rows170 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols170 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD170 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS170 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42]
theorem problem170_eq : pairedProblem rows170 cols170 requiredD170 requiredS170 =
    MomentData.problem170 := by rfl
theorem leaf170 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows170++rows170))
    (hc : (q.map Prod.snd).Perm (cols170++cols170))
    (hd : ∀ k ∈ requiredD170, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS170, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows170 cols170 requiredD170 requiredS170
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem170_eq] at model
  exact MomentData.excluded170 ds ss model
def rows171 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def cols171 : List Int := [0,3,6,9,12,15,18,21,23,24,25,26,27,28,29]
def requiredD171 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS171 : List Int := [3,6,9,12,15,18,21,23,24,27,30,33,36,39]
theorem problem171_eq : pairedProblem rows171 cols171 requiredD171 requiredS171 =
    MomentData.problem171 := by rfl
theorem leaf171 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows171++rows171))
    (hc : (q.map Prod.snd).Perm (cols171++cols171))
    (hd : ∀ k ∈ requiredD171, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS171, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows171 cols171 requiredD171 requiredS171
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem171_eq] at model
  exact MomentData.excluded171 ds ss model
def rows172 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols172 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD172 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS172 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem172_eq : pairedProblem rows172 cols172 requiredD172 requiredS172 =
    MomentData.problem172 := by rfl
theorem leaf172 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows172++rows172))
    (hc : (q.map Prod.snd).Perm (cols172++cols172))
    (hd : ∀ k ∈ requiredD172, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS172, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows172 cols172 requiredD172 requiredS172
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem172_eq] at model
  exact MomentData.excluded172 ds ss model
def rows173 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols173 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD173 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS173 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem173_eq : pairedProblem rows173 cols173 requiredD173 requiredS173 =
    MomentData.problem173 := by rfl
theorem leaf173 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows173++rows173))
    (hc : (q.map Prod.snd).Perm (cols173++cols173))
    (hd : ∀ k ∈ requiredD173, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS173, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows173 cols173 requiredD173 requiredS173
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem173_eq] at model
  exact MomentData.excluded173 ds ss model
def rows174 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols174 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD174 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS174 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem174_eq : pairedProblem rows174 cols174 requiredD174 requiredS174 =
    MomentData.problem174 := by rfl
theorem leaf174 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows174++rows174))
    (hc : (q.map Prod.snd).Perm (cols174++cols174))
    (hd : ∀ k ∈ requiredD174, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS174, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows174 cols174 requiredD174 requiredS174
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem174_eq] at model
  exact MomentData.excluded174 ds ss model
def rows175 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols175 : List Int := [0,1,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD175 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS175 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41]
theorem problem175_eq : pairedProblem rows175 cols175 requiredD175 requiredS175 =
    MomentData.problem175 := by rfl
theorem leaf175 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows175++rows175))
    (hc : (q.map Prod.snd).Perm (cols175++cols175))
    (hd : ∀ k ∈ requiredD175, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS175, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows175 cols175 requiredD175 requiredS175
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem175_eq] at model
  exact MomentData.excluded175 ds ss model
def rows176 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols176 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD176 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS176 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem176_eq : pairedProblem rows176 cols176 requiredD176 requiredS176 =
    MomentData.problem176 := by rfl
theorem leaf176 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows176++rows176))
    (hc : (q.map Prod.snd).Perm (cols176++cols176))
    (hd : ∀ k ∈ requiredD176, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS176, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows176 cols176 requiredD176 requiredS176
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem176_eq] at model
  exact MomentData.excluded176 ds ss model
def rows177 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols177 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD177 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS177 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem177_eq : pairedProblem rows177 cols177 requiredD177 requiredS177 =
    MomentData.problem177 := by rfl
theorem leaf177 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows177++rows177))
    (hc : (q.map Prod.snd).Perm (cols177++cols177))
    (hd : ∀ k ∈ requiredD177, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS177, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows177 cols177 requiredD177 requiredS177
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem177_eq] at model
  exact MomentData.excluded177 ds ss model
def rows178 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols178 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD178 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS178 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem178_eq : pairedProblem rows178 cols178 requiredD178 requiredS178 =
    MomentData.problem178 := by rfl
theorem leaf178 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows178++rows178))
    (hc : (q.map Prod.snd).Perm (cols178++cols178))
    (hd : ∀ k ∈ requiredD178, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS178, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows178 cols178 requiredD178 requiredS178
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem178_eq] at model
  exact MomentData.excluded178 ds ss model
def rows179 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def cols179 : List Int := [0,1,2,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD179 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS179 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43]
theorem problem179_eq : pairedProblem rows179 cols179 requiredD179 requiredS179 =
    MomentData.problem179 := by rfl
theorem leaf179 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows179++rows179))
    (hc : (q.map Prod.snd).Perm (cols179++cols179))
    (hd : ∀ k ∈ requiredD179, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS179, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows179 cols179 requiredD179 requiredS179
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem179_eq] at model
  exact MomentData.excluded179 ds ss model
def rows180 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols180 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD180 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS180 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45,48]
theorem problem180_eq : pairedProblem rows180 cols180 requiredD180 requiredS180 =
    MomentData.problem180 := by rfl
theorem leaf180 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows180++rows180))
    (hc : (q.map Prod.snd).Perm (cols180++cols180))
    (hd : ∀ k ∈ requiredD180, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS180, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows180 cols180 requiredD180 requiredS180
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem180_eq] at model
  exact MomentData.excluded180 ds ss model
def rows181 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols181 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD181 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS181 : List Int := [12,15,18,21,24,27,29,30,33,36,39,42,45,48]
theorem problem181_eq : pairedProblem rows181 cols181 requiredD181 requiredS181 =
    MomentData.problem181 := by rfl
theorem leaf181 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows181++rows181))
    (hc : (q.map Prod.snd).Perm (cols181++cols181))
    (hd : ∀ k ∈ requiredD181, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS181, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows181 cols181 requiredD181 requiredS181
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem181_eq] at model
  exact MomentData.excluded181 ds ss model
def rows182 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols182 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD182 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS182 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem182_eq : pairedProblem rows182 cols182 requiredD182 requiredS182 =
    MomentData.problem182 := by rfl
theorem leaf182 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows182++rows182))
    (hc : (q.map Prod.snd).Perm (cols182++cols182))
    (hd : ∀ k ∈ requiredD182, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS182, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows182 cols182 requiredD182 requiredS182
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem182_eq] at model
  exact MomentData.excluded182 ds ss model
def rows183 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def cols183 : List Int := [0,1,2,3,6,9,12,15,18,21,24,26,27,28,29]
def requiredD183 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS183 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem183_eq : pairedProblem rows183 cols183 requiredD183 requiredS183 =
    MomentData.problem183 := by rfl
theorem leaf183 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows183++rows183))
    (hc : (q.map Prod.snd).Perm (cols183++cols183))
    (hd : ∀ k ∈ requiredD183, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS183, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows183 cols183 requiredD183 requiredS183
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem183_eq] at model
  exact MomentData.excluded183 ds ss model
def rows184 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def cols184 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def requiredD184 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS184 : List Int := [11,14,17,20,23,26,29,31,32,35,38,41,44,47,50]
theorem problem184_eq : pairedProblem rows184 cols184 requiredD184 requiredS184 =
    MomentData.problem184 := by rfl
theorem leaf184 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows184++rows184))
    (hc : (q.map Prod.snd).Perm (cols184++cols184))
    (hd : ∀ k ∈ requiredD184, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS184, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows184 cols184 requiredD184 requiredS184
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem184_eq] at model
  exact MomentData.excluded184 ds ss model
def rows185 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def cols185 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def requiredD185 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS185 : List Int := [14,17,20,23,26,29,31,32,35,38,41,44,47,50]
theorem problem185_eq : pairedProblem rows185 cols185 requiredD185 requiredS185 =
    MomentData.problem185 := by rfl
theorem leaf185 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows185++rows185))
    (hc : (q.map Prod.snd).Perm (cols185++cols185))
    (hd : ∀ k ∈ requiredD185, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS185, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows185 cols185 requiredD185 requiredS185
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem185_eq] at model
  exact MomentData.excluded185 ds ss model
def rows186 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def cols186 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def requiredD186 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS186 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem186_eq : pairedProblem rows186 cols186 requiredD186 requiredS186 =
    MomentData.problem186 := by rfl
theorem leaf186 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows186++rows186))
    (hc : (q.map Prod.snd).Perm (cols186++cols186))
    (hd : ∀ k ∈ requiredD186, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS186, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows186 cols186 requiredD186 requiredS186
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem186_eq] at model
  exact MomentData.excluded186 ds ss model
def rows187 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def cols187 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,27,28,29]
def requiredD187 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS187 : List Int := [11,14,17,20,23,26,29,31,32,35,38,41,44,47]
theorem problem187_eq : pairedProblem rows187 cols187 requiredD187 requiredS187 =
    MomentData.problem187 := by rfl
theorem leaf187 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows187++rows187))
    (hc : (q.map Prod.snd).Perm (cols187++cols187))
    (hd : ∀ k ∈ requiredD187, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS187, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows187 cols187 requiredD187 requiredS187
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem187_eq] at model
  exact MomentData.excluded187 ds ss model
def rows188 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def cols188 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def requiredD188 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS188 : List Int := [13,16,19,22,25,28,31,33,34,37,40,43,46,49,52]
theorem problem188_eq : pairedProblem rows188 cols188 requiredD188 requiredS188 =
    MomentData.problem188 := by rfl
theorem leaf188 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows188++rows188))
    (hc : (q.map Prod.snd).Perm (cols188++cols188))
    (hd : ∀ k ∈ requiredD188, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS188, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows188 cols188 requiredD188 requiredS188
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem188_eq] at model
  exact MomentData.excluded188 ds ss model
def rows189 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def cols189 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def requiredD189 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS189 : List Int := [16,19,22,25,28,31,33,34,37,40,43,46,49,52]
theorem problem189_eq : pairedProblem rows189 cols189 requiredD189 requiredS189 =
    MomentData.problem189 := by rfl
theorem leaf189 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows189++rows189))
    (hc : (q.map Prod.snd).Perm (cols189++cols189))
    (hd : ∀ k ∈ requiredD189, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS189, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows189 cols189 requiredD189 requiredS189
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem189_eq] at model
  exact MomentData.excluded189 ds ss model
def rows190 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def cols190 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def requiredD190 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS190 : List Int := [13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem190_eq : pairedProblem rows190 cols190 requiredD190 requiredS190 =
    MomentData.problem190 := by rfl
theorem leaf190 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows190++rows190))
    (hc : (q.map Prod.snd).Perm (cols190++cols190))
    (hd : ∀ k ∈ requiredD190, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS190, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows190 cols190 requiredD190 requiredS190
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem190_eq] at model
  exact MomentData.excluded190 ds ss model
def rows191 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def cols191 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,28,29]
def requiredD191 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS191 : List Int := [13,16,19,22,25,28,31,33,34,37,40,43,46,49]
theorem problem191_eq : pairedProblem rows191 cols191 requiredD191 requiredS191 =
    MomentData.problem191 := by rfl
theorem leaf191 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows191++rows191))
    (hc : (q.map Prod.snd).Perm (cols191++cols191))
    (hd : ∀ k ∈ requiredD191, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS191, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows191 cols191 requiredD191 requiredS191
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem191_eq] at model
  exact MomentData.excluded191 ds ss model
def rows192 : List Int := [0,1,2,3,4,5,6,9,12,15,18,21,24,27,29]
def cols192 : List Int := [0,1,2,3,4,5,6,9,12,15,18,21,24,27,29]
def requiredD192 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS192 : List Int := [15,18,21,24,27,30,33,35,36,39,42,45,48,51]
theorem problem192_eq : pairedProblem rows192 cols192 requiredD192 requiredS192 =
    MomentData.problem192 := by rfl
theorem leaf192 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows192++rows192))
    (hc : (q.map Prod.snd).Perm (cols192++cols192))
    (hd : ∀ k ∈ requiredD192, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS192, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows192 cols192 requiredD192 requiredS192
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem192_eq] at model
  exact MomentData.excluded192 ds ss model
def rows193 : List Int := [0,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def cols193 : List Int := [0,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def requiredD193 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS193 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43]
theorem problem193_eq : pairedProblem rows193 cols193 requiredD193 requiredS193 =
    MomentData.problem193 := by rfl
theorem leaf193 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows193++rows193))
    (hc : (q.map Prod.snd).Perm (cols193++cols193))
    (hd : ∀ k ∈ requiredD193, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS193, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows193 cols193 requiredD193 requiredS193
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem193_eq] at model
  exact MomentData.excluded193 ds ss model
def rows194 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols194 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD194 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS194 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem194_eq : pairedProblem rows194 cols194 requiredD194 requiredS194 =
    MomentData.problem194 := by rfl
theorem leaf194 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows194++rows194))
    (hc : (q.map Prod.snd).Perm (cols194++cols194))
    (hd : ∀ k ∈ requiredD194, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS194, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows194 cols194 requiredD194 requiredS194
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem194_eq] at model
  exact MomentData.excluded194 ds ss model
def rows195 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols195 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD195 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS195 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem195_eq : pairedProblem rows195 cols195 requiredD195 requiredS195 =
    MomentData.problem195 := by rfl
theorem leaf195 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows195++rows195))
    (hc : (q.map Prod.snd).Perm (cols195++cols195))
    (hd : ∀ k ∈ requiredD195, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS195, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows195 cols195 requiredD195 requiredS195
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem195_eq] at model
  exact MomentData.excluded195 ds ss model
def rows196 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols196 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD196 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS196 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem196_eq : pairedProblem rows196 cols196 requiredD196 requiredS196 =
    MomentData.problem196 := by rfl
theorem leaf196 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows196++rows196))
    (hc : (q.map Prod.snd).Perm (cols196++cols196))
    (hd : ∀ k ∈ requiredD196, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS196, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows196 cols196 requiredD196 requiredS196
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem196_eq] at model
  exact MomentData.excluded196 ds ss model
def rows197 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols197 : List Int := [0,1,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD197 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS197 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem197_eq : pairedProblem rows197 cols197 requiredD197 requiredS197 =
    MomentData.problem197 := by rfl
theorem leaf197 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows197++rows197))
    (hc : (q.map Prod.snd).Perm (cols197++cols197))
    (hd : ∀ k ∈ requiredD197, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS197, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows197 cols197 requiredD197 requiredS197
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem197_eq] at model
  exact MomentData.excluded197 ds ss model
def rows198 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols198 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD198 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS198 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44,47]
theorem problem198_eq : pairedProblem rows198 cols198 requiredD198 requiredS198 =
    MomentData.problem198 := by rfl
theorem leaf198 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows198++rows198))
    (hc : (q.map Prod.snd).Perm (cols198++cols198))
    (hd : ∀ k ∈ requiredD198, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS198, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows198 cols198 requiredD198 requiredS198
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem198_eq] at model
  exact MomentData.excluded198 ds ss model
def rows199 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols199 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD199 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS199 : List Int := [11,14,17,20,23,26,27,29,32,35,38,41,44,47]
theorem problem199_eq : pairedProblem rows199 cols199 requiredD199 requiredS199 =
    MomentData.problem199 := by rfl
theorem leaf199 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows199++rows199))
    (hc : (q.map Prod.snd).Perm (cols199++cols199))
    (hd : ∀ k ∈ requiredD199, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS199, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows199 cols199 requiredD199 requiredS199
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem199_eq] at model
  exact MomentData.excluded199 ds ss model
def rows200 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols200 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD200 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS200 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem200_eq : pairedProblem rows200 cols200 requiredD200 requiredS200 =
    MomentData.problem200 := by rfl
theorem leaf200 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows200++rows200))
    (hc : (q.map Prod.snd).Perm (cols200++cols200))
    (hd : ∀ k ∈ requiredD200, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS200, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows200 cols200 requiredD200 requiredS200
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem200_eq] at model
  exact MomentData.excluded200 ds ss model
def rows201 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def cols201 : List Int := [0,1,2,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD201 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS201 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem201_eq : pairedProblem rows201 cols201 requiredD201 requiredS201 =
    MomentData.problem201 := by rfl
theorem leaf201 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows201++rows201))
    (hc : (q.map Prod.snd).Perm (cols201++cols201))
    (hd : ∀ k ∈ requiredD201, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS201, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows201 cols201 requiredD201 requiredS201
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem201_eq] at model
  exact MomentData.excluded201 ds ss model
def rows202 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def cols202 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def requiredD202 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS202 : List Int := [10,13,16,19,22,25,28,29,31,34,37,40,43,46,49]
theorem problem202_eq : pairedProblem rows202 cols202 requiredD202 requiredS202 =
    MomentData.problem202 := by rfl
theorem leaf202 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows202++rows202))
    (hc : (q.map Prod.snd).Perm (cols202++cols202))
    (hd : ∀ k ∈ requiredD202, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS202, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows202 cols202 requiredD202 requiredS202
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem202_eq] at model
  exact MomentData.excluded202 ds ss model
def rows203 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def cols203 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def requiredD203 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS203 : List Int := [13,16,19,22,25,28,29,31,34,37,40,43,46,49]
theorem problem203_eq : pairedProblem rows203 cols203 requiredD203 requiredS203 =
    MomentData.problem203 := by rfl
theorem leaf203 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows203++rows203))
    (hc : (q.map Prod.snd).Perm (cols203++cols203))
    (hd : ∀ k ∈ requiredD203, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS203, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows203 cols203 requiredD203 requiredS203
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem203_eq] at model
  exact MomentData.excluded203 ds ss model
def rows204 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def cols204 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def requiredD204 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS204 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem204_eq : pairedProblem rows204 cols204 requiredD204 requiredS204 =
    MomentData.problem204 := by rfl
theorem leaf204 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows204++rows204))
    (hc : (q.map Prod.snd).Perm (cols204++cols204))
    (hd : ∀ k ∈ requiredD204, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS204, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows204 cols204 requiredD204 requiredS204
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem204_eq] at model
  exact MomentData.excluded204 ds ss model
def rows205 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def cols205 : List Int := [0,1,2,3,5,8,11,14,17,20,23,26,27,28,29]
def requiredD205 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS205 : List Int := [10,13,16,19,22,25,28,29,31,34,37,40,43,46]
theorem problem205_eq : pairedProblem rows205 cols205 requiredD205 requiredS205 =
    MomentData.problem205 := by rfl
theorem leaf205 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows205++rows205))
    (hc : (q.map Prod.snd).Perm (cols205++cols205))
    (hd : ∀ k ∈ requiredD205, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS205, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows205 cols205 requiredD205 requiredS205
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem205_eq] at model
  exact MomentData.excluded205 ds ss model
def rows206 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def cols206 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def requiredD206 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS206 : List Int := [12,15,18,21,24,27,30,31,33,36,39,42,45,48,51]
theorem problem206_eq : pairedProblem rows206 cols206 requiredD206 requiredS206 =
    MomentData.problem206 := by rfl
theorem leaf206 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows206++rows206))
    (hc : (q.map Prod.snd).Perm (cols206++cols206))
    (hd : ∀ k ∈ requiredD206, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS206, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows206 cols206 requiredD206 requiredS206
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem206_eq] at model
  exact MomentData.excluded206 ds ss model
def rows207 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def cols207 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def requiredD207 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS207 : List Int := [15,18,21,24,27,30,31,33,36,39,42,45,48,51]
theorem problem207_eq : pairedProblem rows207 cols207 requiredD207 requiredS207 =
    MomentData.problem207 := by rfl
theorem leaf207 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows207++rows207))
    (hc : (q.map Prod.snd).Perm (cols207++cols207))
    (hd : ∀ k ∈ requiredD207, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS207, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows207 cols207 requiredD207 requiredS207
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem207_eq] at model
  exact MomentData.excluded207 ds ss model
def rows208 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def cols208 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def requiredD208 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS208 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem208_eq : pairedProblem rows208 cols208 requiredD208 requiredS208 =
    MomentData.problem208 := by rfl
theorem leaf208 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows208++rows208))
    (hc : (q.map Prod.snd).Perm (cols208++cols208))
    (hd : ∀ k ∈ requiredD208, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS208, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows208 cols208 requiredD208 requiredS208
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem208_eq] at model
  exact MomentData.excluded208 ds ss model
def rows209 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def cols209 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,27,28,29]
def requiredD209 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS209 : List Int := [12,15,18,21,24,27,30,31,33,36,39,42,45,48]
theorem problem209_eq : pairedProblem rows209 cols209 requiredD209 requiredS209 =
    MomentData.problem209 := by rfl
theorem leaf209 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows209++rows209))
    (hc : (q.map Prod.snd).Perm (cols209++cols209))
    (hd : ∀ k ∈ requiredD209, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS209, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows209 cols209 requiredD209 requiredS209
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem209_eq] at model
  exact MomentData.excluded209 ds ss model
def rows210 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def cols210 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def requiredD210 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS210 : List Int := [14,17,20,23,26,29,32,33,35,38,41,44,47,50,53]
theorem problem210_eq : pairedProblem rows210 cols210 requiredD210 requiredS210 =
    MomentData.problem210 := by rfl
theorem leaf210 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows210++rows210))
    (hc : (q.map Prod.snd).Perm (cols210++cols210))
    (hd : ∀ k ∈ requiredD210, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS210, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows210 cols210 requiredD210 requiredS210
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem210_eq] at model
  exact MomentData.excluded210 ds ss model
def rows211 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def cols211 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def requiredD211 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS211 : List Int := [17,20,23,26,29,32,33,35,38,41,44,47,50,53]
theorem problem211_eq : pairedProblem rows211 cols211 requiredD211 requiredS211 =
    MomentData.problem211 := by rfl
theorem leaf211 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows211++rows211))
    (hc : (q.map Prod.snd).Perm (cols211++cols211))
    (hd : ∀ k ∈ requiredD211, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS211, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows211 cols211 requiredD211 requiredS211
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem211_eq] at model
  exact MomentData.excluded211 ds ss model
def rows212 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def cols212 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def requiredD212 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS212 : List Int := [14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem212_eq : pairedProblem rows212 cols212 requiredD212 requiredS212 =
    MomentData.problem212 := by rfl
theorem leaf212 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows212++rows212))
    (hc : (q.map Prod.snd).Perm (cols212++cols212))
    (hd : ∀ k ∈ requiredD212, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS212, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows212 cols212 requiredD212 requiredS212
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem212_eq] at model
  exact MomentData.excluded212 ds ss model
def rows213 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def cols213 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,28,29]
def requiredD213 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS213 : List Int := [14,17,20,23,26,29,32,33,35,38,41,44,47,50]
theorem problem213_eq : pairedProblem rows213 cols213 requiredD213 requiredS213 =
    MomentData.problem213 := by rfl
theorem leaf213 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows213++rows213))
    (hc : (q.map Prod.snd).Perm (cols213++cols213))
    (hd : ∀ k ∈ requiredD213, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS213, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows213 cols213 requiredD213 requiredS213
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem213_eq] at model
  exact MomentData.excluded213 ds ss model
def rows214 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def cols214 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def requiredD214 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS214 : List Int := [16,19,22,25,28,31,34,35,37,40,43,46,49,52,55]
theorem problem214_eq : pairedProblem rows214 cols214 requiredD214 requiredS214 =
    MomentData.problem214 := by rfl
theorem leaf214 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows214++rows214))
    (hc : (q.map Prod.snd).Perm (cols214++cols214))
    (hd : ∀ k ∈ requiredD214, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS214, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows214 cols214 requiredD214 requiredS214
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem214_eq] at model
  exact MomentData.excluded214 ds ss model
def rows215 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def cols215 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def requiredD215 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS215 : List Int := [19,22,25,28,31,34,35,37,40,43,46,49,52,55]
theorem problem215_eq : pairedProblem rows215 cols215 requiredD215 requiredS215 =
    MomentData.problem215 := by rfl
theorem leaf215 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows215++rows215))
    (hc : (q.map Prod.snd).Perm (cols215++cols215))
    (hd : ∀ k ∈ requiredD215, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS215, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows215 cols215 requiredD215 requiredS215
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem215_eq] at model
  exact MomentData.excluded215 ds ss model
def rows216 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def cols216 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def requiredD216 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS216 : List Int := [16,19,22,25,28,31,34,37,40,43,46,49,52,55]
theorem problem216_eq : pairedProblem rows216 cols216 requiredD216 requiredS216 =
    MomentData.problem216 := by rfl
theorem leaf216 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows216++rows216))
    (hc : (q.map Prod.snd).Perm (cols216++cols216))
    (hd : ∀ k ∈ requiredD216, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS216, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows216 cols216 requiredD216 requiredS216
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem216_eq] at model
  exact MomentData.excluded216 ds ss model
def rows217 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def cols217 : List Int := [0,1,2,3,4,5,6,8,11,14,17,20,23,26,29]
def requiredD217 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS217 : List Int := [16,19,22,25,28,31,34,35,37,40,43,46,49,52]
theorem problem217_eq : pairedProblem rows217 cols217 requiredD217 requiredS217 =
    MomentData.problem217 := by rfl
theorem leaf217 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows217++rows217))
    (hc : (q.map Prod.snd).Perm (cols217++cols217))
    (hd : ∀ k ∈ requiredD217, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS217, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows217 cols217 requiredD217 requiredS217
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem217_eq] at model
  exact MomentData.excluded217 ds ss model
def rows218 : List Int := [0,1,2,3,4,5,6,15,16,17,18,19,20,21,29]
def cols218 : List Int := [0,1,2,3,4,5,6,15,16,17,18,19,20,21,29]
def requiredD218 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS218 : List Int := [21,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem218_eq : pairedProblem rows218 cols218 requiredD218 requiredS218 =
    MomentData.problem218 := by rfl
theorem leaf218 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows218++rows218))
    (hc : (q.map Prod.snd).Perm (cols218++cols218))
    (hd : ∀ k ∈ requiredD218, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS218, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows218 cols218 requiredD218 requiredS218
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem218_eq] at model
  exact MomentData.excluded218 ds ss model
def rows219 : List Int := [0,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols219 : List Int := [0,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD219 : List Int := [-14,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,14]
def requiredS219 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,37]
theorem problem219_eq : pairedProblem rows219 cols219 requiredD219 requiredS219 =
    MomentData.problem219 := by rfl
theorem leaf219 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows219++rows219))
    (hc : (q.map Prod.snd).Perm (cols219++cols219))
    (hd : ∀ k ∈ requiredD219, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS219, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows219 cols219 requiredD219 requiredS219
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem219_eq] at model
  exact MomentData.excluded219 ds ss model
def rows220 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols220 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD220 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS220 : List Int := [3,6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem220_eq : pairedProblem rows220 cols220 requiredD220 requiredS220 =
    MomentData.problem220 := by rfl
theorem leaf220 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows220++rows220))
    (hc : (q.map Prod.snd).Perm (cols220++cols220))
    (hd : ∀ k ∈ requiredD220, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS220, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows220 cols220 requiredD220 requiredS220
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem220_eq] at model
  exact MomentData.excluded220 ds ss model
def rows221 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols221 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD221 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS221 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem221_eq : pairedProblem rows221 cols221 requiredD221 requiredS221 =
    MomentData.problem221 := by rfl
theorem leaf221 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows221++rows221))
    (hc : (q.map Prod.snd).Perm (cols221++cols221))
    (hd : ∀ k ∈ requiredD221, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS221, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows221 cols221 requiredD221 requiredS221
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem221_eq] at model
  exact MomentData.excluded221 ds ss model
def rows222 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols222 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD222 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS222 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42]
theorem problem222_eq : pairedProblem rows222 cols222 requiredD222 requiredS222 =
    MomentData.problem222 := by rfl
theorem leaf222 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows222++rows222))
    (hc : (q.map Prod.snd).Perm (cols222++cols222))
    (hd : ∀ k ∈ requiredD222, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS222, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows222 cols222 requiredD222 requiredS222
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem222_eq] at model
  exact MomentData.excluded222 ds ss model
def rows223 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols223 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD223 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS223 : List Int := [3,6,9,12,15,18,21,24,25,27,30,33,36,39]
theorem problem223_eq : pairedProblem rows223 cols223 requiredD223 requiredS223 =
    MomentData.problem223 := by rfl
theorem leaf223 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows223++rows223))
    (hc : (q.map Prod.snd).Perm (cols223++cols223))
    (hd : ∀ k ∈ requiredD223, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS223, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows223 cols223 requiredD223 requiredS223
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem223_eq] at model
  exact MomentData.excluded223 ds ss model
def rows224 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols224 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD224 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS224 : List Int := [5,8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem224_eq : pairedProblem rows224 cols224 requiredD224 requiredS224 =
    MomentData.problem224 := by rfl
theorem leaf224 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows224++rows224))
    (hc : (q.map Prod.snd).Perm (cols224++cols224))
    (hd : ∀ k ∈ requiredD224, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS224, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows224 cols224 requiredD224 requiredS224
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem224_eq] at model
  exact MomentData.excluded224 ds ss model
def rows225 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols225 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD225 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS225 : List Int := [8,11,14,17,20,23,26,27,29,32,35,38,41,44]
theorem problem225_eq : pairedProblem rows225 cols225 requiredD225 requiredS225 =
    MomentData.problem225 := by rfl
theorem leaf225 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows225++rows225))
    (hc : (q.map Prod.snd).Perm (cols225++cols225))
    (hd : ∀ k ∈ requiredD225, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS225, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows225 cols225 requiredD225 requiredS225
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem225_eq] at model
  exact MomentData.excluded225 ds ss model
def rows226 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols226 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD226 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS226 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem226_eq : pairedProblem rows226 cols226 requiredD226 requiredS226 =
    MomentData.problem226 := by rfl
theorem leaf226 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows226++rows226))
    (hc : (q.map Prod.snd).Perm (cols226++cols226))
    (hd : ∀ k ∈ requiredD226, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS226, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows226 cols226 requiredD226 requiredS226
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem226_eq] at model
  exact MomentData.excluded226 ds ss model
def rows227 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols227 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD227 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS227 : List Int := [5,8,11,14,17,20,23,26,27,29,32,35,38,41]
theorem problem227_eq : pairedProblem rows227 cols227 requiredD227 requiredS227 =
    MomentData.problem227 := by rfl
theorem leaf227 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows227++rows227))
    (hc : (q.map Prod.snd).Perm (cols227++cols227))
    (hd : ∀ k ∈ requiredD227, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS227, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows227 cols227 requiredD227 requiredS227
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem227_eq] at model
  exact MomentData.excluded227 ds ss model
def rows228 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols228 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD228 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS228 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43,46]
theorem problem228_eq : pairedProblem rows228 cols228 requiredD228 requiredS228 =
    MomentData.problem228 := by rfl
theorem leaf228 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows228++rows228))
    (hc : (q.map Prod.snd).Perm (cols228++cols228))
    (hd : ∀ k ∈ requiredD228, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS228, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows228 cols228 requiredD228 requiredS228
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem228_eq] at model
  exact MomentData.excluded228 ds ss model
def rows229 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols229 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD229 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS229 : List Int := [10,13,16,19,22,25,28,29,31,34,37,40,43,46]
theorem problem229_eq : pairedProblem rows229 cols229 requiredD229 requiredS229 =
    MomentData.problem229 := by rfl
theorem leaf229 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows229++rows229))
    (hc : (q.map Prod.snd).Perm (cols229++cols229))
    (hd : ∀ k ∈ requiredD229, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS229, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows229 cols229 requiredD229 requiredS229
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem229_eq] at model
  exact MomentData.excluded229 ds ss model
def rows230 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols230 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD230 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS230 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem230_eq : pairedProblem rows230 cols230 requiredD230 requiredS230 =
    MomentData.problem230 := by rfl
theorem leaf230 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows230++rows230))
    (hc : (q.map Prod.snd).Perm (cols230++cols230))
    (hd : ∀ k ∈ requiredD230, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS230, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows230 cols230 requiredD230 requiredS230
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem230_eq] at model
  exact MomentData.excluded230 ds ss model
def rows231 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols231 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD231 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS231 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43]
theorem problem231_eq : pairedProblem rows231 cols231 requiredD231 requiredS231 =
    MomentData.problem231 := by rfl
theorem leaf231 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows231++rows231))
    (hc : (q.map Prod.snd).Perm (cols231++cols231))
    (hd : ∀ k ∈ requiredD231, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS231, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows231 cols231 requiredD231 requiredS231
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem231_eq] at model
  exact MomentData.excluded231 ds ss model
def rows232 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols232 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def requiredD232 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS232 : List Int := [9,12,15,18,21,24,27,30,31,33,36,39,42,45,48]
theorem problem232_eq : pairedProblem rows232 cols232 requiredD232 requiredS232 =
    MomentData.problem232 := by rfl
theorem leaf232 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows232++rows232))
    (hc : (q.map Prod.snd).Perm (cols232++cols232))
    (hd : ∀ k ∈ requiredD232, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS232, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows232 cols232 requiredD232 requiredS232
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem232_eq] at model
  exact MomentData.excluded232 ds ss model
def rows233 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols233 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def requiredD233 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS233 : List Int := [12,15,18,21,24,27,30,31,33,36,39,42,45,48]
theorem problem233_eq : pairedProblem rows233 cols233 requiredD233 requiredS233 =
    MomentData.problem233 := by rfl
theorem leaf233 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows233++rows233))
    (hc : (q.map Prod.snd).Perm (cols233++cols233))
    (hd : ∀ k ∈ requiredD233, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS233, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows233 cols233 requiredD233 requiredS233
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem233_eq] at model
  exact MomentData.excluded233 ds ss model
def rows234 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols234 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def requiredD234 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS234 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem234_eq : pairedProblem rows234 cols234 requiredD234 requiredS234 =
    MomentData.problem234 := by rfl
theorem leaf234 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows234++rows234))
    (hc : (q.map Prod.snd).Perm (cols234++cols234))
    (hd : ∀ k ∈ requiredD234, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS234, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows234 cols234 requiredD234 requiredS234
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem234_eq] at model
  exact MomentData.excluded234 ds ss model
def rows235 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols235 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def requiredD235 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS235 : List Int := [9,12,15,18,21,24,27,30,31,33,36,39,42,45]
theorem problem235_eq : pairedProblem rows235 cols235 requiredD235 requiredS235 =
    MomentData.problem235 := by rfl
theorem leaf235 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows235++rows235))
    (hc : (q.map Prod.snd).Perm (cols235++cols235))
    (hd : ∀ k ∈ requiredD235, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS235, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows235 cols235 requiredD235 requiredS235
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem235_eq] at model
  exact MomentData.excluded235 ds ss model
def rows236 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols236 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def requiredD236 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS236 : List Int := [11,14,17,20,23,26,29,32,33,35,38,41,44,47,50]
theorem problem236_eq : pairedProblem rows236 cols236 requiredD236 requiredS236 =
    MomentData.problem236 := by rfl
theorem leaf236 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows236++rows236))
    (hc : (q.map Prod.snd).Perm (cols236++cols236))
    (hd : ∀ k ∈ requiredD236, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS236, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows236 cols236 requiredD236 requiredS236
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem236_eq] at model
  exact MomentData.excluded236 ds ss model
def rows237 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols237 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def requiredD237 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS237 : List Int := [14,17,20,23,26,29,32,33,35,38,41,44,47,50]
theorem problem237_eq : pairedProblem rows237 cols237 requiredD237 requiredS237 =
    MomentData.problem237 := by rfl
theorem leaf237 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows237++rows237))
    (hc : (q.map Prod.snd).Perm (cols237++cols237))
    (hd : ∀ k ∈ requiredD237, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS237, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows237 cols237 requiredD237 requiredS237
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem237_eq] at model
  exact MomentData.excluded237 ds ss model
def rows238 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols238 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def requiredD238 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS238 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem238_eq : pairedProblem rows238 cols238 requiredD238 requiredS238 =
    MomentData.problem238 := by rfl
theorem leaf238 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows238++rows238))
    (hc : (q.map Prod.snd).Perm (cols238++cols238))
    (hd : ∀ k ∈ requiredD238, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS238, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows238 cols238 requiredD238 requiredS238
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem238_eq] at model
  exact MomentData.excluded238 ds ss model
def rows239 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols239 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def requiredD239 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS239 : List Int := [11,14,17,20,23,26,29,32,33,35,38,41,44,47]
theorem problem239_eq : pairedProblem rows239 cols239 requiredD239 requiredS239 =
    MomentData.problem239 := by rfl
theorem leaf239 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows239++rows239))
    (hc : (q.map Prod.snd).Perm (cols239++cols239))
    (hd : ∀ k ∈ requiredD239, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS239, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows239 cols239 requiredD239 requiredS239
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem239_eq] at model
  exact MomentData.excluded239 ds ss model
def rows240 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols240 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def requiredD240 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS240 : List Int := [13,16,19,22,25,28,31,34,35,37,40,43,46,49,52]
theorem problem240_eq : pairedProblem rows240 cols240 requiredD240 requiredS240 =
    MomentData.problem240 := by rfl
theorem leaf240 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows240++rows240))
    (hc : (q.map Prod.snd).Perm (cols240++cols240))
    (hd : ∀ k ∈ requiredD240, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS240, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows240 cols240 requiredD240 requiredS240
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem240_eq] at model
  exact MomentData.excluded240 ds ss model
def rows241 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols241 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def requiredD241 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS241 : List Int := [16,19,22,25,28,31,34,35,37,40,43,46,49,52]
theorem problem241_eq : pairedProblem rows241 cols241 requiredD241 requiredS241 =
    MomentData.problem241 := by rfl
theorem leaf241 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows241++rows241))
    (hc : (q.map Prod.snd).Perm (cols241++cols241))
    (hd : ∀ k ∈ requiredD241, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS241, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows241 cols241 requiredD241 requiredS241
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem241_eq] at model
  exact MomentData.excluded241 ds ss model
def rows242 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols242 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def requiredD242 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS242 : List Int := [13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem242_eq : pairedProblem rows242 cols242 requiredD242 requiredS242 =
    MomentData.problem242 := by rfl
theorem leaf242 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows242++rows242))
    (hc : (q.map Prod.snd).Perm (cols242++cols242))
    (hd : ∀ k ∈ requiredD242, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS242, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows242 cols242 requiredD242 requiredS242
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem242_eq] at model
  exact MomentData.excluded242 ds ss model
def rows243 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols243 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def requiredD243 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS243 : List Int := [13,16,19,22,25,28,31,34,35,37,40,43,46,49]
theorem problem243_eq : pairedProblem rows243 cols243 requiredD243 requiredS243 =
    MomentData.problem243 := by rfl
theorem leaf243 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows243++rows243))
    (hc : (q.map Prod.snd).Perm (cols243++cols243))
    (hd : ∀ k ∈ requiredD243, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS243, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows243 cols243 requiredD243 requiredS243
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem243_eq] at model
  exact MomentData.excluded243 ds ss model
def rows244 : List Int := [0,1,2,3,4,5,6,9,12,15,18,21,24,27,28]
def cols244 : List Int := [0,1,2,3,4,5,6,9,12,15,18,21,24,27,28]
def requiredD244 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS244 : List Int := [15,18,21,24,27,30,33,36,37,39,42,45,48,51]
theorem problem244_eq : pairedProblem rows244 cols244 requiredD244 requiredS244 =
    MomentData.problem244 := by rfl
theorem leaf244 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows244++rows244))
    (hc : (q.map Prod.snd).Perm (cols244++cols244))
    (hd : ∀ k ∈ requiredD244, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS244, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows244 cols244 requiredD244 requiredS244
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem244_eq] at model
  exact MomentData.excluded244 ds ss model
def rows245 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols245 : List Int := [0,3,6,7,9,12,15,18,21,24,25,26,27,28,29]
def requiredD245 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS245 : List Int := [4,7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem245_eq : pairedProblem rows245 cols245 requiredD245 requiredS245 =
    MomentData.problem245 := by rfl
theorem leaf245 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows245++rows245))
    (hc : (q.map Prod.snd).Perm (cols245++cols245))
    (hd : ∀ k ∈ requiredD245, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS245, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows245 cols245 requiredD245 requiredS245
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem245_eq] at model
  exact MomentData.excluded245 ds ss model
def rows246 : List Int := [0,1,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols246 : List Int := [0,3,6,7,9,12,15,18,21,24,25,26,27,28,29]
def requiredD246 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS246 : List Int := [4,7,10,13,16,19,22,25,26,28,31,34,37,40,43]
theorem problem246_eq : pairedProblem rows246 cols246 requiredD246 requiredS246 =
    MomentData.problem246 := by rfl
theorem leaf246 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows246++rows246))
    (hc : (q.map Prod.snd).Perm (cols246++cols246))
    (hd : ∀ k ∈ requiredD246, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS246, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows246 cols246 requiredD246 requiredS246
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem246_eq] at model
  exact MomentData.excluded246 ds ss model
def rows247 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols247 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def requiredD247 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS247 : List Int := [6,9,12,15,18,21,24,27,28,30,33,36,39,42,45]
theorem problem247_eq : pairedProblem rows247 cols247 requiredD247 requiredS247 =
    MomentData.problem247 := by rfl
theorem leaf247 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows247++rows247))
    (hc : (q.map Prod.snd).Perm (cols247++cols247))
    (hd : ∀ k ∈ requiredD247, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS247, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows247 cols247 requiredD247 requiredS247
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem247_eq] at model
  exact MomentData.excluded247 ds ss model
def rows248 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols248 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def requiredD248 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS248 : List Int := [9,12,15,18,21,24,26,27,28,30,33,36,39,42,45]
theorem problem248_eq : pairedProblem rows248 cols248 requiredD248 requiredS248 =
    MomentData.problem248 := by rfl
theorem leaf248 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows248++rows248))
    (hc : (q.map Prod.snd).Perm (cols248++cols248))
    (hd : ∀ k ∈ requiredD248, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS248, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows248 cols248 requiredD248 requiredS248
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem248_eq] at model
  exact MomentData.excluded248 ds ss model
def rows249 : List Int := [0,1,2,5,8,11,14,17,20,23,24,26,27,28,29]
def cols249 : List Int := [0,1,4,7,8,10,13,16,19,22,25,26,27,28,29]
def requiredD249 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS249 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem249_eq : pairedProblem rows249 cols249 requiredD249 requiredS249 =
    MomentData.problem249 := by rfl
theorem leaf249 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows249++rows249))
    (hc : (q.map Prod.snd).Perm (cols249++cols249))
    (hd : ∀ k ∈ requiredD249, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS249, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows249 cols249 requiredD249 requiredS249
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem249_eq] at model
  exact MomentData.excluded249 ds ss model
def rows250 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols250 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def requiredD250 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS250 : List Int := [8,11,14,17,20,23,26,29,30,32,35,38,41,44,47]
theorem problem250_eq : pairedProblem rows250 cols250 requiredD250 requiredS250 =
    MomentData.problem250 := by rfl
theorem leaf250 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows250++rows250))
    (hc : (q.map Prod.snd).Perm (cols250++cols250))
    (hd : ∀ k ∈ requiredD250, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS250, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows250 cols250 requiredD250 requiredS250
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem250_eq] at model
  exact MomentData.excluded250 ds ss model
def rows251 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols251 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def requiredD251 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS251 : List Int := [11,14,17,20,23,26,28,29,30,32,35,38,41,44,47]
theorem problem251_eq : pairedProblem rows251 cols251 requiredD251 requiredS251 =
    MomentData.problem251 := by rfl
theorem leaf251 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows251++rows251))
    (hc : (q.map Prod.snd).Perm (cols251++cols251))
    (hd : ∀ k ∈ requiredD251, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS251, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows251 cols251 requiredD251 requiredS251
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem251_eq] at model
  exact MomentData.excluded251 ds ss model
def rows252 : List Int := [0,1,2,3,6,9,12,15,18,21,24,25,27,28,29]
def cols252 : List Int := [0,1,2,5,8,9,11,14,17,20,23,26,27,28,29]
def requiredD252 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS252 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem252_eq : pairedProblem rows252 cols252 requiredD252 requiredS252 =
    MomentData.problem252 := by rfl
theorem leaf252 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows252++rows252))
    (hc : (q.map Prod.snd).Perm (cols252++cols252))
    (hd : ∀ k ∈ requiredD252, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS252, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows252 cols252 requiredD252 requiredS252
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem252_eq] at model
  exact MomentData.excluded252 ds ss model
def rows253 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols253 : List Int := [0,1,2,3,6,9,10,12,15,18,21,24,27,28,29]
def requiredD253 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS253 : List Int := [10,13,16,19,22,25,28,31,32,34,37,40,43,46,49]
theorem problem253_eq : pairedProblem rows253 cols253 requiredD253 requiredS253 =
    MomentData.problem253 := by rfl
theorem leaf253 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows253++rows253))
    (hc : (q.map Prod.snd).Perm (cols253++cols253))
    (hd : ∀ k ∈ requiredD253, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS253, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows253 cols253 requiredD253 requiredS253
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem253_eq] at model
  exact MomentData.excluded253 ds ss model
def rows254 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols254 : List Int := [0,1,2,3,6,9,10,12,15,18,21,24,27,28,29]
def requiredD254 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS254 : List Int := [13,16,19,22,25,28,30,31,32,34,37,40,43,46,49]
theorem problem254_eq : pairedProblem rows254 cols254 requiredD254 requiredS254 =
    MomentData.problem254 := by rfl
theorem leaf254 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows254++rows254))
    (hc : (q.map Prod.snd).Perm (cols254++cols254))
    (hd : ∀ k ∈ requiredD254, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS254, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows254 cols254 requiredD254 requiredS254
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem254_eq] at model
  exact MomentData.excluded254 ds ss model
def rows255 : List Int := [0,1,2,3,4,7,10,13,16,19,22,25,26,28,29]
def cols255 : List Int := [0,1,2,3,6,9,10,12,15,18,21,24,27,28,29]
def requiredD255 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS255 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem255_eq : pairedProblem rows255 cols255 requiredD255 requiredS255 =
    MomentData.problem255 := by rfl
theorem leaf255 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows255++rows255))
    (hc : (q.map Prod.snd).Perm (cols255++cols255))
    (hd : ∀ k ∈ requiredD255, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS255, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows255 cols255 requiredD255 requiredS255
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem255_eq] at model
  exact MomentData.excluded255 ds ss model
#print axioms leaf128
end Gardner.Kernel.MomentContexts
