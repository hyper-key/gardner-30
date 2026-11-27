import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows256 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols256 : List Int := [0,1,2,3,4,7,10,11,13,16,19,22,25,28,29]
def requiredD256 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS256 : List Int := [12,15,18,21,24,27,30,33,34,36,39,42,45,48,51]
theorem problem256_eq : pairedProblem rows256 cols256 requiredD256 requiredS256 =
    MomentData.problem256 := by rfl
theorem leaf256 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows256++rows256))
    (hc : (q.map Prod.snd).Perm (cols256++cols256))
    (hd : ∀ k ∈ requiredD256, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS256, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows256 cols256 requiredD256 requiredS256
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem256_eq] at model
  exact MomentData.excluded256 ds ss model
def rows257 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols257 : List Int := [0,1,2,3,4,7,10,11,13,16,19,22,25,28,29]
def requiredD257 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS257 : List Int := [15,18,21,24,27,30,32,33,34,36,39,42,45,48,51]
theorem problem257_eq : pairedProblem rows257 cols257 requiredD257 requiredS257 =
    MomentData.problem257 := by rfl
theorem leaf257 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows257++rows257))
    (hc : (q.map Prod.snd).Perm (cols257++cols257))
    (hd : ∀ k ∈ requiredD257, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS257, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows257 cols257 requiredD257 requiredS257
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem257_eq] at model
  exact MomentData.excluded257 ds ss model
def rows258 : List Int := [0,1,2,3,4,5,8,11,14,17,20,23,26,27,29]
def cols258 : List Int := [0,1,2,3,4,7,10,11,13,16,19,22,25,28,29]
def requiredD258 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS258 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51,54]
theorem problem258_eq : pairedProblem rows258 cols258 requiredD258 requiredS258 =
    MomentData.problem258 := by rfl
theorem leaf258 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows258++rows258))
    (hc : (q.map Prod.snd).Perm (cols258++cols258))
    (hd : ∀ k ∈ requiredD258, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS258, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows258 cols258 requiredD258 requiredS258
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem258_eq] at model
  exact MomentData.excluded258 ds ss model
def rows259 : List Int := [0,1,2,3,4,5,6,9,12,15,18,21,24,27,28]
def cols259 : List Int := [0,1,2,3,4,5,8,11,12,14,17,20,23,26,29]
def requiredD259 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS259 : List Int := [14,17,20,23,26,29,32,35,36,38,41,44,47,50,53]
theorem problem259_eq : pairedProblem rows259 cols259 requiredD259 requiredS259 =
    MomentData.problem259 := by rfl
theorem leaf259 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows259++rows259))
    (hc : (q.map Prod.snd).Perm (cols259++cols259))
    (hd : ∀ k ∈ requiredD259, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS259, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows259 cols259 requiredD259 requiredS259
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem259_eq] at model
  exact MomentData.excluded259 ds ss model
def rows260 : List Int := [0,3,6,9,12,15,17,18,21,24,25,26,27,28,29]
def cols260 : List Int := [1,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def requiredD260 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS260 : List Int := [5,8,11,14,17,20,22,23,26,29,32,35,38,41,44]
theorem problem260_eq : pairedProblem rows260 cols260 requiredD260 requiredS260 =
    MomentData.problem260 := by rfl
theorem leaf260 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows260++rows260))
    (hc : (q.map Prod.snd).Perm (cols260++cols260))
    (hd : ∀ k ∈ requiredD260, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS260, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows260 cols260 requiredD260 requiredS260
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem260_eq] at model
  exact MomentData.excluded260 ds ss model
def rows261 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def cols261 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD261 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS261 : List Int := [7,10,13,16,19,22,24,25,28,31,34,37,40,43,46]
theorem problem261_eq : pairedProblem rows261 cols261 requiredD261 requiredS261 =
    MomentData.problem261 := by rfl
theorem leaf261 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows261++rows261))
    (hc : (q.map Prod.snd).Perm (cols261++cols261))
    (hd : ∀ k ∈ requiredD261, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS261, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows261 cols261 requiredD261 requiredS261
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem261_eq] at model
  exact MomentData.excluded261 ds ss model
def rows262 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def cols262 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD262 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS262 : List Int := [4,7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem262_eq : pairedProblem rows262 cols262 requiredD262 requiredS262 =
    MomentData.problem262 := by rfl
theorem leaf262 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows262++rows262))
    (hc : (q.map Prod.snd).Perm (cols262++cols262))
    (hd : ∀ k ∈ requiredD262, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS262, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows262 cols262 requiredD262 requiredS262
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem262_eq] at model
  exact MomentData.excluded262 ds ss model
def rows263 : List Int := [0,1,4,7,10,13,16,18,19,22,25,26,27,28,29]
def cols263 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD263 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS263 : List Int := [7,10,13,16,19,22,24,25,26,28,31,34,37,40,43]
theorem problem263_eq : pairedProblem rows263 cols263 requiredD263 requiredS263 =
    MomentData.problem263 := by rfl
theorem leaf263 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows263++rows263))
    (hc : (q.map Prod.snd).Perm (cols263++cols263))
    (hd : ∀ k ∈ requiredD263, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS263, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows263 cols263 requiredD263 requiredS263
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem263_eq] at model
  exact MomentData.excluded263 ds ss model
def rows264 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def cols264 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD264 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS264 : List Int := [9,12,15,18,21,24,26,27,30,33,36,39,42,45,48]
theorem problem264_eq : pairedProblem rows264 cols264 requiredD264 requiredS264 =
    MomentData.problem264 := by rfl
theorem leaf264 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows264++rows264))
    (hc : (q.map Prod.snd).Perm (cols264++cols264))
    (hd : ∀ k ∈ requiredD264, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS264, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows264 cols264 requiredD264 requiredS264
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem264_eq] at model
  exact MomentData.excluded264 ds ss model
def rows265 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def cols265 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD265 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS265 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem265_eq : pairedProblem rows265 cols265 requiredD265 requiredS265 =
    MomentData.problem265 := by rfl
theorem leaf265 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows265++rows265))
    (hc : (q.map Prod.snd).Perm (cols265++cols265))
    (hd : ∀ k ∈ requiredD265, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS265, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows265 cols265 requiredD265 requiredS265
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem265_eq] at model
  exact MomentData.excluded265 ds ss model
def rows266 : List Int := [0,1,2,5,8,11,14,17,19,20,23,26,27,28,29]
def cols266 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD266 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS266 : List Int := [9,12,15,18,21,24,26,27,28,30,33,36,39,42,45]
theorem problem266_eq : pairedProblem rows266 cols266 requiredD266 requiredS266 =
    MomentData.problem266 := by rfl
theorem leaf266 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows266++rows266))
    (hc : (q.map Prod.snd).Perm (cols266++cols266))
    (hd : ∀ k ∈ requiredD266, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS266, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows266 cols266 requiredD266 requiredS266
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem266_eq] at model
  exact MomentData.excluded266 ds ss model
def rows267 : List Int := [0,1,2,3,6,9,12,15,18,20,21,24,27,28,29]
def cols267 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD267 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS267 : List Int := [11,14,17,20,23,26,28,29,32,35,38,41,44,47,50]
theorem problem267_eq : pairedProblem rows267 cols267 requiredD267 requiredS267 =
    MomentData.problem267 := by rfl
theorem leaf267 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows267++rows267))
    (hc : (q.map Prod.snd).Perm (cols267++cols267))
    (hd : ∀ k ∈ requiredD267, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS267, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows267 cols267 requiredD267 requiredS267
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem267_eq] at model
  exact MomentData.excluded267 ds ss model
def rows268 : List Int := [0,1,2,3,6,9,12,15,18,20,21,24,27,28,29]
def cols268 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD268 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS268 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem268_eq : pairedProblem rows268 cols268 requiredD268 requiredS268 =
    MomentData.problem268 := by rfl
theorem leaf268 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows268++rows268))
    (hc : (q.map Prod.snd).Perm (cols268++cols268))
    (hd : ∀ k ∈ requiredD268, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS268, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows268 cols268 requiredD268 requiredS268
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem268_eq] at model
  exact MomentData.excluded268 ds ss model
def rows269 : List Int := [0,1,2,3,6,9,12,15,18,20,21,24,27,28,29]
def cols269 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD269 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS269 : List Int := [11,14,17,20,23,26,28,29,30,32,35,38,41,44,47]
theorem problem269_eq : pairedProblem rows269 cols269 requiredD269 requiredS269 =
    MomentData.problem269 := by rfl
theorem leaf269 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows269++rows269))
    (hc : (q.map Prod.snd).Perm (cols269++cols269))
    (hd : ∀ k ∈ requiredD269, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS269, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows269 cols269 requiredD269 requiredS269
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem269_eq] at model
  exact MomentData.excluded269 ds ss model
def rows270 : List Int := [0,1,2,3,4,7,10,13,16,19,21,22,25,28,29]
def cols270 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD270 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS270 : List Int := [13,16,19,22,25,28,30,31,34,37,40,43,46,49,52]
theorem problem270_eq : pairedProblem rows270 cols270 requiredD270 requiredS270 =
    MomentData.problem270 := by rfl
theorem leaf270 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows270++rows270))
    (hc : (q.map Prod.snd).Perm (cols270++cols270))
    (hd : ∀ k ∈ requiredD270, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS270, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows270 cols270 requiredD270 requiredS270
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem270_eq] at model
  exact MomentData.excluded270 ds ss model
def rows271 : List Int := [0,1,2,3,4,7,10,13,16,19,21,22,25,28,29]
def cols271 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD271 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS271 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem271_eq : pairedProblem rows271 cols271 requiredD271 requiredS271 =
    MomentData.problem271 := by rfl
theorem leaf271 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows271++rows271))
    (hc : (q.map Prod.snd).Perm (cols271++cols271))
    (hd : ∀ k ∈ requiredD271, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS271, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows271 cols271 requiredD271 requiredS271
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem271_eq] at model
  exact MomentData.excluded271 ds ss model
def rows272 : List Int := [0,1,2,3,4,7,10,13,16,19,21,22,25,28,29]
def cols272 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD272 : List Int := [-17,-14,-11,-8,-5,-2,0,1,2,4,7,10,13,16,19]
def requiredS272 : List Int := [13,16,19,22,25,28,30,31,32,34,37,40,43,46,49]
theorem problem272_eq : pairedProblem rows272 cols272 requiredD272 requiredS272 =
    MomentData.problem272 := by rfl
theorem leaf272 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows272++rows272))
    (hc : (q.map Prod.snd).Perm (cols272++cols272))
    (hd : ∀ k ∈ requiredD272, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS272, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows272 cols272 requiredD272 requiredS272
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem272_eq] at model
  exact MomentData.excluded272 ds ss model
def rows273 : List Int := [0,1,2,3,4,5,8,11,14,17,20,22,23,26,29]
def cols273 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD273 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS273 : List Int := [15,18,21,24,27,30,32,33,36,39,42,45,48,51,54]
theorem problem273_eq : pairedProblem rows273 cols273 requiredD273 requiredS273 =
    MomentData.problem273 := by rfl
theorem leaf273 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows273++rows273))
    (hc : (q.map Prod.snd).Perm (cols273++cols273))
    (hd : ∀ k ∈ requiredD273, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS273, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows273 cols273 requiredD273 requiredS273
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem273_eq] at model
  exact MomentData.excluded273 ds ss model
def rows274 : List Int := [0,1,2,3,4,5,8,11,14,17,20,22,23,26,29]
def cols274 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD274 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS274 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51,54]
theorem problem274_eq : pairedProblem rows274 cols274 requiredD274 requiredS274 =
    MomentData.problem274 := by rfl
theorem leaf274 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows274++rows274))
    (hc : (q.map Prod.snd).Perm (cols274++cols274))
    (hd : ∀ k ∈ requiredD274, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS274, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows274 cols274 requiredD274 requiredS274
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem274_eq] at model
  exact MomentData.excluded274 ds ss model
def rows275 : List Int := [1,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def cols275 : List Int := [1,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def requiredD275 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS275 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43]
theorem problem275_eq : pairedProblem rows275 cols275 requiredD275 requiredS275 =
    MomentData.problem275 := by rfl
theorem leaf275 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows275++rows275))
    (hc : (q.map Prod.snd).Perm (cols275++cols275))
    (hd : ∀ k ∈ requiredD275, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS275, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows275 cols275 requiredD275 requiredS275
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem275_eq] at model
  exact MomentData.excluded275 ds ss model
def rows276 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols276 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD276 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS276 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem276_eq : pairedProblem rows276 cols276 requiredD276 requiredS276 =
    MomentData.problem276 := by rfl
theorem leaf276 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows276++rows276))
    (hc : (q.map Prod.snd).Perm (cols276++cols276))
    (hd : ∀ k ∈ requiredD276, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS276, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows276 cols276 requiredD276 requiredS276
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem276_eq] at model
  exact MomentData.excluded276 ds ss model
def rows277 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols277 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD277 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS277 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem277_eq : pairedProblem rows277 cols277 requiredD277 requiredS277 =
    MomentData.problem277 := by rfl
theorem leaf277 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows277++rows277))
    (hc : (q.map Prod.snd).Perm (cols277++cols277))
    (hd : ∀ k ∈ requiredD277, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS277, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows277 cols277 requiredD277 requiredS277
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem277_eq] at model
  exact MomentData.excluded277 ds ss model
def rows278 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols278 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD278 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS278 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem278_eq : pairedProblem rows278 cols278 requiredD278 requiredS278 =
    MomentData.problem278 := by rfl
theorem leaf278 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows278++rows278))
    (hc : (q.map Prod.snd).Perm (cols278++cols278))
    (hd : ∀ k ∈ requiredD278, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS278, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows278 cols278 requiredD278 requiredS278
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem278_eq] at model
  exact MomentData.excluded278 ds ss model
def rows279 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def cols279 : List Int := [0,2,3,6,9,12,15,18,21,24,25,26,27,28,29]
def requiredD279 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS279 : List Int := [6,9,12,15,18,21,23,24,27,30,33,36,39,42]
theorem problem279_eq : pairedProblem rows279 cols279 requiredD279 requiredS279 =
    MomentData.problem279 := by rfl
theorem leaf279 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows279++rows279))
    (hc : (q.map Prod.snd).Perm (cols279++cols279))
    (hd : ∀ k ∈ requiredD279, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS279, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows279 cols279 requiredD279 requiredS279
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem279_eq] at model
  exact MomentData.excluded279 ds ss model
def rows280 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols280 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD280 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS280 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44,47]
theorem problem280_eq : pairedProblem rows280 cols280 requiredD280 requiredS280 =
    MomentData.problem280 := by rfl
theorem leaf280 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows280++rows280))
    (hc : (q.map Prod.snd).Perm (cols280++cols280))
    (hd : ∀ k ∈ requiredD280, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS280, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows280 cols280 requiredD280 requiredS280
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem280_eq] at model
  exact MomentData.excluded280 ds ss model
def rows281 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols281 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD281 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS281 : List Int := [11,14,17,20,23,25,26,29,32,35,38,41,44,47]
theorem problem281_eq : pairedProblem rows281 cols281 requiredD281 requiredS281 =
    MomentData.problem281 := by rfl
theorem leaf281 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows281++rows281))
    (hc : (q.map Prod.snd).Perm (cols281++cols281))
    (hd : ∀ k ∈ requiredD281, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS281, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows281 cols281 requiredD281 requiredS281
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem281_eq] at model
  exact MomentData.excluded281 ds ss model
def rows282 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols282 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD282 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS282 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem282_eq : pairedProblem rows282 cols282 requiredD282 requiredS282 =
    MomentData.problem282 := by rfl
theorem leaf282 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows282++rows282))
    (hc : (q.map Prod.snd).Perm (cols282++cols282))
    (hd : ∀ k ∈ requiredD282, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS282, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows282 cols282 requiredD282 requiredS282
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem282_eq] at model
  exact MomentData.excluded282 ds ss model
def rows283 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def cols283 : List Int := [0,1,3,4,7,10,13,16,19,22,25,26,27,28,29]
def requiredD283 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS283 : List Int := [8,11,14,17,20,23,25,26,29,32,35,38,41,44]
theorem problem283_eq : pairedProblem rows283 cols283 requiredD283 requiredS283 =
    MomentData.problem283 := by rfl
theorem leaf283 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows283++rows283))
    (hc : (q.map Prod.snd).Perm (cols283++cols283))
    (hd : ∀ k ∈ requiredD283, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS283, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows283 cols283 requiredD283 requiredS283
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem283_eq] at model
  exact MomentData.excluded283 ds ss model
def rows284 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols284 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD284 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS284 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem284_eq : pairedProblem rows284 cols284 requiredD284 requiredS284 =
    MomentData.problem284 := by rfl
theorem leaf284 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows284++rows284))
    (hc : (q.map Prod.snd).Perm (cols284++cols284))
    (hd : ∀ k ∈ requiredD284, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS284, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows284 cols284 requiredD284 requiredS284
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem284_eq] at model
  exact MomentData.excluded284 ds ss model
def rows285 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols285 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD285 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS285 : List Int := [13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem285_eq : pairedProblem rows285 cols285 requiredD285 requiredS285 =
    MomentData.problem285 := by rfl
theorem leaf285 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows285++rows285))
    (hc : (q.map Prod.snd).Perm (cols285++cols285))
    (hd : ∀ k ∈ requiredD285, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS285, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows285 cols285 requiredD285 requiredS285
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem285_eq] at model
  exact MomentData.excluded285 ds ss model
def rows286 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols286 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD286 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS286 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem286_eq : pairedProblem rows286 cols286 requiredD286 requiredS286 =
    MomentData.problem286 := by rfl
theorem leaf286 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows286++rows286))
    (hc : (q.map Prod.snd).Perm (cols286++cols286))
    (hd : ∀ k ∈ requiredD286, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS286, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows286 cols286 requiredD286 requiredS286
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem286_eq] at model
  exact MomentData.excluded286 ds ss model
def rows287 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def cols287 : List Int := [0,1,2,4,5,8,11,14,17,20,23,26,27,28,29]
def requiredD287 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS287 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46]
theorem problem287_eq : pairedProblem rows287 cols287 requiredD287 requiredS287 =
    MomentData.problem287 := by rfl
theorem leaf287 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows287++rows287))
    (hc : (q.map Prod.snd).Perm (cols287++cols287))
    (hd : ∀ k ∈ requiredD287, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS287, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows287 cols287 requiredD287 requiredS287
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem287_eq] at model
  exact MomentData.excluded287 ds ss model
def rows288 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def cols288 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD288 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS288 : List Int := [12,15,18,21,24,27,29,30,33,36,39,42,45,48,51]
theorem problem288_eq : pairedProblem rows288 cols288 requiredD288 requiredS288 =
    MomentData.problem288 := by rfl
theorem leaf288 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows288++rows288))
    (hc : (q.map Prod.snd).Perm (cols288++cols288))
    (hd : ∀ k ∈ requiredD288, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS288, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows288 cols288 requiredD288 requiredS288
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem288_eq] at model
  exact MomentData.excluded288 ds ss model
def rows289 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def cols289 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD289 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS289 : List Int := [15,18,21,24,27,29,30,33,36,39,42,45,48,51]
theorem problem289_eq : pairedProblem rows289 cols289 requiredD289 requiredS289 =
    MomentData.problem289 := by rfl
theorem leaf289 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows289++rows289))
    (hc : (q.map Prod.snd).Perm (cols289++cols289))
    (hd : ∀ k ∈ requiredD289, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS289, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows289 cols289 requiredD289 requiredS289
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem289_eq] at model
  exact MomentData.excluded289 ds ss model
def rows290 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def cols290 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD290 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS290 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem290_eq : pairedProblem rows290 cols290 requiredD290 requiredS290 =
    MomentData.problem290 := by rfl
theorem leaf290 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows290++rows290))
    (hc : (q.map Prod.snd).Perm (cols290++cols290))
    (hd : ∀ k ∈ requiredD290, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS290, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows290 cols290 requiredD290 requiredS290
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem290_eq] at model
  exact MomentData.excluded290 ds ss model
def rows291 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def cols291 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,27,28,29]
def requiredD291 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS291 : List Int := [12,15,18,21,24,27,29,30,33,36,39,42,45,48]
theorem problem291_eq : pairedProblem rows291 cols291 requiredD291 requiredS291 =
    MomentData.problem291 := by rfl
theorem leaf291 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows291++rows291))
    (hc : (q.map Prod.snd).Perm (cols291++cols291))
    (hd : ∀ k ∈ requiredD291, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS291, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows291 cols291 requiredD291 requiredS291
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem291_eq] at model
  exact MomentData.excluded291 ds ss model
def rows292 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def cols292 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD292 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS292 : List Int := [14,17,20,23,26,29,31,32,35,38,41,44,47,50,53]
theorem problem292_eq : pairedProblem rows292 cols292 requiredD292 requiredS292 =
    MomentData.problem292 := by rfl
theorem leaf292 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows292++rows292))
    (hc : (q.map Prod.snd).Perm (cols292++cols292))
    (hd : ∀ k ∈ requiredD292, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS292, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows292 cols292 requiredD292 requiredS292
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem292_eq] at model
  exact MomentData.excluded292 ds ss model
def rows293 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def cols293 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD293 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS293 : List Int := [17,20,23,26,29,31,32,35,38,41,44,47,50,53]
theorem problem293_eq : pairedProblem rows293 cols293 requiredD293 requiredS293 =
    MomentData.problem293 := by rfl
theorem leaf293 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows293++rows293))
    (hc : (q.map Prod.snd).Perm (cols293++cols293))
    (hd : ∀ k ∈ requiredD293, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS293, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows293 cols293 requiredD293 requiredS293
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem293_eq] at model
  exact MomentData.excluded293 ds ss model
def rows294 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def cols294 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD294 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS294 : List Int := [14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem294_eq : pairedProblem rows294 cols294 requiredD294 requiredS294 =
    MomentData.problem294 := by rfl
theorem leaf294 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows294++rows294))
    (hc : (q.map Prod.snd).Perm (cols294++cols294))
    (hd : ∀ k ∈ requiredD294, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS294, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows294 cols294 requiredD294 requiredS294
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem294_eq] at model
  exact MomentData.excluded294 ds ss model
def rows295 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def cols295 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,28,29]
def requiredD295 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS295 : List Int := [14,17,20,23,26,29,31,32,35,38,41,44,47,50]
theorem problem295_eq : pairedProblem rows295 cols295 requiredD295 requiredS295 =
    MomentData.problem295 := by rfl
theorem leaf295 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows295++rows295))
    (hc : (q.map Prod.snd).Perm (cols295++cols295))
    (hd : ∀ k ∈ requiredD295, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS295, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows295 cols295 requiredD295 requiredS295
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem295_eq] at model
  exact MomentData.excluded295 ds ss model
def rows296 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def cols296 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def requiredD296 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS296 : List Int := [16,19,22,25,28,31,33,34,37,40,43,46,49,52,55]
theorem problem296_eq : pairedProblem rows296 cols296 requiredD296 requiredS296 =
    MomentData.problem296 := by rfl
theorem leaf296 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows296++rows296))
    (hc : (q.map Prod.snd).Perm (cols296++cols296))
    (hd : ∀ k ∈ requiredD296, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS296, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows296 cols296 requiredD296 requiredS296
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem296_eq] at model
  exact MomentData.excluded296 ds ss model
def rows297 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def cols297 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def requiredD297 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS297 : List Int := [19,22,25,28,31,33,34,37,40,43,46,49,52,55]
theorem problem297_eq : pairedProblem rows297 cols297 requiredD297 requiredS297 =
    MomentData.problem297 := by rfl
theorem leaf297 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows297++rows297))
    (hc : (q.map Prod.snd).Perm (cols297++cols297))
    (hd : ∀ k ∈ requiredD297, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS297, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows297 cols297 requiredD297 requiredS297
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem297_eq] at model
  exact MomentData.excluded297 ds ss model
def rows298 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def cols298 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def requiredD298 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS298 : List Int := [16,19,22,25,28,31,34,37,40,43,46,49,52,55]
theorem problem298_eq : pairedProblem rows298 cols298 requiredD298 requiredS298 =
    MomentData.problem298 := by rfl
theorem leaf298 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows298++rows298))
    (hc : (q.map Prod.snd).Perm (cols298++cols298))
    (hd : ∀ k ∈ requiredD298, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS298, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows298 cols298 requiredD298 requiredS298
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem298_eq] at model
  exact MomentData.excluded298 ds ss model
def rows299 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def cols299 : List Int := [0,1,2,3,4,5,7,8,11,14,17,20,23,26,29]
def requiredD299 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS299 : List Int := [16,19,22,25,28,31,33,34,37,40,43,46,49,52]
theorem problem299_eq : pairedProblem rows299 cols299 requiredD299 requiredS299 =
    MomentData.problem299 := by rfl
theorem leaf299 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows299++rows299))
    (hc : (q.map Prod.snd).Perm (cols299++cols299))
    (hd : ∀ k ∈ requiredD299, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS299, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows299 cols299 requiredD299 requiredS299
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem299_eq] at model
  exact MomentData.excluded299 ds ss model
def rows300 : List Int := [0,1,2,3,4,5,15,16,17,18,19,20,21,22,29]
def cols300 : List Int := [0,1,2,3,4,5,15,16,17,18,19,20,21,22,29]
def requiredD300 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS300 : List Int := [20,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem300_eq : pairedProblem rows300 cols300 requiredD300 requiredS300 =
    MomentData.problem300 := by rfl
theorem leaf300 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows300++rows300))
    (hc : (q.map Prod.snd).Perm (cols300++cols300))
    (hd : ∀ k ∈ requiredD300, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS300, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows300 cols300 requiredD300 requiredS300
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem300_eq] at model
  exact MomentData.excluded300 ds ss model
def rows301 : List Int := [0,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def cols301 : List Int := [0,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def requiredD301 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS301 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem301_eq : pairedProblem rows301 cols301 requiredD301 requiredS301 =
    MomentData.problem301 := by rfl
theorem leaf301 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows301++rows301))
    (hc : (q.map Prod.snd).Perm (cols301++cols301))
    (hd : ∀ k ∈ requiredD301, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS301, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows301 cols301 requiredD301 requiredS301
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem301_eq] at model
  exact MomentData.excluded301 ds ss model
def rows302 : List Int := [0,1,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols302 : List Int := [0,1,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD302 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS302 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem302_eq : pairedProblem rows302 cols302 requiredD302 requiredS302 =
    MomentData.problem302 := by rfl
theorem leaf302 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows302++rows302))
    (hc : (q.map Prod.snd).Perm (cols302++cols302))
    (hd : ∀ k ∈ requiredD302, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS302, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows302 cols302 requiredD302 requiredS302
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem302_eq] at model
  exact MomentData.excluded302 ds ss model
def rows303 : List Int := [0,1,2,11,12,13,14,15,16,17,18,26,27,28,29]
def cols303 : List Int := [0,1,2,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD303 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS303 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem303_eq : pairedProblem rows303 cols303 requiredD303 requiredS303 =
    MomentData.problem303 := by rfl
theorem leaf303 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows303++rows303))
    (hc : (q.map Prod.snd).Perm (cols303++cols303))
    (hd : ∀ k ∈ requiredD303, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS303, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows303 cols303 requiredD303 requiredS303
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem303_eq] at model
  exact MomentData.excluded303 ds ss model
def rows304 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,27,28,29]
def cols304 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,27,28,29]
def requiredD304 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS304 : List Int := [15,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem304_eq : pairedProblem rows304 cols304 requiredD304 requiredS304 =
    MomentData.problem304 := by rfl
theorem leaf304 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows304++rows304))
    (hc : (q.map Prod.snd).Perm (cols304++cols304))
    (hd : ∀ k ∈ requiredD304, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS304, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows304 cols304 requiredD304 requiredS304
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem304_eq] at model
  exact MomentData.excluded304 ds ss model
def rows305 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,28,29]
def cols305 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,28,29]
def requiredD305 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS305 : List Int := [17,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem305_eq : pairedProblem rows305 cols305 requiredD305 requiredS305 =
    MomentData.problem305 := by rfl
theorem leaf305 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows305++rows305))
    (hc : (q.map Prod.snd).Perm (cols305++cols305))
    (hd : ∀ k ∈ requiredD305, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS305, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows305 cols305 requiredD305 requiredS305
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem305_eq] at model
  exact MomentData.excluded305 ds ss model
def rows306 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,29]
def cols306 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,29]
def requiredD306 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS306 : List Int := [19,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem306_eq : pairedProblem rows306 cols306 requiredD306 requiredS306 =
    MomentData.problem306 := by rfl
theorem leaf306 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows306++rows306))
    (hc : (q.map Prod.snd).Perm (cols306++cols306))
    (hd : ∀ k ∈ requiredD306, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS306, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows306 cols306 requiredD306 requiredS306
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem306_eq] at model
  exact MomentData.excluded306 ds ss model
def rows307 : List Int := [0,1,2,3,4,5,6,15,16,17,18,19,20,21,22]
def cols307 : List Int := [0,1,2,3,4,5,6,15,16,17,18,19,20,21,22]
def requiredD307 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS307 : List Int := [21,31,32,33,34,35,36,37,38,39,40,41,42,43]
theorem problem307_eq : pairedProblem rows307 cols307 requiredD307 requiredS307 =
    MomentData.problem307 := by rfl
theorem leaf307 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows307++rows307))
    (hc : (q.map Prod.snd).Perm (cols307++cols307))
    (hd : ∀ k ∈ requiredD307, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS307, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows307 cols307 requiredD307 requiredS307
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem307_eq] at model
  exact MomentData.excluded307 ds ss model
def rows308 : List Int := [7,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols308 : List Int := [7,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD308 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS308 : List Int := [15,16,17,18,19,20,21,22,23,24,25,26,27,37]
theorem problem308_eq : pairedProblem rows308 cols308 requiredD308 requiredS308 =
    MomentData.problem308 := by rfl
theorem leaf308 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows308++rows308))
    (hc : (q.map Prod.snd).Perm (cols308++cols308))
    (hd : ∀ k ∈ requiredD308, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS308, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows308 cols308 requiredD308 requiredS308
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem308_eq] at model
  exact MomentData.excluded308 ds ss model
def rows309 : List Int := [0,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols309 : List Int := [0,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD309 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS309 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem309_eq : pairedProblem rows309 cols309 requiredD309 requiredS309 =
    MomentData.problem309 := by rfl
theorem leaf309 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows309++rows309))
    (hc : (q.map Prod.snd).Perm (cols309++cols309))
    (hd : ∀ k ∈ requiredD309, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS309, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows309 cols309 requiredD309 requiredS309
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem309_eq] at model
  exact MomentData.excluded309 ds ss model
def rows310 : List Int := [0,1,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols310 : List Int := [0,1,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD310 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS310 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem310_eq : pairedProblem rows310 cols310 requiredD310 requiredS310 =
    MomentData.problem310 := by rfl
theorem leaf310 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows310++rows310))
    (hc : (q.map Prod.snd).Perm (cols310++cols310))
    (hd : ∀ k ∈ requiredD310, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS310, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows310 cols310 requiredD310 requiredS310
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem310_eq] at model
  exact MomentData.excluded310 ds ss model
def rows311 : List Int := [0,1,2,10,11,12,13,14,15,16,17,26,27,28,29]
def cols311 : List Int := [0,1,2,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD311 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS311 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem311_eq : pairedProblem rows311 cols311 requiredD311 requiredS311 =
    MomentData.problem311 := by rfl
theorem leaf311 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows311++rows311))
    (hc : (q.map Prod.snd).Perm (cols311++cols311))
    (hd : ∀ k ∈ requiredD311, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS311, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows311 cols311 requiredD311 requiredS311
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem311_eq] at model
  exact MomentData.excluded311 ds ss model
def rows312 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,27,28,29]
def cols312 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,27,28,29]
def requiredD312 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS312 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem312_eq : pairedProblem rows312 cols312 requiredD312 requiredS312 =
    MomentData.problem312 := by rfl
theorem leaf312 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows312++rows312))
    (hc : (q.map Prod.snd).Perm (cols312++cols312))
    (hd : ∀ k ∈ requiredD312, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS312, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows312 cols312 requiredD312 requiredS312
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem312_eq] at model
  exact MomentData.excluded312 ds ss model
def rows313 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,28,29]
def cols313 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,28,29]
def requiredD313 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS313 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,47]
theorem problem313_eq : pairedProblem rows313 cols313 requiredD313 requiredS313 =
    MomentData.problem313 := by rfl
theorem leaf313 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows313++rows313))
    (hc : (q.map Prod.snd).Perm (cols313++cols313))
    (hd : ∀ k ∈ requiredD313, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS313, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows313 cols313 requiredD313 requiredS313
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem313_eq] at model
  exact MomentData.excluded313 ds ss model
def rows314 : List Int := [0,1,2,3,4,5,13,14,15,16,17,18,19,20,29]
def cols314 : List Int := [0,1,2,3,4,5,13,14,15,16,17,18,19,20,29]
def requiredD314 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS314 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,49]
theorem problem314_eq : pairedProblem rows314 cols314 requiredD314 requiredS314 =
    MomentData.problem314 := by rfl
theorem leaf314 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows314++rows314))
    (hc : (q.map Prod.snd).Perm (cols314++cols314))
    (hd : ∀ k ∈ requiredD314, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS314, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows314 cols314 requiredD314 requiredS314
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem314_eq] at model
  exact MomentData.excluded314 ds ss model
def rows315 : List Int := [0,7,8,9,10,11,12,13,14,24,25,26,27,28,29]
def cols315 : List Int := [0,7,8,9,10,11,12,13,14,24,25,26,27,28,29]
def requiredD315 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS315 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,38]
theorem problem315_eq : pairedProblem rows315 cols315 requiredD315 requiredS315 =
    MomentData.problem315 := by rfl
theorem leaf315 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows315++rows315))
    (hc : (q.map Prod.snd).Perm (cols315++cols315))
    (hd : ∀ k ∈ requiredD315, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS315, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows315 cols315 requiredD315 requiredS315
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem315_eq] at model
  exact MomentData.excluded315 ds ss model
def rows316 : List Int := [1,4,7,10,13,16,19,21,22,24,25,26,27,28,29]
def cols316 : List Int := [1,4,7,10,13,16,19,21,22,24,25,26,27,28,29]
def requiredD316 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS316 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41]
theorem problem316_eq : pairedProblem rows316 cols316 requiredD316 requiredS316 =
    MomentData.problem316 := by rfl
theorem leaf316 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows316++rows316))
    (hc : (q.map Prod.snd).Perm (cols316++cols316))
    (hd : ∀ k ∈ requiredD316, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS316, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows316 cols316 requiredD316 requiredS316
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem316_eq] at model
  exact MomentData.excluded316 ds ss model
def rows317 : List Int := [0,2,5,8,11,14,17,20,22,23,25,26,27,28,29]
def cols317 : List Int := [0,2,5,8,11,14,17,20,22,23,25,26,27,28,29]
def requiredD317 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS317 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43]
theorem problem317_eq : pairedProblem rows317 cols317 requiredD317 requiredS317 =
    MomentData.problem317 := by rfl
theorem leaf317 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows317++rows317))
    (hc : (q.map Prod.snd).Perm (cols317++cols317))
    (hd : ∀ k ∈ requiredD317, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS317, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows317 cols317 requiredD317 requiredS317
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem317_eq] at model
  exact MomentData.excluded317 ds ss model
def rows318 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols318 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD318 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS318 : List Int := [6,9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem318_eq : pairedProblem rows318 cols318 requiredD318 requiredS318 =
    MomentData.problem318 := by rfl
theorem leaf318 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows318++rows318))
    (hc : (q.map Prod.snd).Perm (cols318++cols318))
    (hd : ∀ k ∈ requiredD318, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS318, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows318 cols318 requiredD318 requiredS318
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem318_eq] at model
  exact MomentData.excluded318 ds ss model
def rows319 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols319 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD319 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS319 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem319_eq : pairedProblem rows319 cols319 requiredD319 requiredS319 =
    MomentData.problem319 := by rfl
theorem leaf319 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows319++rows319))
    (hc : (q.map Prod.snd).Perm (cols319++cols319))
    (hd : ∀ k ∈ requiredD319, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS319, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows319 cols319 requiredD319 requiredS319
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem319_eq] at model
  exact MomentData.excluded319 ds ss model
def rows320 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols320 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD320 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS320 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem320_eq : pairedProblem rows320 cols320 requiredD320 requiredS320 =
    MomentData.problem320 := by rfl
theorem leaf320 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows320++rows320))
    (hc : (q.map Prod.snd).Perm (cols320++cols320))
    (hd : ∀ k ∈ requiredD320, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS320, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows320 cols320 requiredD320 requiredS320
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem320_eq] at model
  exact MomentData.excluded320 ds ss model
def rows321 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols321 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD321 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS321 : List Int := [6,9,12,15,18,21,24,27,29,30,33,36,39,42]
theorem problem321_eq : pairedProblem rows321 cols321 requiredD321 requiredS321 =
    MomentData.problem321 := by rfl
theorem leaf321 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows321++rows321))
    (hc : (q.map Prod.snd).Perm (cols321++cols321))
    (hd : ∀ k ∈ requiredD321, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS321, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows321 cols321 requiredD321 requiredS321
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem321_eq] at model
  exact MomentData.excluded321 ds ss model
def rows322 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols322 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD322 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS322 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44,47]
theorem problem322_eq : pairedProblem rows322 cols322 requiredD322 requiredS322 =
    MomentData.problem322 := by rfl
theorem leaf322 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows322++rows322))
    (hc : (q.map Prod.snd).Perm (cols322++cols322))
    (hd : ∀ k ∈ requiredD322, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS322, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows322 cols322 requiredD322 requiredS322
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem322_eq] at model
  exact MomentData.excluded322 ds ss model
def rows323 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols323 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD323 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS323 : List Int := [11,14,17,20,23,26,29,31,32,35,38,41,44,47]
theorem problem323_eq : pairedProblem rows323 cols323 requiredD323 requiredS323 =
    MomentData.problem323 := by rfl
theorem leaf323 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows323++rows323))
    (hc : (q.map Prod.snd).Perm (cols323++cols323))
    (hd : ∀ k ∈ requiredD323, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS323, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows323 cols323 requiredD323 requiredS323
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem323_eq] at model
  exact MomentData.excluded323 ds ss model
def rows324 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols324 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD324 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS324 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem324_eq : pairedProblem rows324 cols324 requiredD324 requiredS324 =
    MomentData.problem324 := by rfl
theorem leaf324 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows324++rows324))
    (hc : (q.map Prod.snd).Perm (cols324++cols324))
    (hd : ∀ k ∈ requiredD324, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS324, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows324 cols324 requiredD324 requiredS324
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem324_eq] at model
  exact MomentData.excluded324 ds ss model
def rows325 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols325 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD325 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS325 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem325_eq : pairedProblem rows325 cols325 requiredD325 requiredS325 =
    MomentData.problem325 := by rfl
theorem leaf325 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows325++rows325))
    (hc : (q.map Prod.snd).Perm (cols325++cols325))
    (hd : ∀ k ∈ requiredD325, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS325, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows325 cols325 requiredD325 requiredS325
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem325_eq] at model
  exact MomentData.excluded325 ds ss model
def rows326 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols326 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def requiredD326 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS326 : List Int := [10,13,16,19,22,25,28,31,33,34,37,40,43,46,49]
theorem problem326_eq : pairedProblem rows326 cols326 requiredD326 requiredS326 =
    MomentData.problem326 := by rfl
theorem leaf326 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows326++rows326))
    (hc : (q.map Prod.snd).Perm (cols326++cols326))
    (hd : ∀ k ∈ requiredD326, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS326, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows326 cols326 requiredD326 requiredS326
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem326_eq] at model
  exact MomentData.excluded326 ds ss model
def rows327 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols327 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def requiredD327 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS327 : List Int := [13,16,19,22,25,28,31,33,34,37,40,43,46,49]
theorem problem327_eq : pairedProblem rows327 cols327 requiredD327 requiredS327 =
    MomentData.problem327 := by rfl
theorem leaf327 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows327++rows327))
    (hc : (q.map Prod.snd).Perm (cols327++cols327))
    (hd : ∀ k ∈ requiredD327, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS327, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows327 cols327 requiredD327 requiredS327
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem327_eq] at model
  exact MomentData.excluded327 ds ss model
def rows328 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols328 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def requiredD328 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS328 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem328_eq : pairedProblem rows328 cols328 requiredD328 requiredS328 =
    MomentData.problem328 := by rfl
theorem leaf328 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows328++rows328))
    (hc : (q.map Prod.snd).Perm (cols328++cols328))
    (hd : ∀ k ∈ requiredD328, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS328, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows328 cols328 requiredD328 requiredS328
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem328_eq] at model
  exact MomentData.excluded328 ds ss model
def rows329 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols329 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def requiredD329 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS329 : List Int := [10,13,16,19,22,25,28,31,33,34,37,40,43,46]
theorem problem329_eq : pairedProblem rows329 cols329 requiredD329 requiredS329 =
    MomentData.problem329 := by rfl
theorem leaf329 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows329++rows329))
    (hc : (q.map Prod.snd).Perm (cols329++cols329))
    (hd : ∀ k ∈ requiredD329, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS329, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows329 cols329 requiredD329 requiredS329
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem329_eq] at model
  exact MomentData.excluded329 ds ss model
def rows330 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols330 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def requiredD330 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS330 : List Int := [12,15,18,21,24,27,30,33,35,36,39,42,45,48,51]
theorem problem330_eq : pairedProblem rows330 cols330 requiredD330 requiredS330 =
    MomentData.problem330 := by rfl
theorem leaf330 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows330++rows330))
    (hc : (q.map Prod.snd).Perm (cols330++cols330))
    (hd : ∀ k ∈ requiredD330, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS330, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows330 cols330 requiredD330 requiredS330
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem330_eq] at model
  exact MomentData.excluded330 ds ss model
def rows331 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols331 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def requiredD331 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS331 : List Int := [15,18,21,24,27,30,33,35,36,39,42,45,48,51]
theorem problem331_eq : pairedProblem rows331 cols331 requiredD331 requiredS331 =
    MomentData.problem331 := by rfl
theorem leaf331 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows331++rows331))
    (hc : (q.map Prod.snd).Perm (cols331++cols331))
    (hd : ∀ k ∈ requiredD331, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS331, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows331 cols331 requiredD331 requiredS331
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem331_eq] at model
  exact MomentData.excluded331 ds ss model
def rows332 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols332 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def requiredD332 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS332 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem332_eq : pairedProblem rows332 cols332 requiredD332 requiredS332 =
    MomentData.problem332 := by rfl
theorem leaf332 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows332++rows332))
    (hc : (q.map Prod.snd).Perm (cols332++cols332))
    (hd : ∀ k ∈ requiredD332, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS332, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows332 cols332 requiredD332 requiredS332
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem332_eq] at model
  exact MomentData.excluded332 ds ss model
def rows333 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols333 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def requiredD333 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS333 : List Int := [12,15,18,21,24,27,30,33,35,36,39,42,45,48]
theorem problem333_eq : pairedProblem rows333 cols333 requiredD333 requiredS333 =
    MomentData.problem333 := by rfl
theorem leaf333 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows333++rows333))
    (hc : (q.map Prod.snd).Perm (cols333++cols333))
    (hd : ∀ k ∈ requiredD333, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS333, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows333 cols333 requiredD333 requiredS333
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem333_eq] at model
  exact MomentData.excluded333 ds ss model
def rows334 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols334 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def requiredD334 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS334 : List Int := [14,17,20,23,26,29,32,35,37,38,41,44,47,50,53]
theorem problem334_eq : pairedProblem rows334 cols334 requiredD334 requiredS334 =
    MomentData.problem334 := by rfl
theorem leaf334 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows334++rows334))
    (hc : (q.map Prod.snd).Perm (cols334++cols334))
    (hd : ∀ k ∈ requiredD334, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS334, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows334 cols334 requiredD334 requiredS334
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem334_eq] at model
  exact MomentData.excluded334 ds ss model
def rows335 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols335 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def requiredD335 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS335 : List Int := [17,20,23,26,29,32,35,37,38,41,44,47,50,53]
theorem problem335_eq : pairedProblem rows335 cols335 requiredD335 requiredS335 =
    MomentData.problem335 := by rfl
theorem leaf335 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows335++rows335))
    (hc : (q.map Prod.snd).Perm (cols335++cols335))
    (hd : ∀ k ∈ requiredD335, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS335, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows335 cols335 requiredD335 requiredS335
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem335_eq] at model
  exact MomentData.excluded335 ds ss model
def rows336 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols336 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def requiredD336 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS336 : List Int := [14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem336_eq : pairedProblem rows336 cols336 requiredD336 requiredS336 =
    MomentData.problem336 := by rfl
theorem leaf336 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows336++rows336))
    (hc : (q.map Prod.snd).Perm (cols336++cols336))
    (hd : ∀ k ∈ requiredD336, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS336, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows336 cols336 requiredD336 requiredS336
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem336_eq] at model
  exact MomentData.excluded336 ds ss model
def rows337 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols337 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def requiredD337 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS337 : List Int := [14,17,20,23,26,29,32,35,37,38,41,44,47,50]
theorem problem337_eq : pairedProblem rows337 cols337 requiredD337 requiredS337 =
    MomentData.problem337 := by rfl
theorem leaf337 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows337++rows337))
    (hc : (q.map Prod.snd).Perm (cols337++cols337))
    (hd : ∀ k ∈ requiredD337, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS337, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows337 cols337 requiredD337 requiredS337
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem337_eq] at model
  exact MomentData.excluded337 ds ss model
def rows338 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols338 : List Int := [0,2,5,7,8,11,14,17,20,23,25,26,27,28,29]
def requiredD338 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS338 : List Int := [5,8,11,14,17,20,23,26,28,29,32,35,38,41,44]
theorem problem338_eq : pairedProblem rows338 cols338 requiredD338 requiredS338 =
    MomentData.problem338 := by rfl
theorem leaf338 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows338++rows338))
    (hc : (q.map Prod.snd).Perm (cols338++cols338))
    (hd : ∀ k ∈ requiredD338, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS338, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows338 cols338 requiredD338 requiredS338
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem338_eq] at model
  exact MomentData.excluded338 ds ss model
def rows339 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols339 : List Int := [0,2,5,7,8,11,14,17,20,23,25,26,27,28,29]
def requiredD339 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS339 : List Int := [8,11,14,17,20,23,24,26,28,29,32,35,38,41,44]
theorem problem339_eq : pairedProblem rows339 cols339 requiredD339 requiredS339 =
    MomentData.problem339 := by rfl
theorem leaf339 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows339++rows339))
    (hc : (q.map Prod.snd).Perm (cols339++cols339))
    (hd : ∀ k ∈ requiredD339, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS339, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows339 cols339 requiredD339 requiredS339
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem339_eq] at model
  exact MomentData.excluded339 ds ss model
def rows340 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols340 : List Int := [0,2,5,7,8,11,14,17,20,23,25,26,27,28,29]
def requiredD340 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS340 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem340_eq : pairedProblem rows340 cols340 requiredD340 requiredS340 =
    MomentData.problem340 := by rfl
theorem leaf340 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows340++rows340))
    (hc : (q.map Prod.snd).Perm (cols340++cols340))
    (hd : ∀ k ∈ requiredD340, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS340, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows340 cols340 requiredD340 requiredS340
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem340_eq] at model
  exact MomentData.excluded340 ds ss model
def rows341 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols341 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def requiredD341 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS341 : List Int := [7,10,13,16,19,22,25,28,30,31,34,37,40,43,46]
theorem problem341_eq : pairedProblem rows341 cols341 requiredD341 requiredS341 =
    MomentData.problem341 := by rfl
theorem leaf341 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows341++rows341))
    (hc : (q.map Prod.snd).Perm (cols341++cols341))
    (hd : ∀ k ∈ requiredD341, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS341, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows341 cols341 requiredD341 requiredS341
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem341_eq] at model
  exact MomentData.excluded341 ds ss model
def rows342 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols342 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def requiredD342 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS342 : List Int := [10,13,16,19,22,25,26,28,30,31,34,37,40,43,46]
theorem problem342_eq : pairedProblem rows342 cols342 requiredD342 requiredS342 =
    MomentData.problem342 := by rfl
theorem leaf342 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows342++rows342))
    (hc : (q.map Prod.snd).Perm (cols342++cols342))
    (hd : ∀ k ∈ requiredD342, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS342, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows342 cols342 requiredD342 requiredS342
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem342_eq] at model
  exact MomentData.excluded342 ds ss model
def rows343 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols343 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def requiredD343 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS343 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem343_eq : pairedProblem rows343 cols343 requiredD343 requiredS343 =
    MomentData.problem343 := by rfl
theorem leaf343 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows343++rows343))
    (hc : (q.map Prod.snd).Perm (cols343++cols343))
    (hd : ∀ k ∈ requiredD343, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS343, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows343 cols343 requiredD343 requiredS343
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem343_eq] at model
  exact MomentData.excluded343 ds ss model
def rows344 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols344 : List Int := [0,1,2,4,7,9,10,13,16,19,22,25,27,28,29]
def requiredD344 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS344 : List Int := [9,12,15,18,21,24,27,30,32,33,36,39,42,45,48]
theorem problem344_eq : pairedProblem rows344 cols344 requiredD344 requiredS344 =
    MomentData.problem344 := by rfl
theorem leaf344 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows344++rows344))
    (hc : (q.map Prod.snd).Perm (cols344++cols344))
    (hd : ∀ k ∈ requiredD344, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS344, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows344 cols344 requiredD344 requiredS344
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem344_eq] at model
  exact MomentData.excluded344 ds ss model
def rows345 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols345 : List Int := [0,1,2,4,7,9,10,13,16,19,22,25,27,28,29]
def requiredD345 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS345 : List Int := [12,15,18,21,24,27,28,30,32,33,36,39,42,45,48]
theorem problem345_eq : pairedProblem rows345 cols345 requiredD345 requiredS345 =
    MomentData.problem345 := by rfl
theorem leaf345 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows345++rows345))
    (hc : (q.map Prod.snd).Perm (cols345++cols345))
    (hd : ∀ k ∈ requiredD345, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS345, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows345 cols345 requiredD345 requiredS345
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem345_eq] at model
  exact MomentData.excluded345 ds ss model
def rows346 : List Int := [0,1,2,3,5,8,11,14,17,20,23,25,26,28,29]
def cols346 : List Int := [0,1,2,4,7,9,10,13,16,19,22,25,27,28,29]
def requiredD346 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS346 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem346_eq : pairedProblem rows346 cols346 requiredD346 requiredS346 =
    MomentData.problem346 := by rfl
theorem leaf346 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows346++rows346))
    (hc : (q.map Prod.snd).Perm (cols346++cols346))
    (hd : ∀ k ∈ requiredD346, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS346, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows346 cols346 requiredD346 requiredS346
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem346_eq] at model
  exact MomentData.excluded346 ds ss model
def rows347 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols347 : List Int := [0,1,2,3,5,8,10,11,14,17,20,23,26,28,29]
def requiredD347 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS347 : List Int := [11,14,17,20,23,26,29,32,34,35,38,41,44,47,50]
theorem problem347_eq : pairedProblem rows347 cols347 requiredD347 requiredS347 =
    MomentData.problem347 := by rfl
theorem leaf347 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows347++rows347))
    (hc : (q.map Prod.snd).Perm (cols347++cols347))
    (hd : ∀ k ∈ requiredD347, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS347, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows347 cols347 requiredD347 requiredS347
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem347_eq] at model
  exact MomentData.excluded347 ds ss model
def rows348 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols348 : List Int := [0,1,2,3,5,8,10,11,14,17,20,23,26,28,29]
def requiredD348 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS348 : List Int := [14,17,20,23,26,29,30,32,34,35,38,41,44,47,50]
theorem problem348_eq : pairedProblem rows348 cols348 requiredD348 requiredS348 =
    MomentData.problem348 := by rfl
theorem leaf348 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows348++rows348))
    (hc : (q.map Prod.snd).Perm (cols348++cols348))
    (hd : ∀ k ∈ requiredD348, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS348, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows348 cols348 requiredD348 requiredS348
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem348_eq] at model
  exact MomentData.excluded348 ds ss model
def rows349 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,26,27,29]
def cols349 : List Int := [0,1,2,3,5,8,10,11,14,17,20,23,26,28,29]
def requiredD349 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS349 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem349_eq : pairedProblem rows349 cols349 requiredD349 requiredS349 =
    MomentData.problem349 := by rfl
theorem leaf349 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows349++rows349))
    (hc : (q.map Prod.snd).Perm (cols349++cols349))
    (hd : ∀ k ∈ requiredD349, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS349, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows349 cols349 requiredD349 requiredS349
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem349_eq] at model
  exact MomentData.excluded349 ds ss model
def rows350 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols350 : List Int := [0,1,2,3,4,6,9,11,12,15,18,21,24,27,29]
def requiredD350 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS350 : List Int := [16,19,22,25,28,31,32,34,36,37,40,43,46,49,52]
theorem problem350_eq : pairedProblem rows350 cols350 requiredD350 requiredS350 =
    MomentData.problem350 := by rfl
theorem leaf350 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows350++rows350))
    (hc : (q.map Prod.snd).Perm (cols350++cols350))
    (hd : ∀ k ∈ requiredD350, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS350, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows350 cols350 requiredD350 requiredS350
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem350_eq] at model
  exact MomentData.excluded350 ds ss model
def rows351 : List Int := [0,1,2,3,4,5,7,10,13,16,19,22,25,27,28]
def cols351 : List Int := [0,1,2,3,4,6,9,11,12,15,18,21,24,27,29]
def requiredD351 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS351 : List Int := [13,16,19,22,25,28,31,34,36,37,40,43,46,49,52]
theorem problem351_eq : pairedProblem rows351 cols351 requiredD351 requiredS351 =
    MomentData.problem351 := by rfl
theorem leaf351 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows351++rows351))
    (hc : (q.map Prod.snd).Perm (cols351++cols351))
    (hd : ∀ k ∈ requiredD351, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS351, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows351 cols351 requiredD351 requiredS351
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem351_eq] at model
  exact MomentData.excluded351 ds ss model
def rows352 : List Int := [0,2,5,8,11,14,17,18,20,23,25,26,27,28,29]
def cols352 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD352 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS352 : List Int := [6,9,12,15,18,21,22,24,27,30,33,36,39,42,45]
theorem problem352_eq : pairedProblem rows352 cols352 requiredD352 requiredS352 =
    MomentData.problem352 := by rfl
theorem leaf352 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows352++rows352))
    (hc : (q.map Prod.snd).Perm (cols352++cols352))
    (hd : ∀ k ∈ requiredD352, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS352, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows352 cols352 requiredD352 requiredS352
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem352_eq] at model
  exact MomentData.excluded352 ds ss model
def rows353 : List Int := [0,2,5,8,11,14,17,18,20,23,25,26,27,28,29]
def cols353 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD353 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS353 : List Int := [6,9,12,15,18,21,22,24,26,27,30,33,36,39,42]
theorem problem353_eq : pairedProblem rows353 cols353 requiredD353 requiredS353 =
    MomentData.problem353 := by rfl
theorem leaf353 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows353++rows353))
    (hc : (q.map Prod.snd).Perm (cols353++cols353))
    (hd : ∀ k ∈ requiredD353, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS353, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows353 cols353 requiredD353 requiredS353
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem353_eq] at model
  exact MomentData.excluded353 ds ss model
def rows354 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def cols354 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD354 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS354 : List Int := [8,11,14,17,20,23,24,26,29,32,35,38,41,44,47]
theorem problem354_eq : pairedProblem rows354 cols354 requiredD354 requiredS354 =
    MomentData.problem354 := by rfl
theorem leaf354 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows354++rows354))
    (hc : (q.map Prod.snd).Perm (cols354++cols354))
    (hd : ∀ k ∈ requiredD354, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS354, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows354 cols354 requiredD354 requiredS354
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem354_eq] at model
  exact MomentData.excluded354 ds ss model
def rows355 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def cols355 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD355 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS355 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem355_eq : pairedProblem rows355 cols355 requiredD355 requiredS355 =
    MomentData.problem355 := by rfl
theorem leaf355 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows355++rows355))
    (hc : (q.map Prod.snd).Perm (cols355++cols355))
    (hd : ∀ k ∈ requiredD355, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS355, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows355 cols355 requiredD355 requiredS355
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem355_eq] at model
  exact MomentData.excluded355 ds ss model
def rows356 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def cols356 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD356 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS356 : List Int := [8,11,14,17,20,23,24,26,28,29,32,35,38,41,44]
theorem problem356_eq : pairedProblem rows356 cols356 requiredD356 requiredS356 =
    MomentData.problem356 := by rfl
theorem leaf356 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows356++rows356))
    (hc : (q.map Prod.snd).Perm (cols356++cols356))
    (hd : ∀ k ∈ requiredD356, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS356, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows356 cols356 requiredD356 requiredS356
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem356_eq] at model
  exact MomentData.excluded356 ds ss model
def rows357 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def cols357 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD357 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS357 : List Int := [10,13,16,19,22,25,26,28,31,34,37,40,43,46,49]
theorem problem357_eq : pairedProblem rows357 cols357 requiredD357 requiredS357 =
    MomentData.problem357 := by rfl
theorem leaf357 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows357++rows357))
    (hc : (q.map Prod.snd).Perm (cols357++cols357))
    (hd : ∀ k ∈ requiredD357, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS357, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows357 cols357 requiredD357 requiredS357
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem357_eq] at model
  exact MomentData.excluded357 ds ss model
def rows358 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def cols358 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD358 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS358 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem358_eq : pairedProblem rows358 cols358 requiredD358 requiredS358 =
    MomentData.problem358 := by rfl
theorem leaf358 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows358++rows358))
    (hc : (q.map Prod.snd).Perm (cols358++cols358))
    (hd : ∀ k ∈ requiredD358, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS358, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows358 cols358 requiredD358 requiredS358
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem358_eq] at model
  exact MomentData.excluded358 ds ss model
def rows359 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def cols359 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD359 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS359 : List Int := [10,13,16,19,22,25,26,28,30,31,34,37,40,43,46]
theorem problem359_eq : pairedProblem rows359 cols359 requiredD359 requiredS359 =
    MomentData.problem359 := by rfl
theorem leaf359 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows359++rows359))
    (hc : (q.map Prod.snd).Perm (cols359++cols359))
    (hd : ∀ k ∈ requiredD359, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS359, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows359 cols359 requiredD359 requiredS359
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem359_eq] at model
  exact MomentData.excluded359 ds ss model
def rows360 : List Int := [0,1,2,3,5,8,11,14,17,20,21,23,26,28,29]
def cols360 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD360 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS360 : List Int := [12,15,18,21,24,27,28,30,33,36,39,42,45,48,51]
theorem problem360_eq : pairedProblem rows360 cols360 requiredD360 requiredS360 =
    MomentData.problem360 := by rfl
theorem leaf360 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows360++rows360))
    (hc : (q.map Prod.snd).Perm (cols360++cols360))
    (hd : ∀ k ∈ requiredD360, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS360, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows360 cols360 requiredD360 requiredS360
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem360_eq] at model
  exact MomentData.excluded360 ds ss model
def rows361 : List Int := [0,1,2,3,5,8,11,14,17,20,21,23,26,28,29]
def cols361 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD361 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS361 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem361_eq : pairedProblem rows361 cols361 requiredD361 requiredS361 =
    MomentData.problem361 := by rfl
theorem leaf361 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows361++rows361))
    (hc : (q.map Prod.snd).Perm (cols361++cols361))
    (hd : ∀ k ∈ requiredD361, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS361, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows361 cols361 requiredD361 requiredS361
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem361_eq] at model
  exact MomentData.excluded361 ds ss model
def rows362 : List Int := [0,1,2,3,5,8,11,14,17,20,21,23,26,28,29]
def cols362 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD362 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS362 : List Int := [12,15,18,21,24,27,28,30,32,33,36,39,42,45,48]
theorem problem362_eq : pairedProblem rows362 cols362 requiredD362 requiredS362 =
    MomentData.problem362 := by rfl
theorem leaf362 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows362++rows362))
    (hc : (q.map Prod.snd).Perm (cols362++cols362))
    (hd : ∀ k ∈ requiredD362, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS362, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows362 cols362 requiredD362 requiredS362
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem362_eq] at model
  exact MomentData.excluded362 ds ss model
def rows363 : List Int := [0,1,2,3,4,6,9,12,15,18,21,22,24,27,29]
def cols363 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD363 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,3,4,7,10,13,16,19]
def requiredS363 : List Int := [14,17,20,23,26,29,30,32,35,38,41,44,47,50,53]
theorem problem363_eq : pairedProblem rows363 cols363 requiredD363 requiredS363 =
    MomentData.problem363 := by rfl
theorem leaf363 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows363++rows363))
    (hc : (q.map Prod.snd).Perm (cols363++cols363))
    (hd : ∀ k ∈ requiredD363, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS363, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows363 cols363 requiredD363 requiredS363
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem363_eq] at model
  exact MomentData.excluded363 ds ss model
def rows364 : List Int := [0,1,2,3,4,6,9,12,15,18,21,22,24,27,29]
def cols364 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD364 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS364 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem364_eq : pairedProblem rows364 cols364 requiredD364 requiredS364 =
    MomentData.problem364 := by rfl
theorem leaf364 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows364++rows364))
    (hc : (q.map Prod.snd).Perm (cols364++cols364))
    (hd : ∀ k ∈ requiredD364, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS364, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows364 cols364 requiredD364 requiredS364
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem364_eq] at model
  exact MomentData.excluded364 ds ss model
def rows365 : List Int := [0,1,2,3,4,6,9,12,15,18,21,22,24,27,29]
def cols365 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD365 : List Int := [-17,-14,-11,-8,-5,-2,-1,1,3,4,7,10,13,16,19]
def requiredS365 : List Int := [14,17,20,23,26,29,30,32,34,35,38,41,44,47,50]
theorem problem365_eq : pairedProblem rows365 cols365 requiredD365 requiredS365 =
    MomentData.problem365 := by rfl
theorem leaf365 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows365++rows365))
    (hc : (q.map Prod.snd).Perm (cols365++cols365))
    (hd : ∀ k ∈ requiredD365, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS365, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows365 cols365 requiredD365 requiredS365
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem365_eq] at model
  exact MomentData.excluded365 ds ss model
def rows366 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols366 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD366 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS366 : List Int := [5,8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem366_eq : pairedProblem rows366 cols366 requiredD366 requiredS366 =
    MomentData.problem366 := by rfl
theorem leaf366 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows366++rows366))
    (hc : (q.map Prod.snd).Perm (cols366++cols366))
    (hd : ∀ k ∈ requiredD366, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS366, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows366 cols366 requiredD366 requiredS366
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem366_eq] at model
  exact MomentData.excluded366 ds ss model
def rows367 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols367 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD367 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS367 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem367_eq : pairedProblem rows367 cols367 requiredD367 requiredS367 =
    MomentData.problem367 := by rfl
theorem leaf367 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows367++rows367))
    (hc : (q.map Prod.snd).Perm (cols367++cols367))
    (hd : ∀ k ∈ requiredD367, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS367, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows367 cols367 requiredD367 requiredS367
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem367_eq] at model
  exact MomentData.excluded367 ds ss model
def rows368 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols368 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD368 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS368 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem368_eq : pairedProblem rows368 cols368 requiredD368 requiredS368 =
    MomentData.problem368 := by rfl
theorem leaf368 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows368++rows368))
    (hc : (q.map Prod.snd).Perm (cols368++cols368))
    (hd : ∀ k ∈ requiredD368, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS368, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows368 cols368 requiredD368 requiredS368
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem368_eq] at model
  exact MomentData.excluded368 ds ss model
def rows369 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols369 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD369 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS369 : List Int := [5,8,11,14,17,20,21,23,26,29,32,35,38,41]
theorem problem369_eq : pairedProblem rows369 cols369 requiredD369 requiredS369 =
    MomentData.problem369 := by rfl
theorem leaf369 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows369++rows369))
    (hc : (q.map Prod.snd).Perm (cols369++cols369))
    (hd : ∀ k ∈ requiredD369, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS369, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows369 cols369 requiredD369 requiredS369
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem369_eq] at model
  exact MomentData.excluded369 ds ss model
def rows370 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols370 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD370 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS370 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem370_eq : pairedProblem rows370 cols370 requiredD370 requiredS370 =
    MomentData.problem370 := by rfl
theorem leaf370 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows370++rows370))
    (hc : (q.map Prod.snd).Perm (cols370++cols370))
    (hd : ∀ k ∈ requiredD370, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS370, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows370 cols370 requiredD370 requiredS370
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem370_eq] at model
  exact MomentData.excluded370 ds ss model
def rows371 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols371 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD371 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS371 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem371_eq : pairedProblem rows371 cols371 requiredD371 requiredS371 =
    MomentData.problem371 := by rfl
theorem leaf371 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows371++rows371))
    (hc : (q.map Prod.snd).Perm (cols371++cols371))
    (hd : ∀ k ∈ requiredD371, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS371, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows371 cols371 requiredD371 requiredS371
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem371_eq] at model
  exact MomentData.excluded371 ds ss model
def rows372 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols372 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD372 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS372 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem372_eq : pairedProblem rows372 cols372 requiredD372 requiredS372 =
    MomentData.problem372 := by rfl
theorem leaf372 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows372++rows372))
    (hc : (q.map Prod.snd).Perm (cols372++cols372))
    (hd : ∀ k ∈ requiredD372, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS372, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows372 cols372 requiredD372 requiredS372
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem372_eq] at model
  exact MomentData.excluded372 ds ss model
def rows373 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols373 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD373 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS373 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43]
theorem problem373_eq : pairedProblem rows373 cols373 requiredD373 requiredS373 =
    MomentData.problem373 := by rfl
theorem leaf373 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows373++rows373))
    (hc : (q.map Prod.snd).Perm (cols373++cols373))
    (hd : ∀ k ∈ requiredD373, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS373, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows373 cols373 requiredD373 requiredS373
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem373_eq] at model
  exact MomentData.excluded373 ds ss model
def rows374 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols374 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD374 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS374 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45,48]
theorem problem374_eq : pairedProblem rows374 cols374 requiredD374 requiredS374 =
    MomentData.problem374 := by rfl
theorem leaf374 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows374++rows374))
    (hc : (q.map Prod.snd).Perm (cols374++cols374))
    (hd : ∀ k ∈ requiredD374, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS374, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows374 cols374 requiredD374 requiredS374
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem374_eq] at model
  exact MomentData.excluded374 ds ss model
def rows375 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols375 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD375 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS375 : List Int := [12,15,18,21,24,25,27,30,33,36,39,42,45,48]
theorem problem375_eq : pairedProblem rows375 cols375 requiredD375 requiredS375 =
    MomentData.problem375 := by rfl
theorem leaf375 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows375++rows375))
    (hc : (q.map Prod.snd).Perm (cols375++cols375))
    (hd : ∀ k ∈ requiredD375, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS375, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows375 cols375 requiredD375 requiredS375
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem375_eq] at model
  exact MomentData.excluded375 ds ss model
def rows376 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols376 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD376 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS376 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem376_eq : pairedProblem rows376 cols376 requiredD376 requiredS376 =
    MomentData.problem376 := by rfl
theorem leaf376 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows376++rows376))
    (hc : (q.map Prod.snd).Perm (cols376++cols376))
    (hd : ∀ k ∈ requiredD376, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS376, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows376 cols376 requiredD376 requiredS376
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem376_eq] at model
  exact MomentData.excluded376 ds ss model
def rows377 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols377 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD377 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS377 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem377_eq : pairedProblem rows377 cols377 requiredD377 requiredS377 =
    MomentData.problem377 := by rfl
theorem leaf377 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows377++rows377))
    (hc : (q.map Prod.snd).Perm (cols377++cols377))
    (hd : ∀ k ∈ requiredD377, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS377, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows377 cols377 requiredD377 requiredS377
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem377_eq] at model
  exact MomentData.excluded377 ds ss model
def rows378 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def cols378 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD378 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS378 : List Int := [11,14,17,20,23,26,27,29,32,35,38,41,44,47,50]
theorem problem378_eq : pairedProblem rows378 cols378 requiredD378 requiredS378 =
    MomentData.problem378 := by rfl
theorem leaf378 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows378++rows378))
    (hc : (q.map Prod.snd).Perm (cols378++cols378))
    (hd : ∀ k ∈ requiredD378, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS378, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows378 cols378 requiredD378 requiredS378
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem378_eq] at model
  exact MomentData.excluded378 ds ss model
def rows379 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def cols379 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD379 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS379 : List Int := [14,17,20,23,26,27,29,32,35,38,41,44,47,50]
theorem problem379_eq : pairedProblem rows379 cols379 requiredD379 requiredS379 =
    MomentData.problem379 := by rfl
theorem leaf379 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows379++rows379))
    (hc : (q.map Prod.snd).Perm (cols379++cols379))
    (hd : ∀ k ∈ requiredD379, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS379, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows379 cols379 requiredD379 requiredS379
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem379_eq] at model
  exact MomentData.excluded379 ds ss model
def rows380 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def cols380 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD380 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS380 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem380_eq : pairedProblem rows380 cols380 requiredD380 requiredS380 =
    MomentData.problem380 := by rfl
theorem leaf380 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows380++rows380))
    (hc : (q.map Prod.snd).Perm (cols380++cols380))
    (hd : ∀ k ∈ requiredD380, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS380, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows380 cols380 requiredD380 requiredS380
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem380_eq] at model
  exact MomentData.excluded380 ds ss model
def rows381 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def cols381 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,27,28,29]
def requiredD381 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS381 : List Int := [11,14,17,20,23,26,27,29,32,35,38,41,44,47]
theorem problem381_eq : pairedProblem rows381 cols381 requiredD381 requiredS381 =
    MomentData.problem381 := by rfl
theorem leaf381 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows381++rows381))
    (hc : (q.map Prod.snd).Perm (cols381++cols381))
    (hd : ∀ k ∈ requiredD381, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS381, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows381 cols381 requiredD381 requiredS381
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem381_eq] at model
  exact MomentData.excluded381 ds ss model
def rows382 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def cols382 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD382 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS382 : List Int := [13,16,19,22,25,28,29,31,34,37,40,43,46,49,52]
theorem problem382_eq : pairedProblem rows382 cols382 requiredD382 requiredS382 =
    MomentData.problem382 := by rfl
theorem leaf382 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows382++rows382))
    (hc : (q.map Prod.snd).Perm (cols382++cols382))
    (hd : ∀ k ∈ requiredD382, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS382, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows382 cols382 requiredD382 requiredS382
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem382_eq] at model
  exact MomentData.excluded382 ds ss model
def rows383 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def cols383 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD383 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS383 : List Int := [16,19,22,25,28,29,31,34,37,40,43,46,49,52]
theorem problem383_eq : pairedProblem rows383 cols383 requiredD383 requiredS383 =
    MomentData.problem383 := by rfl
theorem leaf383 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows383++rows383))
    (hc : (q.map Prod.snd).Perm (cols383++cols383))
    (hd : ∀ k ∈ requiredD383, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS383, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows383 cols383 requiredD383 requiredS383
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem383_eq] at model
  exact MomentData.excluded383 ds ss model
#print axioms leaf256
end Gardner.Kernel.MomentContexts
