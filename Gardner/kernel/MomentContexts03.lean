import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows384 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def cols384 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD384 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS384 : List Int := [13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem384_eq : pairedProblem rows384 cols384 requiredD384 requiredS384 =
    MomentData.problem384 := by rfl
theorem leaf384 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows384++rows384))
    (hc : (q.map Prod.snd).Perm (cols384++cols384))
    (hd : ∀ k ∈ requiredD384, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS384, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows384 cols384 requiredD384 requiredS384
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem384_eq] at model
  exact MomentData.excluded384 ds ss model
def rows385 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def cols385 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,28,29]
def requiredD385 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS385 : List Int := [13,16,19,22,25,28,29,31,34,37,40,43,46,49]
theorem problem385_eq : pairedProblem rows385 cols385 requiredD385 requiredS385 =
    MomentData.problem385 := by rfl
theorem leaf385 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows385++rows385))
    (hc : (q.map Prod.snd).Perm (cols385++cols385))
    (hd : ∀ k ∈ requiredD385, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS385, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows385 cols385 requiredD385 requiredS385
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem385_eq] at model
  exact MomentData.excluded385 ds ss model
def rows386 : List Int := [0,1,2,3,4,6,7,9,12,15,18,21,24,27,29]
def cols386 : List Int := [0,1,2,3,4,6,7,9,12,15,18,21,24,27,29]
def requiredD386 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS386 : List Int := [15,18,21,24,27,30,31,33,36,39,42,45,48,51]
theorem problem386_eq : pairedProblem rows386 cols386 requiredD386 requiredS386 =
    MomentData.problem386 := by rfl
theorem leaf386 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows386++rows386))
    (hc : (q.map Prod.snd).Perm (cols386++cols386))
    (hd : ∀ k ∈ requiredD386, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS386, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows386 cols386 requiredD386 requiredS386
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem386_eq] at model
  exact MomentData.excluded386 ds ss model
def rows387 : List Int := [0,1,2,3,4,5,7,8,10,13,16,19,22,25,28]
def cols387 : List Int := [0,1,2,3,4,5,7,8,10,13,16,19,22,25,28]
def requiredD387 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS387 : List Int := [17,20,23,26,29,32,33,35,38,41,44,47,50,53]
theorem problem387_eq : pairedProblem rows387 cols387 requiredD387 requiredS387 =
    MomentData.problem387 := by rfl
theorem leaf387 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows387++rows387))
    (hc : (q.map Prod.snd).Perm (cols387++cols387))
    (hd : ∀ k ∈ requiredD387, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS387, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows387 cols387 requiredD387 requiredS387
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem387_eq] at model
  exact MomentData.excluded387 ds ss model
def rows388 : List Int := [0,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def cols388 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD388 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS388 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,40]
theorem problem388_eq : pairedProblem rows388 cols388 requiredD388 requiredS388 =
    MomentData.problem388 := by rfl
theorem leaf388 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows388++rows388))
    (hc : (q.map Prod.snd).Perm (cols388++cols388))
    (hd : ∀ k ∈ requiredD388, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS388, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows388 cols388 requiredD388 requiredS388
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem388_eq] at model
  exact MomentData.excluded388 ds ss model
def rows389 : List Int := [0,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def cols389 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD389 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS389 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem389_eq : pairedProblem rows389 cols389 requiredD389 requiredS389 =
    MomentData.problem389 := by rfl
theorem leaf389 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows389++rows389))
    (hc : (q.map Prod.snd).Perm (cols389++cols389))
    (hd : ∀ k ∈ requiredD389, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS389, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows389 cols389 requiredD389 requiredS389
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem389_eq] at model
  exact MomentData.excluded389 ds ss model
def rows390 : List Int := [0,1,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols390 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD390 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS390 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,42]
theorem problem390_eq : pairedProblem rows390 cols390 requiredD390 requiredS390 =
    MomentData.problem390 := by rfl
theorem leaf390 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows390++rows390))
    (hc : (q.map Prod.snd).Perm (cols390++cols390))
    (hd : ∀ k ∈ requiredD390, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS390, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows390 cols390 requiredD390 requiredS390
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem390_eq] at model
  exact MomentData.excluded390 ds ss model
def rows391 : List Int := [0,1,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols391 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD391 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS391 : List Int := [10,20,21,22,23,24,25,26,27,28,29,30,31,32,42]
theorem problem391_eq : pairedProblem rows391 cols391 requiredD391 requiredS391 =
    MomentData.problem391 := by rfl
theorem leaf391 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows391++rows391))
    (hc : (q.map Prod.snd).Perm (cols391++cols391))
    (hd : ∀ k ∈ requiredD391, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS391, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows391 cols391 requiredD391 requiredS391
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem391_eq] at model
  exact MomentData.excluded391 ds ss model
def rows392 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def cols392 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD392 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS392 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,44]
theorem problem392_eq : pairedProblem rows392 cols392 requiredD392 requiredS392 =
    MomentData.problem392 := by rfl
theorem leaf392 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows392++rows392))
    (hc : (q.map Prod.snd).Perm (cols392++cols392))
    (hd : ∀ k ∈ requiredD392, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS392, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows392 cols392 requiredD392 requiredS392
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem392_eq] at model
  exact MomentData.excluded392 ds ss model
def rows393 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def cols393 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD393 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS393 : List Int := [12,22,23,24,25,26,27,28,29,30,31,32,33,34,44]
theorem problem393_eq : pairedProblem rows393 cols393 requiredD393 requiredS393 =
    MomentData.problem393 := by rfl
theorem leaf393 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows393++rows393))
    (hc : (q.map Prod.snd).Perm (cols393++cols393))
    (hd : ∀ k ∈ requiredD393, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS393, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows393 cols393 requiredD393 requiredS393
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem393_eq] at model
  exact MomentData.excluded393 ds ss model
def rows394 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,26,28,29]
def cols394 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD394 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS394 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,46]
theorem problem394_eq : pairedProblem rows394 cols394 requiredD394 requiredS394 =
    MomentData.problem394 := by rfl
theorem leaf394 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows394++rows394))
    (hc : (q.map Prod.snd).Perm (cols394++cols394))
    (hd : ∀ k ∈ requiredD394, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS394, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows394 cols394 requiredD394 requiredS394
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem394_eq] at model
  exact MomentData.excluded394 ds ss model
def rows395 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,26,28,29]
def cols395 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD395 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS395 : List Int := [14,24,25,26,27,28,29,30,31,32,33,34,35,36,46]
theorem problem395_eq : pairedProblem rows395 cols395 requiredD395 requiredS395 =
    MomentData.problem395 := by rfl
theorem leaf395 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows395++rows395))
    (hc : (q.map Prod.snd).Perm (cols395++cols395))
    (hd : ∀ k ∈ requiredD395, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS395, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows395 cols395 requiredD395 requiredS395
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem395_eq] at model
  exact MomentData.excluded395 ds ss model
def rows396 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,27,29]
def cols396 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD396 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS396 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,48]
theorem problem396_eq : pairedProblem rows396 cols396 requiredD396 requiredS396 =
    MomentData.problem396 := by rfl
theorem leaf396 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows396++rows396))
    (hc : (q.map Prod.snd).Perm (cols396++cols396))
    (hd : ∀ k ∈ requiredD396, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS396, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows396 cols396 requiredD396 requiredS396
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem396_eq] at model
  exact MomentData.excluded396 ds ss model
def rows397 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,27,29]
def cols397 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD397 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS397 : List Int := [16,26,27,28,29,30,31,32,33,34,35,36,37,38,48]
theorem problem397_eq : pairedProblem rows397 cols397 requiredD397 requiredS397 =
    MomentData.problem397 := by rfl
theorem leaf397 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows397++rows397))
    (hc : (q.map Prod.snd).Perm (cols397++cols397))
    (hd : ∀ k ∈ requiredD397, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS397, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows397 cols397 requiredD397 requiredS397
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem397_eq] at model
  exact MomentData.excluded397 ds ss model
def rows398 : List Int := [8,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def cols398 : List Int := [8,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def requiredD398 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS398 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem398_eq : pairedProblem rows398 cols398 requiredD398 requiredS398 =
    MomentData.problem398 := by rfl
theorem leaf398 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows398++rows398))
    (hc : (q.map Prod.snd).Perm (cols398++cols398))
    (hd : ∀ k ∈ requiredD398, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS398, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows398 cols398 requiredD398 requiredS398
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem398_eq] at model
  exact MomentData.excluded398 ds ss model
def rows399 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols399 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD399 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS399 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem399_eq : pairedProblem rows399 cols399 requiredD399 requiredS399 =
    MomentData.problem399 := by rfl
theorem leaf399 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows399++rows399))
    (hc : (q.map Prod.snd).Perm (cols399++cols399))
    (hd : ∀ k ∈ requiredD399, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS399, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows399 cols399 requiredD399 requiredS399
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem399_eq] at model
  exact MomentData.excluded399 ds ss model
def rows400 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols400 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD400 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS400 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem400_eq : pairedProblem rows400 cols400 requiredD400 requiredS400 =
    MomentData.problem400 := by rfl
theorem leaf400 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows400++rows400))
    (hc : (q.map Prod.snd).Perm (cols400++cols400))
    (hd : ∀ k ∈ requiredD400, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS400, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows400 cols400 requiredD400 requiredS400
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem400_eq] at model
  exact MomentData.excluded400 ds ss model
def rows401 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols401 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD401 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS401 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem401_eq : pairedProblem rows401 cols401 requiredD401 requiredS401 =
    MomentData.problem401 := by rfl
theorem leaf401 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows401++rows401))
    (hc : (q.map Prod.snd).Perm (cols401++cols401))
    (hd : ∀ k ∈ requiredD401, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS401, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows401 cols401 requiredD401 requiredS401
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem401_eq] at model
  exact MomentData.excluded401 ds ss model
def rows402 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols402 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD402 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS402 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem402_eq : pairedProblem rows402 cols402 requiredD402 requiredS402 =
    MomentData.problem402 := by rfl
theorem leaf402 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows402++rows402))
    (hc : (q.map Prod.snd).Perm (cols402++cols402))
    (hd : ∀ k ∈ requiredD402, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS402, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows402 cols402 requiredD402 requiredS402
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem402_eq] at model
  exact MomentData.excluded402 ds ss model
def rows403 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols403 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD403 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS403 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem403_eq : pairedProblem rows403 cols403 requiredD403 requiredS403 =
    MomentData.problem403 := by rfl
theorem leaf403 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows403++rows403))
    (hc : (q.map Prod.snd).Perm (cols403++cols403))
    (hd : ∀ k ∈ requiredD403, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS403, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows403 cols403 requiredD403 requiredS403
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem403_eq] at model
  exact MomentData.excluded403 ds ss model
def rows404 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols404 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD404 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS404 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem404_eq : pairedProblem rows404 cols404 requiredD404 requiredS404 =
    MomentData.problem404 := by rfl
theorem leaf404 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows404++rows404))
    (hc : (q.map Prod.snd).Perm (cols404++cols404))
    (hd : ∀ k ∈ requiredD404, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS404, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows404 cols404 requiredD404 requiredS404
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem404_eq] at model
  exact MomentData.excluded404 ds ss model
def rows405 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols405 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD405 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS405 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem405_eq : pairedProblem rows405 cols405 requiredD405 requiredS405 =
    MomentData.problem405 := by rfl
theorem leaf405 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows405++rows405))
    (hc : (q.map Prod.snd).Perm (cols405++cols405))
    (hd : ∀ k ∈ requiredD405, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS405, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows405 cols405 requiredD405 requiredS405
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem405_eq] at model
  exact MomentData.excluded405 ds ss model
def rows406 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols406 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD406 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS406 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem406_eq : pairedProblem rows406 cols406 requiredD406 requiredS406 =
    MomentData.problem406 := by rfl
theorem leaf406 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows406++rows406))
    (hc : (q.map Prod.snd).Perm (cols406++cols406))
    (hd : ∀ k ∈ requiredD406, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS406, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows406 cols406 requiredD406 requiredS406
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem406_eq] at model
  exact MomentData.excluded406 ds ss model
def rows407 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols407 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD407 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS407 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem407_eq : pairedProblem rows407 cols407 requiredD407 requiredS407 =
    MomentData.problem407 := by rfl
theorem leaf407 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows407++rows407))
    (hc : (q.map Prod.snd).Perm (cols407++cols407))
    (hd : ∀ k ∈ requiredD407, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS407, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows407 cols407 requiredD407 requiredS407
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem407_eq] at model
  exact MomentData.excluded407 ds ss model
def rows408 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols408 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD408 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS408 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem408_eq : pairedProblem rows408 cols408 requiredD408 requiredS408 =
    MomentData.problem408 := by rfl
theorem leaf408 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows408++rows408))
    (hc : (q.map Prod.snd).Perm (cols408++cols408))
    (hd : ∀ k ∈ requiredD408, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS408, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows408 cols408 requiredD408 requiredS408
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem408_eq] at model
  exact MomentData.excluded408 ds ss model
def rows409 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols409 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD409 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS409 : List Int := [13,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem409_eq : pairedProblem rows409 cols409 requiredD409 requiredS409 =
    MomentData.problem409 := by rfl
theorem leaf409 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows409++rows409))
    (hc : (q.map Prod.snd).Perm (cols409++cols409))
    (hd : ∀ k ∈ requiredD409, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS409, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows409 cols409 requiredD409 requiredS409
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem409_eq] at model
  exact MomentData.excluded409 ds ss model
def rows410 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols410 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD410 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS410 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem410_eq : pairedProblem rows410 cols410 requiredD410 requiredS410 =
    MomentData.problem410 := by rfl
theorem leaf410 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows410++rows410))
    (hc : (q.map Prod.snd).Perm (cols410++cols410))
    (hd : ∀ k ∈ requiredD410, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS410, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows410 cols410 requiredD410 requiredS410
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem410_eq] at model
  exact MomentData.excluded410 ds ss model
def rows411 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols411 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def requiredD411 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS411 : List Int := [15,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem411_eq : pairedProblem rows411 cols411 requiredD411 requiredS411 =
    MomentData.problem411 := by rfl
theorem leaf411 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows411++rows411))
    (hc : (q.map Prod.snd).Perm (cols411++cols411))
    (hd : ∀ k ∈ requiredD411, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS411, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows411 cols411 requiredD411 requiredS411
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem411_eq] at model
  exact MomentData.excluded411 ds ss model
def rows412 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols412 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def requiredD412 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS412 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem412_eq : pairedProblem rows412 cols412 requiredD412 requiredS412 =
    MomentData.problem412 := by rfl
theorem leaf412 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows412++rows412))
    (hc : (q.map Prod.snd).Perm (cols412++cols412))
    (hd : ∀ k ∈ requiredD412, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS412, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows412 cols412 requiredD412 requiredS412
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem412_eq] at model
  exact MomentData.excluded412 ds ss model
def rows413 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols413 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def requiredD413 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS413 : List Int := [15,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem413_eq : pairedProblem rows413 cols413 requiredD413 requiredS413 =
    MomentData.problem413 := by rfl
theorem leaf413 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows413++rows413))
    (hc : (q.map Prod.snd).Perm (cols413++cols413))
    (hd : ∀ k ∈ requiredD413, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS413, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows413 cols413 requiredD413 requiredS413
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem413_eq] at model
  exact MomentData.excluded413 ds ss model
def rows414 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols414 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def requiredD414 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS414 : List Int := [15,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem414_eq : pairedProblem rows414 cols414 requiredD414 requiredS414 =
    MomentData.problem414 := by rfl
theorem leaf414 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows414++rows414))
    (hc : (q.map Prod.snd).Perm (cols414++cols414))
    (hd : ∀ k ∈ requiredD414, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS414, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows414 cols414 requiredD414 requiredS414
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem414_eq] at model
  exact MomentData.excluded414 ds ss model
def rows415 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols415 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def requiredD415 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS415 : List Int := [17,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem415_eq : pairedProblem rows415 cols415 requiredD415 requiredS415 =
    MomentData.problem415 := by rfl
theorem leaf415 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows415++rows415))
    (hc : (q.map Prod.snd).Perm (cols415++cols415))
    (hd : ∀ k ∈ requiredD415, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS415, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows415 cols415 requiredD415 requiredS415
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem415_eq] at model
  exact MomentData.excluded415 ds ss model
def rows416 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols416 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def requiredD416 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS416 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem416_eq : pairedProblem rows416 cols416 requiredD416 requiredS416 =
    MomentData.problem416 := by rfl
theorem leaf416 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows416++rows416))
    (hc : (q.map Prod.snd).Perm (cols416++cols416))
    (hd : ∀ k ∈ requiredD416, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS416, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows416 cols416 requiredD416 requiredS416
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem416_eq] at model
  exact MomentData.excluded416 ds ss model
def rows417 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols417 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def requiredD417 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS417 : List Int := [17,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem417_eq : pairedProblem rows417 cols417 requiredD417 requiredS417 =
    MomentData.problem417 := by rfl
theorem leaf417 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows417++rows417))
    (hc : (q.map Prod.snd).Perm (cols417++cols417))
    (hd : ∀ k ∈ requiredD417, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS417, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows417 cols417 requiredD417 requiredS417
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem417_eq] at model
  exact MomentData.excluded417 ds ss model
def rows418 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols418 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def requiredD418 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS418 : List Int := [17,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem418_eq : pairedProblem rows418 cols418 requiredD418 requiredS418 =
    MomentData.problem418 := by rfl
theorem leaf418 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows418++rows418))
    (hc : (q.map Prod.snd).Perm (cols418++cols418))
    (hd : ∀ k ∈ requiredD418, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS418, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows418 cols418 requiredD418 requiredS418
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem418_eq] at model
  exact MomentData.excluded418 ds ss model
def rows419 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols419 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def requiredD419 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS419 : List Int := [19,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem419_eq : pairedProblem rows419 cols419 requiredD419 requiredS419 =
    MomentData.problem419 := by rfl
theorem leaf419 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows419++rows419))
    (hc : (q.map Prod.snd).Perm (cols419++cols419))
    (hd : ∀ k ∈ requiredD419, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS419, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows419 cols419 requiredD419 requiredS419
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem419_eq] at model
  exact MomentData.excluded419 ds ss model
def rows420 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols420 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def requiredD420 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS420 : List Int := [29,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem420_eq : pairedProblem rows420 cols420 requiredD420 requiredS420 =
    MomentData.problem420 := by rfl
theorem leaf420 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows420++rows420))
    (hc : (q.map Prod.snd).Perm (cols420++cols420))
    (hd : ∀ k ∈ requiredD420, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS420, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows420 cols420 requiredD420 requiredS420
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem420_eq] at model
  exact MomentData.excluded420 ds ss model
def rows421 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols421 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def requiredD421 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS421 : List Int := [19,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem421_eq : pairedProblem rows421 cols421 requiredD421 requiredS421 =
    MomentData.problem421 := by rfl
theorem leaf421 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows421++rows421))
    (hc : (q.map Prod.snd).Perm (cols421++cols421))
    (hd : ∀ k ∈ requiredD421, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS421, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows421 cols421 requiredD421 requiredS421
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem421_eq] at model
  exact MomentData.excluded421 ds ss model
def rows422 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols422 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def requiredD422 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS422 : List Int := [19,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem422_eq : pairedProblem rows422 cols422 requiredD422 requiredS422 =
    MomentData.problem422 := by rfl
theorem leaf422 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows422++rows422))
    (hc : (q.map Prod.snd).Perm (cols422++cols422))
    (hd : ∀ k ∈ requiredD422, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS422, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows422 cols422 requiredD422 requiredS422
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem422_eq] at model
  exact MomentData.excluded422 ds ss model
def rows423 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols423 : List Int := [0,2,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD423 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS423 : List Int := [10,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem423_eq : pairedProblem rows423 cols423 requiredD423 requiredS423 =
    MomentData.problem423 := by rfl
theorem leaf423 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows423++rows423))
    (hc : (q.map Prod.snd).Perm (cols423++cols423))
    (hd : ∀ k ∈ requiredD423, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS423, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows423 cols423 requiredD423 requiredS423
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem423_eq] at model
  exact MomentData.excluded423 ds ss model
def rows424 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols424 : List Int := [0,2,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD424 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS424 : List Int := [10,20,21,22,23,24,25,26,27,28,29,30,31,32,42]
theorem problem424_eq : pairedProblem rows424 cols424 requiredD424 requiredS424 =
    MomentData.problem424 := by rfl
theorem leaf424 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows424++rows424))
    (hc : (q.map Prod.snd).Perm (cols424++cols424))
    (hd : ∀ k ∈ requiredD424, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS424, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows424 cols424 requiredD424 requiredS424
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem424_eq] at model
  exact MomentData.excluded424 ds ss model
def rows425 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols425 : List Int := [0,1,3,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD425 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS425 : List Int := [12,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem425_eq : pairedProblem rows425 cols425 requiredD425 requiredS425 =
    MomentData.problem425 := by rfl
theorem leaf425 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows425++rows425))
    (hc : (q.map Prod.snd).Perm (cols425++cols425))
    (hd : ∀ k ∈ requiredD425, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS425, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows425 cols425 requiredD425 requiredS425
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem425_eq] at model
  exact MomentData.excluded425 ds ss model
def rows426 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols426 : List Int := [0,1,3,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD426 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS426 : List Int := [12,22,23,24,25,26,27,28,29,30,31,32,33,34,44]
theorem problem426_eq : pairedProblem rows426 cols426 requiredD426 requiredS426 =
    MomentData.problem426 := by rfl
theorem leaf426 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows426++rows426))
    (hc : (q.map Prod.snd).Perm (cols426++cols426))
    (hd : ∀ k ∈ requiredD426, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS426, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows426 cols426 requiredD426 requiredS426
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem426_eq] at model
  exact MomentData.excluded426 ds ss model
def rows427 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols427 : List Int := [0,1,2,4,11,12,13,14,15,16,17,18,27,28,29]
def requiredD427 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS427 : List Int := [14,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem427_eq : pairedProblem rows427 cols427 requiredD427 requiredS427 =
    MomentData.problem427 := by rfl
theorem leaf427 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows427++rows427))
    (hc : (q.map Prod.snd).Perm (cols427++cols427))
    (hd : ∀ k ∈ requiredD427, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS427, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows427 cols427 requiredD427 requiredS427
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem427_eq] at model
  exact MomentData.excluded427 ds ss model
def rows428 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,28,29]
def cols428 : List Int := [0,1,2,4,11,12,13,14,15,16,17,18,27,28,29]
def requiredD428 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS428 : List Int := [14,24,25,26,27,28,29,30,31,32,33,34,35,36,46]
theorem problem428_eq : pairedProblem rows428 cols428 requiredD428 requiredS428 =
    MomentData.problem428 := by rfl
theorem leaf428 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows428++rows428))
    (hc : (q.map Prod.snd).Perm (cols428++cols428))
    (hd : ∀ k ∈ requiredD428, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS428, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows428 cols428 requiredD428 requiredS428
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem428_eq] at model
  exact MomentData.excluded428 ds ss model
def rows429 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols429 : List Int := [0,1,2,3,5,12,13,14,15,16,17,18,19,28,29]
def requiredD429 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS429 : List Int := [16,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem429_eq : pairedProblem rows429 cols429 requiredD429 requiredS429 =
    MomentData.problem429 := by rfl
theorem leaf429 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows429++rows429))
    (hc : (q.map Prod.snd).Perm (cols429++cols429))
    (hd : ∀ k ∈ requiredD429, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS429, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows429 cols429 requiredD429 requiredS429
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem429_eq] at model
  exact MomentData.excluded429 ds ss model
def rows430 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,29]
def cols430 : List Int := [0,1,2,3,5,12,13,14,15,16,17,18,19,28,29]
def requiredD430 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS430 : List Int := [16,26,27,28,29,30,31,32,33,34,35,36,37,38,48]
theorem problem430_eq : pairedProblem rows430 cols430 requiredD430 requiredS430 =
    MomentData.problem430 := by rfl
theorem leaf430 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows430++rows430))
    (hc : (q.map Prod.snd).Perm (cols430++cols430))
    (hd : ∀ k ∈ requiredD430, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS430, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows430 cols430 requiredD430 requiredS430
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem430_eq] at model
  exact MomentData.excluded430 ds ss model
def rows431 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols431 : List Int := [0,1,2,3,4,6,13,14,15,16,17,18,19,20,29]
def requiredD431 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS431 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem431_eq : pairedProblem rows431 cols431 requiredD431 requiredS431 =
    MomentData.problem431 := by rfl
theorem leaf431 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows431++rows431))
    (hc : (q.map Prod.snd).Perm (cols431++cols431))
    (hd : ∀ k ∈ requiredD431, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS431, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows431 cols431 requiredD431 requiredS431
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem431_eq] at model
  exact MomentData.excluded431 ds ss model
def rows432 : List Int := [0,1,2,3,4,5,14,15,16,17,18,19,20,21,22]
def cols432 : List Int := [0,1,2,3,4,6,13,14,15,16,17,18,19,20,29]
def requiredD432 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS432 : List Int := [18,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem432_eq : pairedProblem rows432 cols432 requiredD432 requiredS432 =
    MomentData.problem432 := by rfl
theorem leaf432 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows432++rows432))
    (hc : (q.map Prod.snd).Perm (cols432++cols432))
    (hd : ∀ k ∈ requiredD432, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS432, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows432 cols432 requiredD432 requiredS432
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem432_eq] at model
  exact MomentData.excluded432 ds ss model
def rows433 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols433 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD433 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS433 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem433_eq : pairedProblem rows433 cols433 requiredD433 requiredS433 =
    MomentData.problem433 := by rfl
theorem leaf433 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows433++rows433))
    (hc : (q.map Prod.snd).Perm (cols433++cols433))
    (hd : ∀ k ∈ requiredD433, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS433, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows433 cols433 requiredD433 requiredS433
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem433_eq] at model
  exact MomentData.excluded433 ds ss model
def rows434 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols434 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD434 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS434 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem434_eq : pairedProblem rows434 cols434 requiredD434 requiredS434 =
    MomentData.problem434 := by rfl
theorem leaf434 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows434++rows434))
    (hc : (q.map Prod.snd).Perm (cols434++cols434))
    (hd : ∀ k ∈ requiredD434, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS434, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows434 cols434 requiredD434 requiredS434
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem434_eq] at model
  exact MomentData.excluded434 ds ss model
def rows435 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols435 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD435 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS435 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,39]
theorem problem435_eq : pairedProblem rows435 cols435 requiredD435 requiredS435 =
    MomentData.problem435 := by rfl
theorem leaf435 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows435++rows435))
    (hc : (q.map Prod.snd).Perm (cols435++cols435))
    (hd : ∀ k ∈ requiredD435, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS435, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows435 cols435 requiredD435 requiredS435
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem435_eq] at model
  exact MomentData.excluded435 ds ss model
def rows436 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols436 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD436 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS436 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29]
theorem problem436_eq : pairedProblem rows436 cols436 requiredD436 requiredS436 =
    MomentData.problem436 := by rfl
theorem leaf436 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows436++rows436))
    (hc : (q.map Prod.snd).Perm (cols436++cols436))
    (hd : ∀ k ∈ requiredD436, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS436, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows436 cols436 requiredD436 requiredS436
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem436_eq] at model
  exact MomentData.excluded436 ds ss model
def rows437 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols437 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD437 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS437 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem437_eq : pairedProblem rows437 cols437 requiredD437 requiredS437 =
    MomentData.problem437 := by rfl
theorem leaf437 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows437++rows437))
    (hc : (q.map Prod.snd).Perm (cols437++cols437))
    (hd : ∀ k ∈ requiredD437, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS437, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows437 cols437 requiredD437 requiredS437
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem437_eq] at model
  exact MomentData.excluded437 ds ss model
def rows438 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols438 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD438 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS438 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem438_eq : pairedProblem rows438 cols438 requiredD438 requiredS438 =
    MomentData.problem438 := by rfl
theorem leaf438 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows438++rows438))
    (hc : (q.map Prod.snd).Perm (cols438++cols438))
    (hd : ∀ k ∈ requiredD438, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS438, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows438 cols438 requiredD438 requiredS438
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem438_eq] at model
  exact MomentData.excluded438 ds ss model
def rows439 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols439 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD439 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS439 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem439_eq : pairedProblem rows439 cols439 requiredD439 requiredS439 =
    MomentData.problem439 := by rfl
theorem leaf439 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows439++rows439))
    (hc : (q.map Prod.snd).Perm (cols439++cols439))
    (hd : ∀ k ∈ requiredD439, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS439, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows439 cols439 requiredD439 requiredS439
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem439_eq] at model
  exact MomentData.excluded439 ds ss model
def rows440 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols440 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD440 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS440 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem440_eq : pairedProblem rows440 cols440 requiredD440 requiredS440 =
    MomentData.problem440 := by rfl
theorem leaf440 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows440++rows440))
    (hc : (q.map Prod.snd).Perm (cols440++cols440))
    (hd : ∀ k ∈ requiredD440, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS440, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows440 cols440 requiredD440 requiredS440
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem440_eq] at model
  exact MomentData.excluded440 ds ss model
def rows441 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols441 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD441 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS441 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem441_eq : pairedProblem rows441 cols441 requiredD441 requiredS441 =
    MomentData.problem441 := by rfl
theorem leaf441 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows441++rows441))
    (hc : (q.map Prod.snd).Perm (cols441++cols441))
    (hd : ∀ k ∈ requiredD441, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS441, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows441 cols441 requiredD441 requiredS441
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem441_eq] at model
  exact MomentData.excluded441 ds ss model
def rows442 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols442 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD442 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS442 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem442_eq : pairedProblem rows442 cols442 requiredD442 requiredS442 =
    MomentData.problem442 := by rfl
theorem leaf442 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows442++rows442))
    (hc : (q.map Prod.snd).Perm (cols442++cols442))
    (hd : ∀ k ∈ requiredD442, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS442, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows442 cols442 requiredD442 requiredS442
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem442_eq] at model
  exact MomentData.excluded442 ds ss model
def rows443 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols443 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD443 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS443 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem443_eq : pairedProblem rows443 cols443 requiredD443 requiredS443 =
    MomentData.problem443 := by rfl
theorem leaf443 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows443++rows443))
    (hc : (q.map Prod.snd).Perm (cols443++cols443))
    (hd : ∀ k ∈ requiredD443, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS443, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows443 cols443 requiredD443 requiredS443
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem443_eq] at model
  exact MomentData.excluded443 ds ss model
def rows444 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols444 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD444 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS444 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem444_eq : pairedProblem rows444 cols444 requiredD444 requiredS444 =
    MomentData.problem444 := by rfl
theorem leaf444 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows444++rows444))
    (hc : (q.map Prod.snd).Perm (cols444++cols444))
    (hd : ∀ k ∈ requiredD444, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS444, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows444 cols444 requiredD444 requiredS444
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem444_eq] at model
  exact MomentData.excluded444 ds ss model
def rows445 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def cols445 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD445 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS445 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem445_eq : pairedProblem rows445 cols445 requiredD445 requiredS445 =
    MomentData.problem445 := by rfl
theorem leaf445 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows445++rows445))
    (hc : (q.map Prod.snd).Perm (cols445++cols445))
    (hd : ∀ k ∈ requiredD445, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS445, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows445 cols445 requiredD445 requiredS445
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem445_eq] at model
  exact MomentData.excluded445 ds ss model
def rows446 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def cols446 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD446 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS446 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem446_eq : pairedProblem rows446 cols446 requiredD446 requiredS446 =
    MomentData.problem446 := by rfl
theorem leaf446 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows446++rows446))
    (hc : (q.map Prod.snd).Perm (cols446++cols446))
    (hd : ∀ k ∈ requiredD446, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS446, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows446 cols446 requiredD446 requiredS446
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem446_eq] at model
  exact MomentData.excluded446 ds ss model
def rows447 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def cols447 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD447 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS447 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem447_eq : pairedProblem rows447 cols447 requiredD447 requiredS447 =
    MomentData.problem447 := by rfl
theorem leaf447 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows447++rows447))
    (hc : (q.map Prod.snd).Perm (cols447++cols447))
    (hd : ∀ k ∈ requiredD447, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS447, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows447 cols447 requiredD447 requiredS447
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem447_eq] at model
  exact MomentData.excluded447 ds ss model
def rows448 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def cols448 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD448 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS448 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem448_eq : pairedProblem rows448 cols448 requiredD448 requiredS448 =
    MomentData.problem448 := by rfl
theorem leaf448 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows448++rows448))
    (hc : (q.map Prod.snd).Perm (cols448++cols448))
    (hd : ∀ k ∈ requiredD448, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS448, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows448 cols448 requiredD448 requiredS448
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem448_eq] at model
  exact MomentData.excluded448 ds ss model
def rows449 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def cols449 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD449 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS449 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,47]
theorem problem449_eq : pairedProblem rows449 cols449 requiredD449 requiredS449 =
    MomentData.problem449 := by rfl
theorem leaf449 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows449++rows449))
    (hc : (q.map Prod.snd).Perm (cols449++cols449))
    (hd : ∀ k ∈ requiredD449, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS449, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows449 cols449 requiredD449 requiredS449
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem449_eq] at model
  exact MomentData.excluded449 ds ss model
def rows450 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def cols450 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD450 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS450 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,47]
theorem problem450_eq : pairedProblem rows450 cols450 requiredD450 requiredS450 =
    MomentData.problem450 := by rfl
theorem leaf450 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows450++rows450))
    (hc : (q.map Prod.snd).Perm (cols450++cols450))
    (hd : ∀ k ∈ requiredD450, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS450, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows450 cols450 requiredD450 requiredS450
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem450_eq] at model
  exact MomentData.excluded450 ds ss model
def rows451 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def cols451 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD451 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS451 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,47]
theorem problem451_eq : pairedProblem rows451 cols451 requiredD451 requiredS451 =
    MomentData.problem451 := by rfl
theorem leaf451 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows451++rows451))
    (hc : (q.map Prod.snd).Perm (cols451++cols451))
    (hd : ∀ k ∈ requiredD451, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS451, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows451 cols451 requiredD451 requiredS451
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem451_eq] at model
  exact MomentData.excluded451 ds ss model
def rows452 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def cols452 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,28,29]
def requiredD452 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS452 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem452_eq : pairedProblem rows452 cols452 requiredD452 requiredS452 =
    MomentData.problem452 := by rfl
theorem leaf452 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows452++rows452))
    (hc : (q.map Prod.snd).Perm (cols452++cols452))
    (hd : ∀ k ∈ requiredD452, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS452, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows452 cols452 requiredD452 requiredS452
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem452_eq] at model
  exact MomentData.excluded452 ds ss model
def rows453 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def cols453 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def requiredD453 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS453 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,49]
theorem problem453_eq : pairedProblem rows453 cols453 requiredD453 requiredS453 =
    MomentData.problem453 := by rfl
theorem leaf453 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows453++rows453))
    (hc : (q.map Prod.snd).Perm (cols453++cols453))
    (hd : ∀ k ∈ requiredD453, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS453, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows453 cols453 requiredD453 requiredS453
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem453_eq] at model
  exact MomentData.excluded453 ds ss model
def rows454 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def cols454 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def requiredD454 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS454 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,49]
theorem problem454_eq : pairedProblem rows454 cols454 requiredD454 requiredS454 =
    MomentData.problem454 := by rfl
theorem leaf454 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows454++rows454))
    (hc : (q.map Prod.snd).Perm (cols454++cols454))
    (hd : ∀ k ∈ requiredD454, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS454, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows454 cols454 requiredD454 requiredS454
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem454_eq] at model
  exact MomentData.excluded454 ds ss model
def rows455 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def cols455 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def requiredD455 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS455 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,49]
theorem problem455_eq : pairedProblem rows455 cols455 requiredD455 requiredS455 =
    MomentData.problem455 := by rfl
theorem leaf455 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows455++rows455))
    (hc : (q.map Prod.snd).Perm (cols455++cols455))
    (hd : ∀ k ∈ requiredD455, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS455, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows455 cols455 requiredD455 requiredS455
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem455_eq] at model
  exact MomentData.excluded455 ds ss model
def rows456 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def cols456 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,29]
def requiredD456 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS456 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem456_eq : pairedProblem rows456 cols456 requiredD456 requiredS456 =
    MomentData.problem456 := by rfl
theorem leaf456 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows456++rows456))
    (hc : (q.map Prod.snd).Perm (cols456++cols456))
    (hd : ∀ k ∈ requiredD456, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS456, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows456 cols456 requiredD456 requiredS456
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem456_eq] at model
  exact MomentData.excluded456 ds ss model
def rows457 : List Int := [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21]
def cols457 : List Int := [0,1,2,3,4,5,13,14,15,16,17,18,19,20,21]
def requiredD457 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS457 : List Int := [28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem457_eq : pairedProblem rows457 cols457 requiredD457 requiredS457 =
    MomentData.problem457 := by rfl
theorem leaf457 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows457++rows457))
    (hc : (q.map Prod.snd).Perm (cols457++cols457))
    (hd : ∀ k ∈ requiredD457, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS457, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows457 cols457 requiredD457 requiredS457
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem457_eq] at model
  exact MomentData.excluded457 ds ss model
def rows458 : List Int := [0,3,6,9,12,15,18,20,21,23,24,26,27,28,29]
def cols458 : List Int := [0,3,6,9,12,15,18,20,21,23,24,26,27,28,29]
def requiredD458 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS458 : List Int := [3,6,9,12,15,18,21,24,26,27,30,33,36,39,42]
theorem problem458_eq : pairedProblem rows458 cols458 requiredD458 requiredS458 =
    MomentData.problem458 := by rfl
theorem leaf458 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows458++rows458))
    (hc : (q.map Prod.snd).Perm (cols458++cols458))
    (hd : ∀ k ∈ requiredD458, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS458, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows458 cols458 requiredD458 requiredS458
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem458_eq] at model
  exact MomentData.excluded458 ds ss model
def rows459 : List Int := [0,1,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols459 : List Int := [0,1,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD459 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS459 : List Int := [5,8,11,14,17,20,23,26,28,29,32,35,38,41,44]
theorem problem459_eq : pairedProblem rows459 cols459 requiredD459 requiredS459 =
    MomentData.problem459 := by rfl
theorem leaf459 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows459++rows459))
    (hc : (q.map Prod.snd).Perm (cols459++cols459))
    (hd : ∀ k ∈ requiredD459, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS459, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows459 cols459 requiredD459 requiredS459
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem459_eq] at model
  exact MomentData.excluded459 ds ss model
def rows460 : List Int := [0,1,2,5,8,11,14,17,20,22,23,25,26,28,29]
def cols460 : List Int := [0,1,2,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD460 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS460 : List Int := [7,10,13,16,19,22,25,28,30,31,34,37,40,43,46]
theorem problem460_eq : pairedProblem rows460 cols460 requiredD460 requiredS460 =
    MomentData.problem460 := by rfl
theorem leaf460 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows460++rows460))
    (hc : (q.map Prod.snd).Perm (cols460++cols460))
    (hd : ∀ k ∈ requiredD460, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS460, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows460 cols460 requiredD460 requiredS460
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem460_eq] at model
  exact MomentData.excluded460 ds ss model
def rows461 : List Int := [0,1,2,3,6,9,12,15,18,21,23,24,26,27,29]
def cols461 : List Int := [0,1,2,3,6,9,12,15,18,21,23,24,26,27,29]
def requiredD461 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS461 : List Int := [9,12,15,18,21,24,27,30,32,33,36,39,42,45,48]
theorem problem461_eq : pairedProblem rows461 cols461 requiredD461 requiredS461 =
    MomentData.problem461 := by rfl
theorem leaf461 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows461++rows461))
    (hc : (q.map Prod.snd).Perm (cols461++cols461))
    (hd : ∀ k ∈ requiredD461, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS461, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows461 cols461 requiredD461 requiredS461
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem461_eq] at model
  exact MomentData.excluded461 ds ss model
def rows462 : List Int := [0,1,2,3,4,7,10,13,16,19,22,24,25,27,28]
def cols462 : List Int := [0,1,2,3,4,7,10,13,16,19,22,24,25,27,28]
def requiredD462 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS462 : List Int := [11,14,17,20,23,26,29,32,34,35,38,41,44,47,50]
theorem problem462_eq : pairedProblem rows462 cols462 requiredD462 requiredS462 =
    MomentData.problem462 := by rfl
theorem leaf462 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows462++rows462))
    (hc : (q.map Prod.snd).Perm (cols462++cols462))
    (hd : ∀ k ∈ requiredD462, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS462, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows462 cols462 requiredD462 requiredS462
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem462_eq] at model
  exact MomentData.excluded462 ds ss model
def rows463 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols463 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD463 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS463 : List Int := [6,9,12,15,18,21,24,27,28,30,33,36,39,42,45]
theorem problem463_eq : pairedProblem rows463 cols463 requiredD463 requiredS463 =
    MomentData.problem463 := by rfl
theorem leaf463 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows463++rows463))
    (hc : (q.map Prod.snd).Perm (cols463++cols463))
    (hd : ∀ k ∈ requiredD463, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS463, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows463 cols463 requiredD463 requiredS463
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem463_eq] at model
  exact MomentData.excluded463 ds ss model
def rows464 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,26,28,29]
def cols464 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD464 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS464 : List Int := [8,11,14,17,20,23,26,29,30,32,35,38,41,44,47]
theorem problem464_eq : pairedProblem rows464 cols464 requiredD464 requiredS464 =
    MomentData.problem464 := by rfl
theorem leaf464 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows464++rows464))
    (hc : (q.map Prod.snd).Perm (cols464++cols464))
    (hd : ∀ k ∈ requiredD464, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS464, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows464 cols464 requiredD464 requiredS464
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem464_eq] at model
  exact MomentData.excluded464 ds ss model
def rows465 : List Int := [0,1,2,3,5,8,11,14,17,20,23,24,26,27,29]
def cols465 : List Int := [0,1,2,3,5,8,11,14,17,20,23,24,26,27,29]
def requiredD465 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS465 : List Int := [10,13,16,19,22,25,28,31,32,34,37,40,43,46,49]
theorem problem465_eq : pairedProblem rows465 cols465 requiredD465 requiredS465 =
    MomentData.problem465 := by rfl
theorem leaf465 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows465++rows465))
    (hc : (q.map Prod.snd).Perm (cols465++cols465))
    (hd : ∀ k ∈ requiredD465, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS465, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows465 cols465 requiredD465 requiredS465
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem465_eq] at model
  exact MomentData.excluded465 ds ss model
def rows466 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,25,27,28]
def cols466 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,25,27,28]
def requiredD466 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS466 : List Int := [12,15,18,21,24,27,30,33,34,36,39,42,45,48,51]
theorem problem466_eq : pairedProblem rows466 cols466 requiredD466 requiredS466 =
    MomentData.problem466 := by rfl
theorem leaf466 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows466++rows466))
    (hc : (q.map Prod.snd).Perm (cols466++cols466))
    (hd : ∀ k ∈ requiredD466, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS466, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows466 cols466 requiredD466 requiredS466
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem466_eq] at model
  exact MomentData.excluded466 ds ss model
def rows467 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols467 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD467 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS467 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem467_eq : pairedProblem rows467 cols467 requiredD467 requiredS467 =
    MomentData.problem467 := by rfl
theorem leaf467 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows467++rows467))
    (hc : (q.map Prod.snd).Perm (cols467++cols467))
    (hd : ∀ k ∈ requiredD467, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS467, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows467 cols467 requiredD467 requiredS467
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem467_eq] at model
  exact MomentData.excluded467 ds ss model
def rows468 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,26,28,29]
def cols468 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def requiredD468 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS468 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem468_eq : pairedProblem rows468 cols468 requiredD468 requiredS468 =
    MomentData.problem468 := by rfl
theorem leaf468 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows468++rows468))
    (hc : (q.map Prod.snd).Perm (cols468++cols468))
    (hd : ∀ k ∈ requiredD468, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS468, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows468 cols468 requiredD468 requiredS468
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem468_eq] at model
  exact MomentData.excluded468 ds ss model
def rows469 : List Int := [0,1,2,3,5,8,11,14,17,20,23,24,26,27,29]
def cols469 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def requiredD469 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS469 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem469_eq : pairedProblem rows469 cols469 requiredD469 requiredS469 =
    MomentData.problem469 := by rfl
theorem leaf469 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows469++rows469))
    (hc : (q.map Prod.snd).Perm (cols469++cols469))
    (hd : ∀ k ∈ requiredD469, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS469, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows469 cols469 requiredD469 requiredS469
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem469_eq] at model
  exact MomentData.excluded469 ds ss model
def rows470 : List Int := [0,1,2,3,4,6,9,12,15,18,21,24,25,27,28]
def cols470 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,28,29]
def requiredD470 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS470 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem470_eq : pairedProblem rows470 cols470 requiredD470 requiredS470 =
    MomentData.problem470 := by rfl
theorem leaf470 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows470++rows470))
    (hc : (q.map Prod.snd).Perm (cols470++cols470))
    (hd : ∀ k ∈ requiredD470, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS470, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows470 cols470 requiredD470 requiredS470
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem470_eq] at model
  exact MomentData.excluded470 ds ss model
def rows471 : List Int := [0,2,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols471 : List Int := [0,2,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD471 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS471 : List Int := [6,9,12,15,18,21,24,26,27,30,33,36,39,42,45]
theorem problem471_eq : pairedProblem rows471 cols471 requiredD471 requiredS471 =
    MomentData.problem471 := by rfl
theorem leaf471 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows471++rows471))
    (hc : (q.map Prod.snd).Perm (cols471++cols471))
    (hd : ∀ k ∈ requiredD471, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS471, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows471 cols471 requiredD471 requiredS471
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem471_eq] at model
  exact MomentData.excluded471 ds ss model
def rows472 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,27,28,29]
def cols472 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD472 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS472 : List Int := [8,11,14,17,20,23,26,28,29,32,35,38,41,44,47]
theorem problem472_eq : pairedProblem rows472 cols472 requiredD472 requiredS472 =
    MomentData.problem472 := by rfl
theorem leaf472 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows472++rows472))
    (hc : (q.map Prod.snd).Perm (cols472++cols472))
    (hd : ∀ k ∈ requiredD472, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS472, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows472 cols472 requiredD472 requiredS472
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem472_eq] at model
  exact MomentData.excluded472 ds ss model
def rows473 : List Int := [0,1,2,4,5,8,11,14,17,20,23,25,26,28,29]
def cols473 : List Int := [0,1,2,4,5,8,11,14,17,20,23,25,26,28,29]
def requiredD473 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS473 : List Int := [10,13,16,19,22,25,28,30,31,34,37,40,43,46,49]
theorem problem473_eq : pairedProblem rows473 cols473 requiredD473 requiredS473 =
    MomentData.problem473 := by rfl
theorem leaf473 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows473++rows473))
    (hc : (q.map Prod.snd).Perm (cols473++cols473))
    (hd : ∀ k ∈ requiredD473, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS473, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows473 cols473 requiredD473 requiredS473
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem473_eq] at model
  exact MomentData.excluded473 ds ss model
def rows474 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,26,27,29]
def cols474 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,26,27,29]
def requiredD474 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS474 : List Int := [12,15,18,21,24,27,30,32,33,36,39,42,45,48,51]
theorem problem474_eq : pairedProblem rows474 cols474 requiredD474 requiredS474 =
    MomentData.problem474 := by rfl
theorem leaf474 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows474++rows474))
    (hc : (q.map Prod.snd).Perm (cols474++cols474))
    (hd : ∀ k ∈ requiredD474, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS474, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows474 cols474 requiredD474 requiredS474
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem474_eq] at model
  exact MomentData.excluded474 ds ss model
def rows475 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,27,28]
def cols475 : List Int := [0,1,2,3,4,6,7,10,13,16,19,22,25,27,28]
def requiredD475 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS475 : List Int := [14,17,20,23,26,29,32,34,35,38,41,44,47,50,53]
theorem problem475_eq : pairedProblem rows475 cols475 requiredD475 requiredS475 =
    MomentData.problem475 := by rfl
theorem leaf475 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows475++rows475))
    (hc : (q.map Prod.snd).Perm (cols475++cols475))
    (hd : ∀ k ∈ requiredD475, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS475, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows475 cols475 requiredD475 requiredS475
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem475_eq] at model
  exact MomentData.excluded475 ds ss model
def rows476 : List Int := [1,2,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols476 : List Int := [1,2,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD476 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS476 : List Int := [5,8,11,14,17,20,23,24,26,29,32,35,38,41,44]
theorem problem476_eq : pairedProblem rows476 cols476 requiredD476 requiredS476 =
    MomentData.problem476 := by rfl
theorem leaf476 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows476++rows476))
    (hc : (q.map Prod.snd).Perm (cols476++cols476))
    (hd : ∀ k ∈ requiredD476, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS476, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows476 cols476 requiredD476 requiredS476
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem476_eq] at model
  exact MomentData.excluded476 ds ss model
def rows477 : List Int := [0,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def cols477 : List Int := [0,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD477 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS477 : List Int := [7,10,13,16,19,22,25,26,28,31,34,37,40,43,46]
theorem problem477_eq : pairedProblem rows477 cols477 requiredD477 requiredS477 =
    MomentData.problem477 := by rfl
theorem leaf477 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows477++rows477))
    (hc : (q.map Prod.snd).Perm (cols477++cols477))
    (hd : ∀ k ∈ requiredD477, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS477, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows477 cols477 requiredD477 requiredS477
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem477_eq] at model
  exact MomentData.excluded477 ds ss model
def rows478 : List Int := [0,1,3,4,6,9,12,15,18,21,24,25,27,28,29]
def cols478 : List Int := [0,1,3,4,6,9,12,15,18,21,24,25,27,28,29]
def requiredD478 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS478 : List Int := [9,12,15,18,21,24,27,28,30,33,36,39,42,45,48]
theorem problem478_eq : pairedProblem rows478 cols478 requiredD478 requiredS478 =
    MomentData.problem478 := by rfl
theorem leaf478 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows478++rows478))
    (hc : (q.map Prod.snd).Perm (cols478++cols478))
    (hd : ∀ k ∈ requiredD478, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS478, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows478 cols478 requiredD478 requiredS478
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem478_eq] at model
  exact MomentData.excluded478 ds ss model
def rows479 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,26,28,29]
def cols479 : List Int := [0,1,2,4,5,7,10,13,16,19,22,25,26,28,29]
def requiredD479 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS479 : List Int := [11,14,17,20,23,26,29,30,32,35,38,41,44,47,50]
theorem problem479_eq : pairedProblem rows479 cols479 requiredD479 requiredS479 =
    MomentData.problem479 := by rfl
theorem leaf479 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows479++rows479))
    (hc : (q.map Prod.snd).Perm (cols479++cols479))
    (hd : ∀ k ∈ requiredD479, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS479, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows479 cols479 requiredD479 requiredS479
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem479_eq] at model
  exact MomentData.excluded479 ds ss model
def rows480 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,27,29]
def cols480 : List Int := [0,1,2,3,5,6,8,11,14,17,20,23,26,27,29]
def requiredD480 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS480 : List Int := [13,16,19,22,25,28,31,32,34,37,40,43,46,49,52]
theorem problem480_eq : pairedProblem rows480 cols480 requiredD480 requiredS480 =
    MomentData.problem480 := by rfl
theorem leaf480 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows480++rows480))
    (hc : (q.map Prod.snd).Perm (cols480++cols480))
    (hd : ∀ k ∈ requiredD480, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS480, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows480 cols480 requiredD480 requiredS480
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem480_eq] at model
  exact MomentData.excluded480 ds ss model
def rows481 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def cols481 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD481 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS481 : List Int := [7,10,13,16,19,22,24,25,28,31,34,37,40,43,46]
theorem problem481_eq : pairedProblem rows481 cols481 requiredD481 requiredS481 =
    MomentData.problem481 := by rfl
theorem leaf481 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows481++rows481))
    (hc : (q.map Prod.snd).Perm (cols481++cols481))
    (hd : ∀ k ∈ requiredD481, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS481, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows481 cols481 requiredD481 requiredS481
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem481_eq] at model
  exact MomentData.excluded481 ds ss model
def rows482 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def cols482 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def requiredD482 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS482 : List Int := [9,12,15,18,21,24,26,27,30,33,36,39,42,45,48]
theorem problem482_eq : pairedProblem rows482 cols482 requiredD482 requiredS482 =
    MomentData.problem482 := by rfl
theorem leaf482 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows482++rows482))
    (hc : (q.map Prod.snd).Perm (cols482++cols482))
    (hd : ∀ k ∈ requiredD482, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS482, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows482 cols482 requiredD482 requiredS482
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem482_eq] at model
  exact MomentData.excluded482 ds ss model
def rows483 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def cols483 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def requiredD483 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS483 : List Int := [11,14,17,20,23,26,28,29,32,35,38,41,44,47,50]
theorem problem483_eq : pairedProblem rows483 cols483 requiredD483 requiredS483 =
    MomentData.problem483 := by rfl
theorem leaf483 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows483++rows483))
    (hc : (q.map Prod.snd).Perm (cols483++cols483))
    (hd : ∀ k ∈ requiredD483, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS483, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows483 cols483 requiredD483 requiredS483
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem483_eq] at model
  exact MomentData.excluded483 ds ss model
def rows484 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,28,29]
def cols484 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,28,29]
def requiredD484 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS484 : List Int := [13,16,19,22,25,28,30,31,34,37,40,43,46,49,52]
theorem problem484_eq : pairedProblem rows484 cols484 requiredD484 requiredS484 =
    MomentData.problem484 := by rfl
theorem leaf484 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows484++rows484))
    (hc : (q.map Prod.snd).Perm (cols484++cols484))
    (hd : ∀ k ∈ requiredD484, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS484, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows484 cols484 requiredD484 requiredS484
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem484_eq] at model
  exact MomentData.excluded484 ds ss model
def rows485 : List Int := [1,2,4,5,7,10,13,16,19,22,25,26,27,28,29]
def cols485 : List Int := [1,2,4,5,7,10,13,16,19,22,25,26,27,28,29]
def requiredD485 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS485 : List Int := [8,11,14,17,20,23,24,26,29,32,35,38,41,44,47]
theorem problem485_eq : pairedProblem rows485 cols485 requiredD485 requiredS485 =
    MomentData.problem485 := by rfl
theorem leaf485 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows485++rows485))
    (hc : (q.map Prod.snd).Perm (cols485++cols485))
    (hd : ∀ k ∈ requiredD485, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS485, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows485 cols485 requiredD485 requiredS485
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem485_eq] at model
  exact MomentData.excluded485 ds ss model
def rows486 : List Int := [0,2,3,5,6,8,11,14,17,20,23,26,27,28,29]
def cols486 : List Int := [0,2,3,5,6,8,11,14,17,20,23,26,27,28,29]
def requiredD486 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS486 : List Int := [10,13,16,19,22,25,26,28,31,34,37,40,43,46,49]
theorem problem486_eq : pairedProblem rows486 cols486 requiredD486 requiredS486 =
    MomentData.problem486 := by rfl
theorem leaf486 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows486++rows486))
    (hc : (q.map Prod.snd).Perm (cols486++cols486))
    (hd : ∀ k ∈ requiredD486, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS486, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows486 cols486 requiredD486 requiredS486
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem486_eq] at model
  exact MomentData.excluded486 ds ss model
def rows487 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,27,28,29]
def cols487 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,27,28,29]
def requiredD487 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS487 : List Int := [12,15,18,21,24,27,28,30,33,36,39,42,45,48,51]
theorem problem487_eq : pairedProblem rows487 cols487 requiredD487 requiredS487 =
    MomentData.problem487 := by rfl
theorem leaf487 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows487++rows487))
    (hc : (q.map Prod.snd).Perm (cols487++cols487))
    (hd : ∀ k ∈ requiredD487, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS487, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows487 cols487 requiredD487 requiredS487
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem487_eq] at model
  exact MomentData.excluded487 ds ss model
def rows488 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,28,29]
def cols488 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,28,29]
def requiredD488 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS488 : List Int := [14,17,20,23,26,29,30,32,35,38,41,44,47,50,53]
theorem problem488_eq : pairedProblem rows488 cols488 requiredD488 requiredS488 =
    MomentData.problem488 := by rfl
theorem leaf488 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows488++rows488))
    (hc : (q.map Prod.snd).Perm (cols488++cols488))
    (hd : ∀ k ∈ requiredD488, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS488, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows488 cols488 requiredD488 requiredS488
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem488_eq] at model
  exact MomentData.excluded488 ds ss model
def rows489 : List Int := [0,1,2,3,5,6,8,9,11,14,17,20,23,26,29]
def cols489 : List Int := [0,1,2,3,5,6,8,9,11,14,17,20,23,26,29]
def requiredD489 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS489 : List Int := [16,19,22,25,28,31,32,34,37,40,43,46,49,52,55]
theorem problem489_eq : pairedProblem rows489 cols489 requiredD489 requiredS489 =
    MomentData.problem489 := by rfl
theorem leaf489 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows489++rows489))
    (hc : (q.map Prod.snd).Perm (cols489++cols489))
    (hd : ∀ k ∈ requiredD489, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS489, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows489 cols489 requiredD489 requiredS489
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem489_eq] at model
  exact MomentData.excluded489 ds ss model
def rows490 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols490 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD490 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS490 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,42]
theorem problem490_eq : pairedProblem rows490 cols490 requiredD490 requiredS490 =
    MomentData.problem490 := by rfl
theorem leaf490 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows490++rows490))
    (hc : (q.map Prod.snd).Perm (cols490++cols490))
    (hd : ∀ k ∈ requiredD490, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS490, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows490 cols490 requiredD490 requiredS490
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem490_eq] at model
  exact MomentData.excluded490 ds ss model
def rows491 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols491 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD491 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS491 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem491_eq : pairedProblem rows491 cols491 requiredD491 requiredS491 =
    MomentData.problem491 := by rfl
theorem leaf491 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows491++rows491))
    (hc : (q.map Prod.snd).Perm (cols491++cols491))
    (hd : ∀ k ∈ requiredD491, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS491, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows491 cols491 requiredD491 requiredS491
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem491_eq] at model
  exact MomentData.excluded491 ds ss model
def rows492 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols492 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD492 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS492 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,44]
theorem problem492_eq : pairedProblem rows492 cols492 requiredD492 requiredS492 =
    MomentData.problem492 := by rfl
theorem leaf492 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows492++rows492))
    (hc : (q.map Prod.snd).Perm (cols492++cols492))
    (hd : ∀ k ∈ requiredD492, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS492, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows492 cols492 requiredD492 requiredS492
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem492_eq] at model
  exact MomentData.excluded492 ds ss model
def rows493 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols493 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD493 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS493 : List Int := [10,21,22,23,24,25,26,27,28,29,30,31,32,33,44]
theorem problem493_eq : pairedProblem rows493 cols493 requiredD493 requiredS493 =
    MomentData.problem493 := by rfl
theorem leaf493 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows493++rows493))
    (hc : (q.map Prod.snd).Perm (cols493++cols493))
    (hd : ∀ k ∈ requiredD493, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS493, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows493 cols493 requiredD493 requiredS493
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem493_eq] at model
  exact MomentData.excluded493 ds ss model
def rows494 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols494 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD494 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS494 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem494_eq : pairedProblem rows494 cols494 requiredD494 requiredS494 =
    MomentData.problem494 := by rfl
theorem leaf494 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows494++rows494))
    (hc : (q.map Prod.snd).Perm (cols494++cols494))
    (hd : ∀ k ∈ requiredD494, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS494, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows494 cols494 requiredD494 requiredS494
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem494_eq] at model
  exact MomentData.excluded494 ds ss model
def rows495 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,25,28,29]
def cols495 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD495 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS495 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,46]
theorem problem495_eq : pairedProblem rows495 cols495 requiredD495 requiredS495 =
    MomentData.problem495 := by rfl
theorem leaf495 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows495++rows495))
    (hc : (q.map Prod.snd).Perm (cols495++cols495))
    (hd : ∀ k ∈ requiredD495, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS495, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows495 cols495 requiredD495 requiredS495
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem495_eq] at model
  exact MomentData.excluded495 ds ss model
def rows496 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,25,28,29]
def cols496 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD496 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS496 : List Int := [12,23,24,25,26,27,28,29,30,31,32,33,34,35,46]
theorem problem496_eq : pairedProblem rows496 cols496 requiredD496 requiredS496 =
    MomentData.problem496 := by rfl
theorem leaf496 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows496++rows496))
    (hc : (q.map Prod.snd).Perm (cols496++cols496))
    (hd : ∀ k ∈ requiredD496, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS496, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows496 cols496 requiredD496 requiredS496
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem496_eq] at model
  exact MomentData.excluded496 ds ss model
def rows497 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,25,28,29]
def cols497 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD497 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS497 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem497_eq : pairedProblem rows497 cols497 requiredD497 requiredS497 =
    MomentData.problem497 := by rfl
theorem leaf497 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows497++rows497))
    (hc : (q.map Prod.snd).Perm (cols497++cols497))
    (hd : ∀ k ∈ requiredD497, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS497, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows497 cols497 requiredD497 requiredS497
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem497_eq] at model
  exact MomentData.excluded497 ds ss model
def rows498 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,26,29]
def cols498 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD498 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS498 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,48]
theorem problem498_eq : pairedProblem rows498 cols498 requiredD498 requiredS498 =
    MomentData.problem498 := by rfl
theorem leaf498 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows498++rows498))
    (hc : (q.map Prod.snd).Perm (cols498++cols498))
    (hd : ∀ k ∈ requiredD498, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS498, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows498 cols498 requiredD498 requiredS498
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem498_eq] at model
  exact MomentData.excluded498 ds ss model
def rows499 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,26,29]
def cols499 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD499 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS499 : List Int := [14,25,26,27,28,29,30,31,32,33,34,35,36,37,48]
theorem problem499_eq : pairedProblem rows499 cols499 requiredD499 requiredS499 =
    MomentData.problem499 := by rfl
theorem leaf499 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows499++rows499))
    (hc : (q.map Prod.snd).Perm (cols499++cols499))
    (hd : ∀ k ∈ requiredD499, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS499, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows499 cols499 requiredD499 requiredS499
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem499_eq] at model
  exact MomentData.excluded499 ds ss model
def rows500 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,26,29]
def cols500 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD500 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS500 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem500_eq : pairedProblem rows500 cols500 requiredD500 requiredS500 =
    MomentData.problem500 := by rfl
theorem leaf500 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows500++rows500))
    (hc : (q.map Prod.snd).Perm (cols500++cols500))
    (hd : ∀ k ∈ requiredD500, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS500, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows500 cols500 requiredD500 requiredS500
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem500_eq] at model
  exact MomentData.excluded500 ds ss model
def rows501 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,27]
def cols501 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def requiredD501 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS501 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem501_eq : pairedProblem rows501 cols501 requiredD501 requiredS501 =
    MomentData.problem501 := by rfl
theorem leaf501 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows501++rows501))
    (hc : (q.map Prod.snd).Perm (cols501++cols501))
    (hd : ∀ k ∈ requiredD501, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS501, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows501 cols501 requiredD501 requiredS501
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem501_eq] at model
  exact MomentData.excluded501 ds ss model
def rows502 : List Int := [0,10,11,12,13,14,15,16,17,18,19,26,27,28,29]
def cols502 : List Int := [0,10,11,12,13,14,15,16,17,18,19,26,27,28,29]
def requiredD502 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS502 : List Int := [10,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem502_eq : pairedProblem rows502 cols502 requiredD502 requiredS502 =
    MomentData.problem502 := by rfl
theorem leaf502 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows502++rows502))
    (hc : (q.map Prod.snd).Perm (cols502++cols502))
    (hd : ∀ k ∈ requiredD502, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS502, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows502 cols502 requiredD502 requiredS502
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem502_eq] at model
  exact MomentData.excluded502 ds ss model
def rows503 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols503 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def requiredD503 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS503 : List Int := [12,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem503_eq : pairedProblem rows503 cols503 requiredD503 requiredS503 =
    MomentData.problem503 := by rfl
theorem leaf503 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows503++rows503))
    (hc : (q.map Prod.snd).Perm (cols503++cols503))
    (hd : ∀ k ∈ requiredD503, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS503, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows503 cols503 requiredD503 requiredS503
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem503_eq] at model
  exact MomentData.excluded503 ds ss model
def rows504 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,28,29]
def cols504 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,28,29]
def requiredD504 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS504 : List Int := [14,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem504_eq : pairedProblem rows504 cols504 requiredD504 requiredS504 =
    MomentData.problem504 := by rfl
theorem leaf504 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows504++rows504))
    (hc : (q.map Prod.snd).Perm (cols504++cols504))
    (hd : ∀ k ∈ requiredD504, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS504, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows504 cols504 requiredD504 requiredS504
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem504_eq] at model
  exact MomentData.excluded504 ds ss model
def rows505 : List Int := [0,1,2,3,13,14,15,16,17,18,19,20,21,22,29]
def cols505 : List Int := [0,1,2,3,13,14,15,16,17,18,19,20,21,22,29]
def requiredD505 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS505 : List Int := [16,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem505_eq : pairedProblem rows505 cols505 requiredD505 requiredS505 =
    MomentData.problem505 := by rfl
theorem leaf505 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows505++rows505))
    (hc : (q.map Prod.snd).Perm (cols505++cols505))
    (hd : ∀ k ∈ requiredD505, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS505, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows505 cols505 requiredD505 requiredS505
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem505_eq] at model
  exact MomentData.excluded505 ds ss model
def rows506 : List Int := [0,1,2,3,4,14,15,16,17,18,19,20,21,22,23]
def cols506 : List Int := [0,1,2,3,4,14,15,16,17,18,19,20,21,22,23]
def requiredD506 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS506 : List Int := [18,29,30,31,32,33,34,35,36,37,38,39,40,41,42]
theorem problem506_eq : pairedProblem rows506 cols506 requiredD506 requiredS506 =
    MomentData.problem506 := by rfl
theorem leaf506 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows506++rows506))
    (hc : (q.map Prod.snd).Perm (cols506++cols506))
    (hd : ∀ k ∈ requiredD506, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS506, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows506 cols506 requiredD506 requiredS506
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem506_eq] at model
  exact MomentData.excluded506 ds ss model
def rows507 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols507 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def requiredD507 : List Int := [-14,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10]
def requiredS507 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem507_eq : pairedProblem rows507 cols507 requiredD507 requiredS507 =
    MomentData.problem507 := by rfl
theorem leaf507 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows507++rows507))
    (hc : (q.map Prod.snd).Perm (cols507++cols507))
    (hd : ∀ k ∈ requiredD507, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS507, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows507 cols507 requiredD507 requiredS507
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem507_eq] at model
  exact MomentData.excluded507 ds ss model
def rows508 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,28,29]
def cols508 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def requiredD508 : List Int := [-14,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10]
def requiredS508 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem508_eq : pairedProblem rows508 cols508 requiredD508 requiredS508 =
    MomentData.problem508 := by rfl
theorem leaf508 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows508++rows508))
    (hc : (q.map Prod.snd).Perm (cols508++cols508))
    (hd : ∀ k ∈ requiredD508, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS508, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows508 cols508 requiredD508 requiredS508
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem508_eq] at model
  exact MomentData.excluded508 ds ss model
def rows509 : List Int := [0,1,2,3,13,14,15,16,17,18,19,20,21,22,29]
def cols509 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD509 : List Int := [-14,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10]
def requiredS509 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem509_eq : pairedProblem rows509 cols509 requiredD509 requiredS509 =
    MomentData.problem509 := by rfl
theorem leaf509 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows509++rows509))
    (hc : (q.map Prod.snd).Perm (cols509++cols509))
    (hd : ∀ k ∈ requiredD509, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS509, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows509 cols509 requiredD509 requiredS509
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem509_eq] at model
  exact MomentData.excluded509 ds ss model
def rows510 : List Int := [0,1,2,3,4,14,15,16,17,18,19,20,21,22,23]
def cols510 : List Int := [0,1,2,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD510 : List Int := [-14,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10]
def requiredS510 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem510_eq : pairedProblem rows510 cols510 requiredD510 requiredS510 =
    MomentData.problem510 := by rfl
theorem leaf510 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows510++rows510))
    (hc : (q.map Prod.snd).Perm (cols510++cols510))
    (hd : ∀ k ∈ requiredD510, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS510, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows510 cols510 requiredD510 requiredS510
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem510_eq] at model
  exact MomentData.excluded510 ds ss model
def rows511 : List Int := [8,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols511 : List Int := [8,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD511 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS511 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem511_eq : pairedProblem rows511 cols511 requiredD511 requiredS511 =
    MomentData.problem511 := by rfl
theorem leaf511 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows511++rows511))
    (hc : (q.map Prod.snd).Perm (cols511++cols511))
    (hd : ∀ k ∈ requiredD511, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS511, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows511 cols511 requiredD511 requiredS511
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem511_eq] at model
  exact MomentData.excluded511 ds ss model
#print axioms leaf384
end Gardner.Kernel.MomentContexts
