import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows512 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols512 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD512 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS512 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem512_eq : pairedProblem rows512 cols512 requiredD512 requiredS512 =
    MomentData.problem512 := by rfl
theorem leaf512 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows512++rows512))
    (hc : (q.map Prod.snd).Perm (cols512++cols512))
    (hd : ∀ k ∈ requiredD512, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS512, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows512 cols512 requiredD512 requiredS512
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem512_eq] at model
  exact MomentData.excluded512 ds ss model
def rows513 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols513 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD513 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS513 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem513_eq : pairedProblem rows513 cols513 requiredD513 requiredS513 =
    MomentData.problem513 := by rfl
theorem leaf513 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows513++rows513))
    (hc : (q.map Prod.snd).Perm (cols513++cols513))
    (hd : ∀ k ∈ requiredD513, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS513, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows513 cols513 requiredD513 requiredS513
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem513_eq] at model
  exact MomentData.excluded513 ds ss model
def rows514 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols514 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD514 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS514 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem514_eq : pairedProblem rows514 cols514 requiredD514 requiredS514 =
    MomentData.problem514 := by rfl
theorem leaf514 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows514++rows514))
    (hc : (q.map Prod.snd).Perm (cols514++cols514))
    (hd : ∀ k ∈ requiredD514, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS514, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows514 cols514 requiredD514 requiredS514
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem514_eq] at model
  exact MomentData.excluded514 ds ss model
def rows515 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols515 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD515 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS515 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem515_eq : pairedProblem rows515 cols515 requiredD515 requiredS515 =
    MomentData.problem515 := by rfl
theorem leaf515 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows515++rows515))
    (hc : (q.map Prod.snd).Perm (cols515++cols515))
    (hd : ∀ k ∈ requiredD515, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS515, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows515 cols515 requiredD515 requiredS515
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem515_eq] at model
  exact MomentData.excluded515 ds ss model
def rows516 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols516 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD516 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS516 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem516_eq : pairedProblem rows516 cols516 requiredD516 requiredS516 =
    MomentData.problem516 := by rfl
theorem leaf516 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows516++rows516))
    (hc : (q.map Prod.snd).Perm (cols516++cols516))
    (hd : ∀ k ∈ requiredD516, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS516, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows516 cols516 requiredD516 requiredS516
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem516_eq] at model
  exact MomentData.excluded516 ds ss model
def rows517 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols517 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD517 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS517 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem517_eq : pairedProblem rows517 cols517 requiredD517 requiredS517 =
    MomentData.problem517 := by rfl
theorem leaf517 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows517++rows517))
    (hc : (q.map Prod.snd).Perm (cols517++cols517))
    (hd : ∀ k ∈ requiredD517, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS517, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows517 cols517 requiredD517 requiredS517
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem517_eq] at model
  exact MomentData.excluded517 ds ss model
def rows518 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols518 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD518 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS518 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem518_eq : pairedProblem rows518 cols518 requiredD518 requiredS518 =
    MomentData.problem518 := by rfl
theorem leaf518 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows518++rows518))
    (hc : (q.map Prod.snd).Perm (cols518++cols518))
    (hd : ∀ k ∈ requiredD518, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS518, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows518 cols518 requiredD518 requiredS518
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem518_eq] at model
  exact MomentData.excluded518 ds ss model
def rows519 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols519 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD519 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS519 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem519_eq : pairedProblem rows519 cols519 requiredD519 requiredS519 =
    MomentData.problem519 := by rfl
theorem leaf519 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows519++rows519))
    (hc : (q.map Prod.snd).Perm (cols519++cols519))
    (hd : ∀ k ∈ requiredD519, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS519, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows519 cols519 requiredD519 requiredS519
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem519_eq] at model
  exact MomentData.excluded519 ds ss model
def rows520 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols520 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD520 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS520 : List Int := [13,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem520_eq : pairedProblem rows520 cols520 requiredD520 requiredS520 =
    MomentData.problem520 := by rfl
theorem leaf520 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows520++rows520))
    (hc : (q.map Prod.snd).Perm (cols520++cols520))
    (hd : ∀ k ∈ requiredD520, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS520, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows520 cols520 requiredD520 requiredS520
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem520_eq] at model
  exact MomentData.excluded520 ds ss model
def rows521 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols521 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD521 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS521 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem521_eq : pairedProblem rows521 cols521 requiredD521 requiredS521 =
    MomentData.problem521 := by rfl
theorem leaf521 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows521++rows521))
    (hc : (q.map Prod.snd).Perm (cols521++cols521))
    (hd : ∀ k ∈ requiredD521, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS521, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows521 cols521 requiredD521 requiredS521
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem521_eq] at model
  exact MomentData.excluded521 ds ss model
def rows522 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols522 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD522 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS522 : List Int := [13,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem522_eq : pairedProblem rows522 cols522 requiredD522 requiredS522 =
    MomentData.problem522 := by rfl
theorem leaf522 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows522++rows522))
    (hc : (q.map Prod.snd).Perm (cols522++cols522))
    (hd : ∀ k ∈ requiredD522, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS522, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows522 cols522 requiredD522 requiredS522
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem522_eq] at model
  exact MomentData.excluded522 ds ss model
def rows523 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols523 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD523 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS523 : List Int := [13,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem523_eq : pairedProblem rows523 cols523 requiredD523 requiredS523 =
    MomentData.problem523 := by rfl
theorem leaf523 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows523++rows523))
    (hc : (q.map Prod.snd).Perm (cols523++cols523))
    (hd : ∀ k ∈ requiredD523, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS523, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows523 cols523 requiredD523 requiredS523
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem523_eq] at model
  exact MomentData.excluded523 ds ss model
def rows524 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols524 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def requiredD524 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS524 : List Int := [15,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem524_eq : pairedProblem rows524 cols524 requiredD524 requiredS524 =
    MomentData.problem524 := by rfl
theorem leaf524 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows524++rows524))
    (hc : (q.map Prod.snd).Perm (cols524++cols524))
    (hd : ∀ k ∈ requiredD524, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS524, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows524 cols524 requiredD524 requiredS524
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem524_eq] at model
  exact MomentData.excluded524 ds ss model
def rows525 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols525 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def requiredD525 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS525 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem525_eq : pairedProblem rows525 cols525 requiredD525 requiredS525 =
    MomentData.problem525 := by rfl
theorem leaf525 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows525++rows525))
    (hc : (q.map Prod.snd).Perm (cols525++cols525))
    (hd : ∀ k ∈ requiredD525, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS525, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows525 cols525 requiredD525 requiredS525
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem525_eq] at model
  exact MomentData.excluded525 ds ss model
def rows526 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols526 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def requiredD526 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS526 : List Int := [15,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem526_eq : pairedProblem rows526 cols526 requiredD526 requiredS526 =
    MomentData.problem526 := by rfl
theorem leaf526 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows526++rows526))
    (hc : (q.map Prod.snd).Perm (cols526++cols526))
    (hd : ∀ k ∈ requiredD526, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS526, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows526 cols526 requiredD526 requiredS526
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem526_eq] at model
  exact MomentData.excluded526 ds ss model
def rows527 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols527 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def requiredD527 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS527 : List Int := [15,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem527_eq : pairedProblem rows527 cols527 requiredD527 requiredS527 =
    MomentData.problem527 := by rfl
theorem leaf527 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows527++rows527))
    (hc : (q.map Prod.snd).Perm (cols527++cols527))
    (hd : ∀ k ∈ requiredD527, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS527, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows527 cols527 requiredD527 requiredS527
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem527_eq] at model
  exact MomentData.excluded527 ds ss model
def rows528 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols528 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def requiredD528 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS528 : List Int := [17,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem528_eq : pairedProblem rows528 cols528 requiredD528 requiredS528 =
    MomentData.problem528 := by rfl
theorem leaf528 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows528++rows528))
    (hc : (q.map Prod.snd).Perm (cols528++cols528))
    (hd : ∀ k ∈ requiredD528, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS528, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows528 cols528 requiredD528 requiredS528
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem528_eq] at model
  exact MomentData.excluded528 ds ss model
def rows529 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols529 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def requiredD529 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS529 : List Int := [28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem529_eq : pairedProblem rows529 cols529 requiredD529 requiredS529 =
    MomentData.problem529 := by rfl
theorem leaf529 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows529++rows529))
    (hc : (q.map Prod.snd).Perm (cols529++cols529))
    (hd : ∀ k ∈ requiredD529, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS529, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows529 cols529 requiredD529 requiredS529
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem529_eq] at model
  exact MomentData.excluded529 ds ss model
def rows530 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols530 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def requiredD530 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS530 : List Int := [17,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem530_eq : pairedProblem rows530 cols530 requiredD530 requiredS530 =
    MomentData.problem530 := by rfl
theorem leaf530 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows530++rows530))
    (hc : (q.map Prod.snd).Perm (cols530++cols530))
    (hd : ∀ k ∈ requiredD530, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS530, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows530 cols530 requiredD530 requiredS530
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem530_eq] at model
  exact MomentData.excluded530 ds ss model
def rows531 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols531 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def requiredD531 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS531 : List Int := [17,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem531_eq : pairedProblem rows531 cols531 requiredD531 requiredS531 =
    MomentData.problem531 := by rfl
theorem leaf531 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows531++rows531))
    (hc : (q.map Prod.snd).Perm (cols531++cols531))
    (hd : ∀ k ∈ requiredD531, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS531, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows531 cols531 requiredD531 requiredS531
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem531_eq] at model
  exact MomentData.excluded531 ds ss model
def rows532 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols532 : List Int := [2,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD532 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS532 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem532_eq : pairedProblem rows532 cols532 requiredD532 requiredS532 =
    MomentData.problem532 := by rfl
theorem leaf532 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows532++rows532))
    (hc : (q.map Prod.snd).Perm (cols532++cols532))
    (hd : ∀ k ∈ requiredD532, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS532, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows532 cols532 requiredD532 requiredS532
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem532_eq] at model
  exact MomentData.excluded532 ds ss model
def rows533 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols533 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD533 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS533 : List Int := [10,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem533_eq : pairedProblem rows533 cols533 requiredD533 requiredS533 =
    MomentData.problem533 := by rfl
theorem leaf533 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows533++rows533))
    (hc : (q.map Prod.snd).Perm (cols533++cols533))
    (hd : ∀ k ∈ requiredD533, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS533, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows533 cols533 requiredD533 requiredS533
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem533_eq] at model
  exact MomentData.excluded533 ds ss model
def rows534 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols534 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD534 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS534 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem534_eq : pairedProblem rows534 cols534 requiredD534 requiredS534 =
    MomentData.problem534 := by rfl
theorem leaf534 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows534++rows534))
    (hc : (q.map Prod.snd).Perm (cols534++cols534))
    (hd : ∀ k ∈ requiredD534, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS534, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows534 cols534 requiredD534 requiredS534
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem534_eq] at model
  exact MomentData.excluded534 ds ss model
def rows535 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols535 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD535 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS535 : List Int := [10,21,22,23,24,25,26,27,28,29,30,31,32,33,44]
theorem problem535_eq : pairedProblem rows535 cols535 requiredD535 requiredS535 =
    MomentData.problem535 := by rfl
theorem leaf535 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows535++rows535))
    (hc : (q.map Prod.snd).Perm (cols535++cols535))
    (hd : ∀ k ∈ requiredD535, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS535, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows535 cols535 requiredD535 requiredS535
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem535_eq] at model
  exact MomentData.excluded535 ds ss model
def rows536 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols536 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD536 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS536 : List Int := [12,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem536_eq : pairedProblem rows536 cols536 requiredD536 requiredS536 =
    MomentData.problem536 := by rfl
theorem leaf536 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows536++rows536))
    (hc : (q.map Prod.snd).Perm (cols536++cols536))
    (hd : ∀ k ∈ requiredD536, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS536, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows536 cols536 requiredD536 requiredS536
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem536_eq] at model
  exact MomentData.excluded536 ds ss model
def rows537 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols537 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD537 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS537 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem537_eq : pairedProblem rows537 cols537 requiredD537 requiredS537 =
    MomentData.problem537 := by rfl
theorem leaf537 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows537++rows537))
    (hc : (q.map Prod.snd).Perm (cols537++cols537))
    (hd : ∀ k ∈ requiredD537, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS537, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows537 cols537 requiredD537 requiredS537
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem537_eq] at model
  exact MomentData.excluded537 ds ss model
def rows538 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,28,29]
def cols538 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD538 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS538 : List Int := [12,23,24,25,26,27,28,29,30,31,32,33,34,35,46]
theorem problem538_eq : pairedProblem rows538 cols538 requiredD538 requiredS538 =
    MomentData.problem538 := by rfl
theorem leaf538 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows538++rows538))
    (hc : (q.map Prod.snd).Perm (cols538++cols538))
    (hd : ∀ k ∈ requiredD538, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS538, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows538 cols538 requiredD538 requiredS538
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem538_eq] at model
  exact MomentData.excluded538 ds ss model
def rows539 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols539 : List Int := [0,1,2,5,11,12,13,14,15,16,17,18,19,28,29]
def requiredD539 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS539 : List Int := [14,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem539_eq : pairedProblem rows539 cols539 requiredD539 requiredS539 =
    MomentData.problem539 := by rfl
theorem leaf539 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows539++rows539))
    (hc : (q.map Prod.snd).Perm (cols539++cols539))
    (hd : ∀ k ∈ requiredD539, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS539, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows539 cols539 requiredD539 requiredS539
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem539_eq] at model
  exact MomentData.excluded539 ds ss model
def rows540 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols540 : List Int := [0,1,2,5,11,12,13,14,15,16,17,18,19,28,29]
def requiredD540 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS540 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem540_eq : pairedProblem rows540 cols540 requiredD540 requiredS540 =
    MomentData.problem540 := by rfl
theorem leaf540 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows540++rows540))
    (hc : (q.map Prod.snd).Perm (cols540++cols540))
    (hd : ∀ k ∈ requiredD540, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS540, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows540 cols540 requiredD540 requiredS540
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem540_eq] at model
  exact MomentData.excluded540 ds ss model
def rows541 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,29]
def cols541 : List Int := [0,1,2,5,11,12,13,14,15,16,17,18,19,28,29]
def requiredD541 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,18]
def requiredS541 : List Int := [14,25,26,27,28,29,30,31,32,33,34,35,36,37,48]
theorem problem541_eq : pairedProblem rows541 cols541 requiredD541 requiredS541 =
    MomentData.problem541 := by rfl
theorem leaf541 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows541++rows541))
    (hc : (q.map Prod.snd).Perm (cols541++cols541))
    (hd : ∀ k ∈ requiredD541, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS541, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows541 cols541 requiredD541 requiredS541
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem541_eq] at model
  exact MomentData.excluded541 ds ss model
def rows542 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols542 : List Int := [0,1,2,3,6,12,13,14,15,16,17,18,19,20,29]
def requiredD542 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS542 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem542_eq : pairedProblem rows542 cols542 requiredD542 requiredS542 =
    MomentData.problem542 := by rfl
theorem leaf542 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows542++rows542))
    (hc : (q.map Prod.snd).Perm (cols542++cols542))
    (hd : ∀ k ∈ requiredD542, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS542, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows542 cols542 requiredD542 requiredS542
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem542_eq] at model
  exact MomentData.excluded542 ds ss model
def rows543 : List Int := [0,1,2,3,4,13,14,15,16,17,18,19,20,21,22]
def cols543 : List Int := [0,1,2,3,6,12,13,14,15,16,17,18,19,20,29]
def requiredD543 : List Int := [-16,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS543 : List Int := [16,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem543_eq : pairedProblem rows543 cols543 requiredD543 requiredS543 =
    MomentData.problem543 := by rfl
theorem leaf543 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows543++rows543))
    (hc : (q.map Prod.snd).Perm (cols543++cols543))
    (hd : ∀ k ∈ requiredD543, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS543, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows543 cols543 requiredD543 requiredS543
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem543_eq] at model
  exact MomentData.excluded543 ds ss model
def rows544 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols544 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD544 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS544 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem544_eq : pairedProblem rows544 cols544 requiredD544 requiredS544 =
    MomentData.problem544 := by rfl
theorem leaf544 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows544++rows544))
    (hc : (q.map Prod.snd).Perm (cols544++cols544))
    (hd : ∀ k ∈ requiredD544, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS544, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows544 cols544 requiredD544 requiredS544
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem544_eq] at model
  exact MomentData.excluded544 ds ss model
def rows545 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols545 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD545 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS545 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem545_eq : pairedProblem rows545 cols545 requiredD545 requiredS545 =
    MomentData.problem545 := by rfl
theorem leaf545 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows545++rows545))
    (hc : (q.map Prod.snd).Perm (cols545++cols545))
    (hd : ∀ k ∈ requiredD545, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS545, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows545 cols545 requiredD545 requiredS545
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem545_eq] at model
  exact MomentData.excluded545 ds ss model
def rows546 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols546 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD546 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS546 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,41]
theorem problem546_eq : pairedProblem rows546 cols546 requiredD546 requiredS546 =
    MomentData.problem546 := by rfl
theorem leaf546 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows546++rows546))
    (hc : (q.map Prod.snd).Perm (cols546++cols546))
    (hd : ∀ k ∈ requiredD546, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS546, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows546 cols546 requiredD546 requiredS546
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem546_eq] at model
  exact MomentData.excluded546 ds ss model
def rows547 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols547 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD547 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS547 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem547_eq : pairedProblem rows547 cols547 requiredD547 requiredS547 =
    MomentData.problem547 := by rfl
theorem leaf547 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows547++rows547))
    (hc : (q.map Prod.snd).Perm (cols547++cols547))
    (hd : ∀ k ∈ requiredD547, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS547, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows547 cols547 requiredD547 requiredS547
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem547_eq] at model
  exact MomentData.excluded547 ds ss model
def rows548 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols548 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD548 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS548 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem548_eq : pairedProblem rows548 cols548 requiredD548 requiredS548 =
    MomentData.problem548 := by rfl
theorem leaf548 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows548++rows548))
    (hc : (q.map Prod.snd).Perm (cols548++cols548))
    (hd : ∀ k ∈ requiredD548, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS548, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows548 cols548 requiredD548 requiredS548
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem548_eq] at model
  exact MomentData.excluded548 ds ss model
def rows549 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols549 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD549 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS549 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem549_eq : pairedProblem rows549 cols549 requiredD549 requiredS549 =
    MomentData.problem549 := by rfl
theorem leaf549 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows549++rows549))
    (hc : (q.map Prod.snd).Perm (cols549++cols549))
    (hd : ∀ k ∈ requiredD549, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS549, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows549 cols549 requiredD549 requiredS549
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem549_eq] at model
  exact MomentData.excluded549 ds ss model
def rows550 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols550 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD550 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS550 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem550_eq : pairedProblem rows550 cols550 requiredD550 requiredS550 =
    MomentData.problem550 := by rfl
theorem leaf550 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows550++rows550))
    (hc : (q.map Prod.snd).Perm (cols550++cols550))
    (hd : ∀ k ∈ requiredD550, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS550, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows550 cols550 requiredD550 requiredS550
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem550_eq] at model
  exact MomentData.excluded550 ds ss model
def rows551 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols551 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD551 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS551 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem551_eq : pairedProblem rows551 cols551 requiredD551 requiredS551 =
    MomentData.problem551 := by rfl
theorem leaf551 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows551++rows551))
    (hc : (q.map Prod.snd).Perm (cols551++cols551))
    (hd : ∀ k ∈ requiredD551, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS551, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows551 cols551 requiredD551 requiredS551
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem551_eq] at model
  exact MomentData.excluded551 ds ss model
def rows552 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols552 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD552 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS552 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem552_eq : pairedProblem rows552 cols552 requiredD552 requiredS552 =
    MomentData.problem552 := by rfl
theorem leaf552 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows552++rows552))
    (hc : (q.map Prod.snd).Perm (cols552++cols552))
    (hd : ∀ k ∈ requiredD552, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS552, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows552 cols552 requiredD552 requiredS552
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem552_eq] at model
  exact MomentData.excluded552 ds ss model
def rows553 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols553 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD553 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS553 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem553_eq : pairedProblem rows553 cols553 requiredD553 requiredS553 =
    MomentData.problem553 := by rfl
theorem leaf553 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows553++rows553))
    (hc : (q.map Prod.snd).Perm (cols553++cols553))
    (hd : ∀ k ∈ requiredD553, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS553, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows553 cols553 requiredD553 requiredS553
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem553_eq] at model
  exact MomentData.excluded553 ds ss model
def rows554 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols554 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD554 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS554 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem554_eq : pairedProblem rows554 cols554 requiredD554 requiredS554 =
    MomentData.problem554 := by rfl
theorem leaf554 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows554++rows554))
    (hc : (q.map Prod.snd).Perm (cols554++cols554))
    (hd : ∀ k ∈ requiredD554, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS554, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows554 cols554 requiredD554 requiredS554
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem554_eq] at model
  exact MomentData.excluded554 ds ss model
def rows555 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols555 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD555 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS555 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem555_eq : pairedProblem rows555 cols555 requiredD555 requiredS555 =
    MomentData.problem555 := by rfl
theorem leaf555 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows555++rows555))
    (hc : (q.map Prod.snd).Perm (cols555++cols555))
    (hd : ∀ k ∈ requiredD555, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS555, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows555 cols555 requiredD555 requiredS555
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem555_eq] at model
  exact MomentData.excluded555 ds ss model
def rows556 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def cols556 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD556 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS556 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,47]
theorem problem556_eq : pairedProblem rows556 cols556 requiredD556 requiredS556 =
    MomentData.problem556 := by rfl
theorem leaf556 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows556++rows556))
    (hc : (q.map Prod.snd).Perm (cols556++cols556))
    (hd : ∀ k ∈ requiredD556, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS556, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows556 cols556 requiredD556 requiredS556
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem556_eq] at model
  exact MomentData.excluded556 ds ss model
def rows557 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def cols557 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD557 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS557 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,47]
theorem problem557_eq : pairedProblem rows557 cols557 requiredD557 requiredS557 =
    MomentData.problem557 := by rfl
theorem leaf557 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows557++rows557))
    (hc : (q.map Prod.snd).Perm (cols557++cols557))
    (hd : ∀ k ∈ requiredD557, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS557, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows557 cols557 requiredD557 requiredS557
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem557_eq] at model
  exact MomentData.excluded557 ds ss model
def rows558 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def cols558 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD558 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS558 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem558_eq : pairedProblem rows558 cols558 requiredD558 requiredS558 =
    MomentData.problem558 := by rfl
theorem leaf558 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows558++rows558))
    (hc : (q.map Prod.snd).Perm (cols558++cols558))
    (hd : ∀ k ∈ requiredD558, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS558, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows558 cols558 requiredD558 requiredS558
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem558_eq] at model
  exact MomentData.excluded558 ds ss model
def rows559 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def cols559 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD559 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS559 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem559_eq : pairedProblem rows559 cols559 requiredD559 requiredS559 =
    MomentData.problem559 := by rfl
theorem leaf559 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows559++rows559))
    (hc : (q.map Prod.snd).Perm (cols559++cols559))
    (hd : ∀ k ∈ requiredD559, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS559, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows559 cols559 requiredD559 requiredS559
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem559_eq] at model
  exact MomentData.excluded559 ds ss model
def rows560 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def cols560 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def requiredD560 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS560 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,49]
theorem problem560_eq : pairedProblem rows560 cols560 requiredD560 requiredS560 =
    MomentData.problem560 := by rfl
theorem leaf560 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows560++rows560))
    (hc : (q.map Prod.snd).Perm (cols560++cols560))
    (hd : ∀ k ∈ requiredD560, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS560, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows560 cols560 requiredD560 requiredS560
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem560_eq] at model
  exact MomentData.excluded560 ds ss model
def rows561 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def cols561 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def requiredD561 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS561 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,49]
theorem problem561_eq : pairedProblem rows561 cols561 requiredD561 requiredS561 =
    MomentData.problem561 := by rfl
theorem leaf561 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows561++rows561))
    (hc : (q.map Prod.snd).Perm (cols561++cols561))
    (hd : ∀ k ∈ requiredD561, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS561, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows561 cols561 requiredD561 requiredS561
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem561_eq] at model
  exact MomentData.excluded561 ds ss model
def rows562 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def cols562 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def requiredD562 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS562 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,49]
theorem problem562_eq : pairedProblem rows562 cols562 requiredD562 requiredS562 =
    MomentData.problem562 := by rfl
theorem leaf562 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows562++rows562))
    (hc : (q.map Prod.snd).Perm (cols562++cols562))
    (hd : ∀ k ∈ requiredD562, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS562, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows562 cols562 requiredD562 requiredS562
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem562_eq] at model
  exact MomentData.excluded562 ds ss model
def rows563 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def cols563 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,29]
def requiredD563 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS563 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem563_eq : pairedProblem rows563 cols563 requiredD563 requiredS563 =
    MomentData.problem563 := by rfl
theorem leaf563 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows563++rows563))
    (hc : (q.map Prod.snd).Perm (cols563++cols563))
    (hd : ∀ k ∈ requiredD563, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS563, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows563 cols563 requiredD563 requiredS563
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem563_eq] at model
  exact MomentData.excluded563 ds ss model
def rows564 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,21]
def cols564 : List Int := [0,1,2,3,4,12,13,14,15,16,17,18,19,20,21]
def requiredD564 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS564 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem564_eq : pairedProblem rows564 cols564 requiredD564 requiredS564 =
    MomentData.problem564 := by rfl
theorem leaf564 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows564++rows564))
    (hc : (q.map Prod.snd).Perm (cols564++cols564))
    (hd : ∀ k ∈ requiredD564, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS564, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows564 cols564 requiredD564 requiredS564
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem564_eq] at model
  exact MomentData.excluded564 ds ss model
def rows565 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def cols565 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def requiredD565 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS565 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,40]
theorem problem565_eq : pairedProblem rows565 cols565 requiredD565 requiredS565 =
    MomentData.problem565 := by rfl
theorem leaf565 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows565++rows565))
    (hc : (q.map Prod.snd).Perm (cols565++cols565))
    (hd : ∀ k ∈ requiredD565, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS565, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows565 cols565 requiredD565 requiredS565
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem565_eq] at model
  exact MomentData.excluded565 ds ss model
def rows566 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def cols566 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def requiredD566 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS566 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,42]
theorem problem566_eq : pairedProblem rows566 cols566 requiredD566 requiredS566 =
    MomentData.problem566 := by rfl
theorem leaf566 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows566++rows566))
    (hc : (q.map Prod.snd).Perm (cols566++cols566))
    (hd : ∀ k ∈ requiredD566, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS566, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows566 cols566 requiredD566 requiredS566
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem566_eq] at model
  exact MomentData.excluded566 ds ss model
def rows567 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols567 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD567 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS567 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,44]
theorem problem567_eq : pairedProblem rows567 cols567 requiredD567 requiredS567 =
    MomentData.problem567 := by rfl
theorem leaf567 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows567++rows567))
    (hc : (q.map Prod.snd).Perm (cols567++cols567))
    (hd : ∀ k ∈ requiredD567, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS567, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows567 cols567 requiredD567 requiredS567
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem567_eq] at model
  exact MomentData.excluded567 ds ss model
def rows568 : List Int := [0,1,2,9,10,11,12,13,14,15,16,17,18,28,29]
def cols568 : List Int := [0,1,2,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD568 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS568 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,46]
theorem problem568_eq : pairedProblem rows568 cols568 requiredD568 requiredS568 =
    MomentData.problem568 := by rfl
theorem leaf568 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows568++rows568))
    (hc : (q.map Prod.snd).Perm (cols568++cols568))
    (hd : ∀ k ∈ requiredD568, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS568, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows568 cols568 requiredD568 requiredS568
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem568_eq] at model
  exact MomentData.excluded568 ds ss model
def rows569 : List Int := [0,1,2,3,10,11,12,13,14,15,16,17,18,19,29]
def cols569 : List Int := [0,1,2,3,10,11,12,13,14,15,16,17,18,19,29]
def requiredD569 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS569 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,48]
theorem problem569_eq : pairedProblem rows569 cols569 requiredD569 requiredS569 =
    MomentData.problem569 := by rfl
theorem leaf569 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows569++rows569))
    (hc : (q.map Prod.snd).Perm (cols569++cols569))
    (hd : ∀ k ∈ requiredD569, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS569, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows569 cols569 requiredD569 requiredS569
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem569_eq] at model
  exact MomentData.excluded569 ds ss model
def rows570 : List Int := [0,3,6,9,12,15,18,19,21,22,24,25,27,28,29]
def cols570 : List Int := [0,3,6,9,12,15,18,19,21,22,24,25,27,28,29]
def requiredD570 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS570 : List Int := [3,6,9,12,15,18,21,24,27,28,30,33,36,39,42]
theorem problem570_eq : pairedProblem rows570 cols570 requiredD570 requiredS570 =
    MomentData.problem570 := by rfl
theorem leaf570 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows570++rows570))
    (hc : (q.map Prod.snd).Perm (cols570++cols570))
    (hd : ∀ k ∈ requiredD570, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS570, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows570 cols570 requiredD570 requiredS570
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem570_eq] at model
  exact MomentData.excluded570 ds ss model
def rows571 : List Int := [0,1,4,7,10,13,16,19,20,22,23,25,26,28,29]
def cols571 : List Int := [0,1,4,7,10,13,16,19,20,22,23,25,26,28,29]
def requiredD571 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS571 : List Int := [5,8,11,14,17,20,23,26,29,30,32,35,38,41,44]
theorem problem571_eq : pairedProblem rows571 cols571 requiredD571 requiredS571 =
    MomentData.problem571 := by rfl
theorem leaf571 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows571++rows571))
    (hc : (q.map Prod.snd).Perm (cols571++cols571))
    (hd : ∀ k ∈ requiredD571, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS571, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows571 cols571 requiredD571 requiredS571
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem571_eq] at model
  exact MomentData.excluded571 ds ss model
def rows572 : List Int := [0,1,2,5,8,11,14,17,20,21,23,24,26,27,29]
def cols572 : List Int := [0,1,2,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD572 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS572 : List Int := [7,10,13,16,19,22,25,28,31,32,34,37,40,43,46]
theorem problem572_eq : pairedProblem rows572 cols572 requiredD572 requiredS572 =
    MomentData.problem572 := by rfl
theorem leaf572 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows572++rows572))
    (hc : (q.map Prod.snd).Perm (cols572++cols572))
    (hd : ∀ k ∈ requiredD572, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS572, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows572 cols572 requiredD572 requiredS572
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem572_eq] at model
  exact MomentData.excluded572 ds ss model
def rows573 : List Int := [0,1,2,3,6,9,12,15,18,21,22,24,25,27,28]
def cols573 : List Int := [0,1,2,3,6,9,12,15,18,21,22,24,25,27,28]
def requiredD573 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS573 : List Int := [9,12,15,18,21,24,27,30,33,34,36,39,42,45,48]
theorem problem573_eq : pairedProblem rows573 cols573 requiredD573 requiredS573 =
    MomentData.problem573 := by rfl
theorem leaf573 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows573++rows573))
    (hc : (q.map Prod.snd).Perm (cols573++cols573))
    (hd : ∀ k ∈ requiredD573, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS573, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows573 cols573 requiredD573 requiredS573
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem573_eq] at model
  exact MomentData.excluded573 ds ss model
def rows574 : List Int := [1,2,5,8,11,14,17,20,21,23,24,26,27,28,29]
def cols574 : List Int := [1,2,5,8,11,14,17,20,21,23,24,26,27,28,29]
def requiredD574 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS574 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43]
theorem problem574_eq : pairedProblem rows574 cols574 requiredD574 requiredS574 =
    MomentData.problem574 := by rfl
theorem leaf574 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows574++rows574))
    (hc : (q.map Prod.snd).Perm (cols574++cols574))
    (hd : ∀ k ∈ requiredD574, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS574, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows574 cols574 requiredD574 requiredS574
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem574_eq] at model
  exact MomentData.excluded574 ds ss model
def rows575 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols575 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD575 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS575 : List Int := [6,9,12,15,18,21,24,27,30,31,33,36,39,42,45]
theorem problem575_eq : pairedProblem rows575 cols575 requiredD575 requiredS575 =
    MomentData.problem575 := by rfl
theorem leaf575 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows575++rows575))
    (hc : (q.map Prod.snd).Perm (cols575++cols575))
    (hd : ∀ k ∈ requiredD575, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS575, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows575 cols575 requiredD575 requiredS575
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem575_eq] at model
  exact MomentData.excluded575 ds ss model
def rows576 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols576 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD576 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS576 : List Int := [9,12,15,18,21,24,27,30,31,33,36,39,42,45]
theorem problem576_eq : pairedProblem rows576 cols576 requiredD576 requiredS576 =
    MomentData.problem576 := by rfl
theorem leaf576 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows576++rows576))
    (hc : (q.map Prod.snd).Perm (cols576++cols576))
    (hd : ∀ k ∈ requiredD576, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS576, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows576 cols576 requiredD576 requiredS576
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem576_eq] at model
  exact MomentData.excluded576 ds ss model
def rows577 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols577 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD577 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS577 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem577_eq : pairedProblem rows577 cols577 requiredD577 requiredS577 =
    MomentData.problem577 := by rfl
theorem leaf577 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows577++rows577))
    (hc : (q.map Prod.snd).Perm (cols577++cols577))
    (hd : ∀ k ∈ requiredD577, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS577, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows577 cols577 requiredD577 requiredS577
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem577_eq] at model
  exact MomentData.excluded577 ds ss model
def rows578 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols578 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD578 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS578 : List Int := [6,9,12,15,18,21,24,27,30,31,33,36,39,42]
theorem problem578_eq : pairedProblem rows578 cols578 requiredD578 requiredS578 =
    MomentData.problem578 := by rfl
theorem leaf578 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows578++rows578))
    (hc : (q.map Prod.snd).Perm (cols578++cols578))
    (hd : ∀ k ∈ requiredD578, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS578, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows578 cols578 requiredD578 requiredS578
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem578_eq] at model
  exact MomentData.excluded578 ds ss model
def rows579 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols579 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD579 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS579 : List Int := [8,11,14,17,20,23,26,29,32,33,35,38,41,44,47]
theorem problem579_eq : pairedProblem rows579 cols579 requiredD579 requiredS579 =
    MomentData.problem579 := by rfl
theorem leaf579 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows579++rows579))
    (hc : (q.map Prod.snd).Perm (cols579++cols579))
    (hd : ∀ k ∈ requiredD579, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS579, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows579 cols579 requiredD579 requiredS579
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem579_eq] at model
  exact MomentData.excluded579 ds ss model
def rows580 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols580 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD580 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS580 : List Int := [11,14,17,20,23,26,29,32,33,35,38,41,44,47]
theorem problem580_eq : pairedProblem rows580 cols580 requiredD580 requiredS580 =
    MomentData.problem580 := by rfl
theorem leaf580 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows580++rows580))
    (hc : (q.map Prod.snd).Perm (cols580++cols580))
    (hd : ∀ k ∈ requiredD580, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS580, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows580 cols580 requiredD580 requiredS580
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem580_eq] at model
  exact MomentData.excluded580 ds ss model
def rows581 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols581 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD581 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS581 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem581_eq : pairedProblem rows581 cols581 requiredD581 requiredS581 =
    MomentData.problem581 := by rfl
theorem leaf581 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows581++rows581))
    (hc : (q.map Prod.snd).Perm (cols581++cols581))
    (hd : ∀ k ∈ requiredD581, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS581, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows581 cols581 requiredD581 requiredS581
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem581_eq] at model
  exact MomentData.excluded581 ds ss model
def rows582 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols582 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD582 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS582 : List Int := [8,11,14,17,20,23,26,29,32,33,35,38,41,44]
theorem problem582_eq : pairedProblem rows582 cols582 requiredD582 requiredS582 =
    MomentData.problem582 := by rfl
theorem leaf582 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows582++rows582))
    (hc : (q.map Prod.snd).Perm (cols582++cols582))
    (hd : ∀ k ∈ requiredD582, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS582, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows582 cols582 requiredD582 requiredS582
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem582_eq] at model
  exact MomentData.excluded582 ds ss model
def rows583 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols583 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD583 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS583 : List Int := [10,13,16,19,22,25,28,31,34,35,37,40,43,46,49]
theorem problem583_eq : pairedProblem rows583 cols583 requiredD583 requiredS583 =
    MomentData.problem583 := by rfl
theorem leaf583 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows583++rows583))
    (hc : (q.map Prod.snd).Perm (cols583++cols583))
    (hd : ∀ k ∈ requiredD583, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS583, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows583 cols583 requiredD583 requiredS583
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem583_eq] at model
  exact MomentData.excluded583 ds ss model
def rows584 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols584 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD584 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS584 : List Int := [13,16,19,22,25,28,31,34,35,37,40,43,46,49]
theorem problem584_eq : pairedProblem rows584 cols584 requiredD584 requiredS584 =
    MomentData.problem584 := by rfl
theorem leaf584 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows584++rows584))
    (hc : (q.map Prod.snd).Perm (cols584++cols584))
    (hd : ∀ k ∈ requiredD584, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS584, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows584 cols584 requiredD584 requiredS584
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem584_eq] at model
  exact MomentData.excluded584 ds ss model
def rows585 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols585 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD585 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS585 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem585_eq : pairedProblem rows585 cols585 requiredD585 requiredS585 =
    MomentData.problem585 := by rfl
theorem leaf585 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows585++rows585))
    (hc : (q.map Prod.snd).Perm (cols585++cols585))
    (hd : ∀ k ∈ requiredD585, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS585, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows585 cols585 requiredD585 requiredS585
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem585_eq] at model
  exact MomentData.excluded585 ds ss model
def rows586 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols586 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD586 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS586 : List Int := [10,13,16,19,22,25,28,31,34,35,37,40,43,46]
theorem problem586_eq : pairedProblem rows586 cols586 requiredD586 requiredS586 =
    MomentData.problem586 := by rfl
theorem leaf586 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows586++rows586))
    (hc : (q.map Prod.snd).Perm (cols586++cols586))
    (hd : ∀ k ∈ requiredD586, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS586, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows586 cols586 requiredD586 requiredS586
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem586_eq] at model
  exact MomentData.excluded586 ds ss model
def rows587 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols587 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def requiredD587 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS587 : List Int := [12,15,18,21,24,27,30,33,36,37,39,42,45,48,51]
theorem problem587_eq : pairedProblem rows587 cols587 requiredD587 requiredS587 =
    MomentData.problem587 := by rfl
theorem leaf587 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows587++rows587))
    (hc : (q.map Prod.snd).Perm (cols587++cols587))
    (hd : ∀ k ∈ requiredD587, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS587, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows587 cols587 requiredD587 requiredS587
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem587_eq] at model
  exact MomentData.excluded587 ds ss model
def rows588 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols588 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def requiredD588 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS588 : List Int := [15,18,21,24,27,30,33,36,37,39,42,45,48,51]
theorem problem588_eq : pairedProblem rows588 cols588 requiredD588 requiredS588 =
    MomentData.problem588 := by rfl
theorem leaf588 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows588++rows588))
    (hc : (q.map Prod.snd).Perm (cols588++cols588))
    (hd : ∀ k ∈ requiredD588, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS588, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows588 cols588 requiredD588 requiredS588
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem588_eq] at model
  exact MomentData.excluded588 ds ss model
def rows589 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols589 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def requiredD589 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS589 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem589_eq : pairedProblem rows589 cols589 requiredD589 requiredS589 =
    MomentData.problem589 := by rfl
theorem leaf589 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows589++rows589))
    (hc : (q.map Prod.snd).Perm (cols589++cols589))
    (hd : ∀ k ∈ requiredD589, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS589, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows589 cols589 requiredD589 requiredS589
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem589_eq] at model
  exact MomentData.excluded589 ds ss model
def rows590 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols590 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def requiredD590 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS590 : List Int := [12,15,18,21,24,27,30,33,36,37,39,42,45,48]
theorem problem590_eq : pairedProblem rows590 cols590 requiredD590 requiredS590 =
    MomentData.problem590 := by rfl
theorem leaf590 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows590++rows590))
    (hc : (q.map Prod.snd).Perm (cols590++cols590))
    (hd : ∀ k ∈ requiredD590, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS590, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows590 cols590 requiredD590 requiredS590
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem590_eq] at model
  exact MomentData.excluded590 ds ss model
def rows591 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols591 : List Int := [1,2,5,6,8,11,14,17,20,23,24,26,27,28,29]
def requiredD591 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS591 : List Int := [5,8,11,14,17,20,23,26,29,30,32,35,38,41,44]
theorem problem591_eq : pairedProblem rows591 cols591 requiredD591 requiredS591 =
    MomentData.problem591 := by rfl
theorem leaf591 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows591++rows591))
    (hc : (q.map Prod.snd).Perm (cols591++cols591))
    (hd : ∀ k ∈ requiredD591, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS591, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows591 cols591 requiredD591 requiredS591
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem591_eq] at model
  exact MomentData.excluded591 ds ss model
def rows592 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols592 : List Int := [1,2,5,6,8,11,14,17,20,23,24,26,27,28,29]
def requiredD592 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS592 : List Int := [8,11,14,17,20,22,23,26,29,30,32,35,38,41,44]
theorem problem592_eq : pairedProblem rows592 cols592 requiredD592 requiredS592 =
    MomentData.problem592 := by rfl
theorem leaf592 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows592++rows592))
    (hc : (q.map Prod.snd).Perm (cols592++cols592))
    (hd : ∀ k ∈ requiredD592, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS592, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows592 cols592 requiredD592 requiredS592
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem592_eq] at model
  exact MomentData.excluded592 ds ss model
def rows593 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols593 : List Int := [1,2,5,6,8,11,14,17,20,23,24,26,27,28,29]
def requiredD593 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS593 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem593_eq : pairedProblem rows593 cols593 requiredD593 requiredS593 =
    MomentData.problem593 := by rfl
theorem leaf593 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows593++rows593))
    (hc : (q.map Prod.snd).Perm (cols593++cols593))
    (hd : ∀ k ∈ requiredD593, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS593, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows593 cols593 requiredD593 requiredS593
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem593_eq] at model
  exact MomentData.excluded593 ds ss model
def rows594 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols594 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def requiredD594 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS594 : List Int := [7,10,13,16,19,22,25,28,31,32,34,37,40,43,46]
theorem problem594_eq : pairedProblem rows594 cols594 requiredD594 requiredS594 =
    MomentData.problem594 := by rfl
theorem leaf594 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows594++rows594))
    (hc : (q.map Prod.snd).Perm (cols594++cols594))
    (hd : ∀ k ∈ requiredD594, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS594, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows594 cols594 requiredD594 requiredS594
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem594_eq] at model
  exact MomentData.excluded594 ds ss model
def rows595 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols595 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def requiredD595 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS595 : List Int := [10,13,16,19,22,24,25,28,31,32,34,37,40,43,46]
theorem problem595_eq : pairedProblem rows595 cols595 requiredD595 requiredS595 =
    MomentData.problem595 := by rfl
theorem leaf595 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows595++rows595))
    (hc : (q.map Prod.snd).Perm (cols595++cols595))
    (hd : ∀ k ∈ requiredD595, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS595, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows595 cols595 requiredD595 requiredS595
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem595_eq] at model
  exact MomentData.excluded595 ds ss model
def rows596 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols596 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def requiredD596 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS596 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem596_eq : pairedProblem rows596 cols596 requiredD596 requiredS596 =
    MomentData.problem596 := by rfl
theorem leaf596 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows596++rows596))
    (hc : (q.map Prod.snd).Perm (cols596++cols596))
    (hd : ∀ k ∈ requiredD596, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS596, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows596 cols596 requiredD596 requiredS596
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem596_eq] at model
  exact MomentData.excluded596 ds ss model
def rows597 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols597 : List Int := [0,1,3,4,7,8,10,13,16,19,22,25,26,28,29]
def requiredD597 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS597 : List Int := [9,12,15,18,21,24,27,30,33,34,36,39,42,45,48]
theorem problem597_eq : pairedProblem rows597 cols597 requiredD597 requiredS597 =
    MomentData.problem597 := by rfl
theorem leaf597 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows597++rows597))
    (hc : (q.map Prod.snd).Perm (cols597++cols597))
    (hd : ∀ k ∈ requiredD597, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS597, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows597 cols597 requiredD597 requiredS597
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem597_eq] at model
  exact MomentData.excluded597 ds ss model
def rows598 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols598 : List Int := [0,1,3,4,7,8,10,13,16,19,22,25,26,28,29]
def requiredD598 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS598 : List Int := [12,15,18,21,24,26,27,30,33,34,36,39,42,45,48]
theorem problem598_eq : pairedProblem rows598 cols598 requiredD598 requiredS598 =
    MomentData.problem598 := by rfl
theorem leaf598 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows598++rows598))
    (hc : (q.map Prod.snd).Perm (cols598++cols598))
    (hd : ∀ k ∈ requiredD598, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS598, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows598 cols598 requiredD598 requiredS598
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem598_eq] at model
  exact MomentData.excluded598 ds ss model
def rows599 : List Int := [0,1,2,4,5,8,11,14,17,20,23,24,26,27,29]
def cols599 : List Int := [0,1,3,4,7,8,10,13,16,19,22,25,26,28,29]
def requiredD599 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS599 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem599_eq : pairedProblem rows599 cols599 requiredD599 requiredS599 =
    MomentData.problem599 := by rfl
theorem leaf599 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows599++rows599))
    (hc : (q.map Prod.snd).Perm (cols599++cols599))
    (hd : ∀ k ∈ requiredD599, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS599, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows599 cols599 requiredD599 requiredS599
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem599_eq] at model
  exact MomentData.excluded599 ds ss model
def rows600 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols600 : List Int := [0,1,2,4,5,8,9,11,14,17,20,23,26,27,29]
def requiredD600 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS600 : List Int := [11,14,17,20,23,26,29,32,35,36,38,41,44,47,50]
theorem problem600_eq : pairedProblem rows600 cols600 requiredD600 requiredS600 =
    MomentData.problem600 := by rfl
theorem leaf600 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows600++rows600))
    (hc : (q.map Prod.snd).Perm (cols600++cols600))
    (hd : ∀ k ∈ requiredD600, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS600, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows600 cols600 requiredD600 requiredS600
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem600_eq] at model
  exact MomentData.excluded600 ds ss model
def rows601 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols601 : List Int := [0,1,2,4,5,8,9,11,14,17,20,23,26,27,29]
def requiredD601 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS601 : List Int := [14,17,20,23,26,28,29,32,35,36,38,41,44,47,50]
theorem problem601_eq : pairedProblem rows601 cols601 requiredD601 requiredS601 =
    MomentData.problem601 := by rfl
theorem leaf601 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows601++rows601))
    (hc : (q.map Prod.snd).Perm (cols601++cols601))
    (hd : ∀ k ∈ requiredD601, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS601, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows601 cols601 requiredD601 requiredS601
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem601_eq] at model
  exact MomentData.excluded601 ds ss model
def rows602 : List Int := [0,1,2,3,5,6,9,12,15,18,21,24,25,27,28]
def cols602 : List Int := [0,1,2,4,5,8,9,11,14,17,20,23,26,27,29]
def requiredD602 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS602 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem602_eq : pairedProblem rows602 cols602 requiredD602 requiredS602 =
    MomentData.problem602 := by rfl
theorem leaf602 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows602++rows602))
    (hc : (q.map Prod.snd).Perm (cols602++cols602))
    (hd : ∀ k ∈ requiredD602, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS602, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows602 cols602 requiredD602 requiredS602
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem602_eq] at model
  exact MomentData.excluded602 ds ss model
def rows603 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def cols603 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD603 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS603 : List Int := [8,11,14,17,20,22,23,26,29,32,35,38,41,44,47]
theorem problem603_eq : pairedProblem rows603 cols603 requiredD603 requiredS603 =
    MomentData.problem603 := by rfl
theorem leaf603 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows603++rows603))
    (hc : (q.map Prod.snd).Perm (cols603++cols603))
    (hd : ∀ k ∈ requiredD603, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS603, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows603 cols603 requiredD603 requiredS603
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem603_eq] at model
  exact MomentData.excluded603 ds ss model
def rows604 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def cols604 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD604 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS604 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem604_eq : pairedProblem rows604 cols604 requiredD604 requiredS604 =
    MomentData.problem604 := by rfl
theorem leaf604 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows604++rows604))
    (hc : (q.map Prod.snd).Perm (cols604++cols604))
    (hd : ∀ k ∈ requiredD604, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS604, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows604 cols604 requiredD604 requiredS604
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem604_eq] at model
  exact MomentData.excluded604 ds ss model
def rows605 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def cols605 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD605 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS605 : List Int := [8,11,14,17,20,22,23,26,29,30,32,35,38,41,44]
theorem problem605_eq : pairedProblem rows605 cols605 requiredD605 requiredS605 =
    MomentData.problem605 := by rfl
theorem leaf605 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows605++rows605))
    (hc : (q.map Prod.snd).Perm (cols605++cols605))
    (hd : ∀ k ∈ requiredD605, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS605, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows605 cols605 requiredD605 requiredS605
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem605_eq] at model
  exact MomentData.excluded605 ds ss model
def rows606 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def cols606 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD606 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS606 : List Int := [10,13,16,19,22,24,25,28,31,34,37,40,43,46,49]
theorem problem606_eq : pairedProblem rows606 cols606 requiredD606 requiredS606 =
    MomentData.problem606 := by rfl
theorem leaf606 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows606++rows606))
    (hc : (q.map Prod.snd).Perm (cols606++cols606))
    (hd : ∀ k ∈ requiredD606, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS606, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows606 cols606 requiredD606 requiredS606
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem606_eq] at model
  exact MomentData.excluded606 ds ss model
def rows607 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def cols607 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD607 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS607 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem607_eq : pairedProblem rows607 cols607 requiredD607 requiredS607 =
    MomentData.problem607 := by rfl
theorem leaf607 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows607++rows607))
    (hc : (q.map Prod.snd).Perm (cols607++cols607))
    (hd : ∀ k ∈ requiredD607, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS607, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows607 cols607 requiredD607 requiredS607
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem607_eq] at model
  exact MomentData.excluded607 ds ss model
def rows608 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def cols608 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD608 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS608 : List Int := [10,13,16,19,22,24,25,28,31,32,34,37,40,43,46]
theorem problem608_eq : pairedProblem rows608 cols608 requiredD608 requiredS608 =
    MomentData.problem608 := by rfl
theorem leaf608 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows608++rows608))
    (hc : (q.map Prod.snd).Perm (cols608++cols608))
    (hd : ∀ k ∈ requiredD608, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS608, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows608 cols608 requiredD608 requiredS608
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem608_eq] at model
  exact MomentData.excluded608 ds ss model
def rows609 : List Int := [0,1,2,4,5,8,11,14,17,20,22,23,26,27,29]
def cols609 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD609 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS609 : List Int := [12,15,18,21,24,26,27,30,33,36,39,42,45,48,51]
theorem problem609_eq : pairedProblem rows609 cols609 requiredD609 requiredS609 =
    MomentData.problem609 := by rfl
theorem leaf609 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows609++rows609))
    (hc : (q.map Prod.snd).Perm (cols609++cols609))
    (hd : ∀ k ∈ requiredD609, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS609, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows609 cols609 requiredD609 requiredS609
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem609_eq] at model
  exact MomentData.excluded609 ds ss model
def rows610 : List Int := [0,1,2,4,5,8,11,14,17,20,22,23,26,27,29]
def cols610 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD610 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS610 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem610_eq : pairedProblem rows610 cols610 requiredD610 requiredS610 =
    MomentData.problem610 := by rfl
theorem leaf610 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows610++rows610))
    (hc : (q.map Prod.snd).Perm (cols610++cols610))
    (hd : ∀ k ∈ requiredD610, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS610, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows610 cols610 requiredD610 requiredS610
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem610_eq] at model
  exact MomentData.excluded610 ds ss model
def rows611 : List Int := [0,1,2,4,5,8,11,14,17,20,22,23,26,27,29]
def cols611 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD611 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS611 : List Int := [12,15,18,21,24,26,27,30,33,34,36,39,42,45,48]
theorem problem611_eq : pairedProblem rows611 cols611 requiredD611 requiredS611 =
    MomentData.problem611 := by rfl
theorem leaf611 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows611++rows611))
    (hc : (q.map Prod.snd).Perm (cols611++cols611))
    (hd : ∀ k ∈ requiredD611, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS611, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows611 cols611 requiredD611 requiredS611
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem611_eq] at model
  exact MomentData.excluded611 ds ss model
def rows612 : List Int := [0,1,2,3,5,6,9,12,15,18,21,23,24,27,28]
def cols612 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD612 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,5,7,10,13,16,19]
def requiredS612 : List Int := [14,17,20,23,26,28,29,32,35,38,41,44,47,50,53]
theorem problem612_eq : pairedProblem rows612 cols612 requiredD612 requiredS612 =
    MomentData.problem612 := by rfl
theorem leaf612 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows612++rows612))
    (hc : (q.map Prod.snd).Perm (cols612++cols612))
    (hd : ∀ k ∈ requiredD612, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS612, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows612 cols612 requiredD612 requiredS612
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem612_eq] at model
  exact MomentData.excluded612 ds ss model
def rows613 : List Int := [0,1,2,3,5,6,9,12,15,18,21,23,24,27,28]
def cols613 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD613 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS613 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem613_eq : pairedProblem rows613 cols613 requiredD613 requiredS613 =
    MomentData.problem613 := by rfl
theorem leaf613 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows613++rows613))
    (hc : (q.map Prod.snd).Perm (cols613++cols613))
    (hd : ∀ k ∈ requiredD613, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS613, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows613 cols613 requiredD613 requiredS613
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem613_eq] at model
  exact MomentData.excluded613 ds ss model
def rows614 : List Int := [0,1,2,3,5,6,9,12,15,18,21,23,24,27,28]
def cols614 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD614 : List Int := [-17,-14,-11,-8,-5,-3,-2,1,4,5,7,10,13,16,19]
def requiredS614 : List Int := [14,17,20,23,26,28,29,32,35,36,38,41,44,47,50]
theorem problem614_eq : pairedProblem rows614 cols614 requiredD614 requiredS614 =
    MomentData.problem614 := by rfl
theorem leaf614 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows614++rows614))
    (hc : (q.map Prod.snd).Perm (cols614++cols614))
    (hd : ∀ k ∈ requiredD614, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS614, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows614 cols614 requiredD614 requiredS614
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem614_eq] at model
  exact MomentData.excluded614 ds ss model
def rows615 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols615 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD615 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS615 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem615_eq : pairedProblem rows615 cols615 requiredD615 requiredS615 =
    MomentData.problem615 := by rfl
theorem leaf615 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows615++rows615))
    (hc : (q.map Prod.snd).Perm (cols615++cols615))
    (hd : ∀ k ∈ requiredD615, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS615, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows615 cols615 requiredD615 requiredS615
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem615_eq] at model
  exact MomentData.excluded615 ds ss model
def rows616 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols616 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD616 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS616 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem616_eq : pairedProblem rows616 cols616 requiredD616 requiredS616 =
    MomentData.problem616 := by rfl
theorem leaf616 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows616++rows616))
    (hc : (q.map Prod.snd).Perm (cols616++cols616))
    (hd : ∀ k ∈ requiredD616, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS616, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows616 cols616 requiredD616 requiredS616
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem616_eq] at model
  exact MomentData.excluded616 ds ss model
def rows617 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols617 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD617 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS617 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem617_eq : pairedProblem rows617 cols617 requiredD617 requiredS617 =
    MomentData.problem617 := by rfl
theorem leaf617 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows617++rows617))
    (hc : (q.map Prod.snd).Perm (cols617++cols617))
    (hd : ∀ k ∈ requiredD617, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS617, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows617 cols617 requiredD617 requiredS617
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem617_eq] at model
  exact MomentData.excluded617 ds ss model
def rows618 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols618 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD618 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS618 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43]
theorem problem618_eq : pairedProblem rows618 cols618 requiredD618 requiredS618 =
    MomentData.problem618 := by rfl
theorem leaf618 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows618++rows618))
    (hc : (q.map Prod.snd).Perm (cols618++cols618))
    (hd : ∀ k ∈ requiredD618, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS618, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows618 cols618 requiredD618 requiredS618
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem618_eq] at model
  exact MomentData.excluded618 ds ss model
def rows619 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols619 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD619 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS619 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45,48]
theorem problem619_eq : pairedProblem rows619 cols619 requiredD619 requiredS619 =
    MomentData.problem619 := by rfl
theorem leaf619 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows619++rows619))
    (hc : (q.map Prod.snd).Perm (cols619++cols619))
    (hd : ∀ k ∈ requiredD619, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS619, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows619 cols619 requiredD619 requiredS619
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem619_eq] at model
  exact MomentData.excluded619 ds ss model
def rows620 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols620 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD620 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS620 : List Int := [12,15,18,21,23,24,27,30,33,36,39,42,45,48]
theorem problem620_eq : pairedProblem rows620 cols620 requiredD620 requiredS620 =
    MomentData.problem620 := by rfl
theorem leaf620 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows620++rows620))
    (hc : (q.map Prod.snd).Perm (cols620++cols620))
    (hd : ∀ k ∈ requiredD620, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS620, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows620 cols620 requiredD620 requiredS620
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem620_eq] at model
  exact MomentData.excluded620 ds ss model
def rows621 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols621 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD621 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS621 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem621_eq : pairedProblem rows621 cols621 requiredD621 requiredS621 =
    MomentData.problem621 := by rfl
theorem leaf621 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows621++rows621))
    (hc : (q.map Prod.snd).Perm (cols621++cols621))
    (hd : ∀ k ∈ requiredD621, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS621, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows621 cols621 requiredD621 requiredS621
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem621_eq] at model
  exact MomentData.excluded621 ds ss model
def rows622 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols622 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD622 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS622 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem622_eq : pairedProblem rows622 cols622 requiredD622 requiredS622 =
    MomentData.problem622 := by rfl
theorem leaf622 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows622++rows622))
    (hc : (q.map Prod.snd).Perm (cols622++cols622))
    (hd : ∀ k ∈ requiredD622, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS622, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows622 cols622 requiredD622 requiredS622
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem622_eq] at model
  exact MomentData.excluded622 ds ss model
def rows623 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def cols623 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD623 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS623 : List Int := [11,14,17,20,23,25,26,29,32,35,38,41,44,47,50]
theorem problem623_eq : pairedProblem rows623 cols623 requiredD623 requiredS623 =
    MomentData.problem623 := by rfl
theorem leaf623 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows623++rows623))
    (hc : (q.map Prod.snd).Perm (cols623++cols623))
    (hd : ∀ k ∈ requiredD623, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS623, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows623 cols623 requiredD623 requiredS623
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem623_eq] at model
  exact MomentData.excluded623 ds ss model
def rows624 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def cols624 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD624 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS624 : List Int := [14,17,20,23,25,26,29,32,35,38,41,44,47,50]
theorem problem624_eq : pairedProblem rows624 cols624 requiredD624 requiredS624 =
    MomentData.problem624 := by rfl
theorem leaf624 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows624++rows624))
    (hc : (q.map Prod.snd).Perm (cols624++cols624))
    (hd : ∀ k ∈ requiredD624, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS624, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows624 cols624 requiredD624 requiredS624
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem624_eq] at model
  exact MomentData.excluded624 ds ss model
def rows625 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def cols625 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD625 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS625 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem625_eq : pairedProblem rows625 cols625 requiredD625 requiredS625 =
    MomentData.problem625 := by rfl
theorem leaf625 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows625++rows625))
    (hc : (q.map Prod.snd).Perm (cols625++cols625))
    (hd : ∀ k ∈ requiredD625, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS625, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows625 cols625 requiredD625 requiredS625
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem625_eq] at model
  exact MomentData.excluded625 ds ss model
def rows626 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def cols626 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,26,28,29]
def requiredD626 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS626 : List Int := [11,14,17,20,23,25,26,29,32,35,38,41,44,47]
theorem problem626_eq : pairedProblem rows626 cols626 requiredD626 requiredS626 =
    MomentData.problem626 := by rfl
theorem leaf626 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows626++rows626))
    (hc : (q.map Prod.snd).Perm (cols626++cols626))
    (hd : ∀ k ∈ requiredD626, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS626, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows626 cols626 requiredD626 requiredS626
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem626_eq] at model
  exact MomentData.excluded626 ds ss model
def rows627 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def cols627 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD627 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS627 : List Int := [13,16,19,22,25,27,28,31,34,37,40,43,46,49,52]
theorem problem627_eq : pairedProblem rows627 cols627 requiredD627 requiredS627 =
    MomentData.problem627 := by rfl
theorem leaf627 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows627++rows627))
    (hc : (q.map Prod.snd).Perm (cols627++cols627))
    (hd : ∀ k ∈ requiredD627, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS627, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows627 cols627 requiredD627 requiredS627
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem627_eq] at model
  exact MomentData.excluded627 ds ss model
def rows628 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def cols628 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD628 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS628 : List Int := [16,19,22,25,27,28,31,34,37,40,43,46,49,52]
theorem problem628_eq : pairedProblem rows628 cols628 requiredD628 requiredS628 =
    MomentData.problem628 := by rfl
theorem leaf628 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows628++rows628))
    (hc : (q.map Prod.snd).Perm (cols628++cols628))
    (hd : ∀ k ∈ requiredD628, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS628, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows628 cols628 requiredD628 requiredS628
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem628_eq] at model
  exact MomentData.excluded628 ds ss model
def rows629 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def cols629 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD629 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS629 : List Int := [13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem629_eq : pairedProblem rows629 cols629 requiredD629 requiredS629 =
    MomentData.problem629 := by rfl
theorem leaf629 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows629++rows629))
    (hc : (q.map Prod.snd).Perm (cols629++cols629))
    (hd : ∀ k ∈ requiredD629, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS629, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows629 cols629 requiredD629 requiredS629
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem629_eq] at model
  exact MomentData.excluded629 ds ss model
def rows630 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def cols630 : List Int := [0,1,2,4,5,7,8,11,14,17,20,23,26,27,29]
def requiredD630 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS630 : List Int := [13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem630_eq : pairedProblem rows630 cols630 requiredD630 requiredS630 =
    MomentData.problem630 := by rfl
theorem leaf630 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows630++rows630))
    (hc : (q.map Prod.snd).Perm (cols630++cols630))
    (hd : ∀ k ∈ requiredD630, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS630, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows630 cols630 requiredD630 requiredS630
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem630_eq] at model
  exact MomentData.excluded630 ds ss model
def rows631 : List Int := [0,1,2,3,5,6,8,9,12,15,18,21,24,27,28]
def cols631 : List Int := [0,1,2,3,5,6,8,9,12,15,18,21,24,27,28]
def requiredD631 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS631 : List Int := [15,18,21,24,27,29,30,33,36,39,42,45,48,51]
theorem problem631_eq : pairedProblem rows631 cols631 requiredD631 requiredS631 =
    MomentData.problem631 := by rfl
theorem leaf631 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows631++rows631))
    (hc : (q.map Prod.snd).Perm (cols631++cols631))
    (hd : ∀ k ∈ requiredD631, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS631, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows631 cols631 requiredD631 requiredS631
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem631_eq] at model
  exact MomentData.excluded631 ds ss model
def rows632 : List Int := [0,2,4,6,8,10,15,17,19,21,23,25,27,28,29]
def cols632 : List Int := [0,2,4,6,8,10,15,17,19,21,23,25,27,28,29]
def requiredD632 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS632 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem632_eq : pairedProblem rows632 cols632 requiredD632 requiredS632 =
    MomentData.problem632 := by rfl
theorem leaf632 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows632++rows632))
    (hc : (q.map Prod.snd).Perm (cols632++cols632))
    (hd : ∀ k ∈ requiredD632, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS632, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows632 cols632 requiredD632 requiredS632
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem632_eq] at model
  exact MomentData.excluded632 ds ss model
def rows633 : List Int := [0,1,2,4,6,8,10,12,17,19,21,23,25,27,29]
def cols633 : List Int := [0,1,2,4,6,8,10,12,17,19,21,23,25,27,29]
def requiredD633 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS633 : List Int := [17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem633_eq : pairedProblem rows633 cols633 requiredD633 requiredS633 =
    MomentData.problem633 := by rfl
theorem leaf633 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows633++rows633))
    (hc : (q.map Prod.snd).Perm (cols633++cols633))
    (hd : ∀ k ∈ requiredD633, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS633, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows633 cols633 requiredD633 requiredS633
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem633_eq] at model
  exact MomentData.excluded633 ds ss model
def rows634 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,27,28,29]
def cols634 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,27,28,29]
def requiredD634 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS634 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem634_eq : pairedProblem rows634 cols634 requiredD634 requiredS634 =
    MomentData.problem634 := by rfl
theorem leaf634 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows634++rows634))
    (hc : (q.map Prod.snd).Perm (cols634++cols634))
    (hd : ∀ k ∈ requiredD634, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS634, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows634 cols634 requiredD634 requiredS634
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem634_eq] at model
  exact MomentData.excluded634 ds ss model
def rows635 : List Int := [0,1,2,4,6,8,10,12,14,19,21,23,25,27,29]
def cols635 : List Int := [0,1,2,4,6,8,10,12,14,19,21,23,25,27,29]
def requiredD635 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS635 : List Int := [19,20,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem635_eq : pairedProblem rows635 cols635 requiredD635 requiredS635 =
    MomentData.problem635 := by rfl
theorem leaf635 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows635++rows635))
    (hc : (q.map Prod.snd).Perm (cols635++cols635))
    (hd : ∀ k ∈ requiredD635, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS635, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows635 cols635 requiredD635 requiredS635
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem635_eq] at model
  exact MomentData.excluded635 ds ss model
def rows636 : List Int := [1,2,4,5,7,8,11,14,17,20,23,26,27,28,29]
def cols636 : List Int := [1,2,4,5,7,8,11,14,17,20,23,26,27,28,29]
def requiredD636 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS636 : List Int := [10,13,16,19,22,24,25,28,31,34,37,40,43,46,49]
theorem problem636_eq : pairedProblem rows636 cols636 requiredD636 requiredS636 =
    MomentData.problem636 := by rfl
theorem leaf636 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows636++rows636))
    (hc : (q.map Prod.snd).Perm (cols636++cols636))
    (hd : ∀ k ∈ requiredD636, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS636, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows636 cols636 requiredD636 requiredS636
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem636_eq] at model
  exact MomentData.excluded636 ds ss model
def rows637 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,27,28,29]
def cols637 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,27,28,29]
def requiredD637 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS637 : List Int := [12,15,18,21,24,26,27,30,33,36,39,42,45,48,51]
theorem problem637_eq : pairedProblem rows637 cols637 requiredD637 requiredS637 =
    MomentData.problem637 := by rfl
theorem leaf637 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows637++rows637))
    (hc : (q.map Prod.snd).Perm (cols637++cols637))
    (hd : ∀ k ∈ requiredD637, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS637, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows637 cols637 requiredD637 requiredS637
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem637_eq] at model
  exact MomentData.excluded637 ds ss model
def rows638 : List Int := [0,1,3,4,6,7,9,10,13,16,19,22,25,28,29]
def cols638 : List Int := [0,1,3,4,6,7,9,10,13,16,19,22,25,28,29]
def requiredD638 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS638 : List Int := [14,17,20,23,26,28,29,32,35,38,41,44,47,50,53]
theorem problem638_eq : pairedProblem rows638 cols638 requiredD638 requiredS638 =
    MomentData.problem638 := by rfl
theorem leaf638 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows638++rows638))
    (hc : (q.map Prod.snd).Perm (cols638++cols638))
    (hd : ∀ k ∈ requiredD638, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS638, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows638 cols638 requiredD638 requiredS638
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem638_eq] at model
  exact MomentData.excluded638 ds ss model
def rows639 : List Int := [0,1,2,4,5,7,8,10,11,14,17,20,23,26,29]
def cols639 : List Int := [0,1,2,4,5,7,8,10,11,14,17,20,23,26,29]
def requiredD639 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS639 : List Int := [16,19,22,25,28,30,31,34,37,40,43,46,49,52,55]
theorem problem639_eq : pairedProblem rows639 cols639 requiredD639 requiredS639 =
    MomentData.problem639 := by rfl
theorem leaf639 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows639++rows639))
    (hc : (q.map Prod.snd).Perm (cols639++cols639))
    (hd : ∀ k ∈ requiredD639, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS639, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows639 cols639 requiredD639 requiredS639
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem639_eq] at model
  exact MomentData.excluded639 ds ss model
#print axioms leaf512
end Gardner.Kernel.MomentContexts
