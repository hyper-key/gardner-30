import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows640 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols640 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD640 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS640 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,44]
theorem problem640_eq : pairedProblem rows640 cols640 requiredD640 requiredS640 =
    MomentData.problem640 := by rfl
theorem leaf640 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows640++rows640))
    (hc : (q.map Prod.snd).Perm (cols640++cols640))
    (hd : ∀ k ∈ requiredD640, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS640, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows640 cols640 requiredD640 requiredS640
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem640_eq] at model
  exact MomentData.excluded640 ds ss model
def rows641 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols641 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD641 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS641 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem641_eq : pairedProblem rows641 cols641 requiredD641 requiredS641 =
    MomentData.problem641 := by rfl
theorem leaf641 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows641++rows641))
    (hc : (q.map Prod.snd).Perm (cols641++cols641))
    (hd : ∀ k ∈ requiredD641, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS641, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows641 cols641 requiredD641 requiredS641
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem641_eq] at model
  exact MomentData.excluded641 ds ss model
def rows642 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols642 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD642 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS642 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem642_eq : pairedProblem rows642 cols642 requiredD642 requiredS642 =
    MomentData.problem642 := by rfl
theorem leaf642 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows642++rows642))
    (hc : (q.map Prod.snd).Perm (cols642++cols642))
    (hd : ∀ k ∈ requiredD642, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS642, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows642 cols642 requiredD642 requiredS642
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem642_eq] at model
  exact MomentData.excluded642 ds ss model
def rows643 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols643 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD643 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS643 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem643_eq : pairedProblem rows643 cols643 requiredD643 requiredS643 =
    MomentData.problem643 := by rfl
theorem leaf643 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows643++rows643))
    (hc : (q.map Prod.snd).Perm (cols643++cols643))
    (hd : ∀ k ∈ requiredD643, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS643, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows643 cols643 requiredD643 requiredS643
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem643_eq] at model
  exact MomentData.excluded643 ds ss model
def rows644 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols644 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD644 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS644 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem644_eq : pairedProblem rows644 cols644 requiredD644 requiredS644 =
    MomentData.problem644 := by rfl
theorem leaf644 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows644++rows644))
    (hc : (q.map Prod.snd).Perm (cols644++cols644))
    (hd : ∀ k ∈ requiredD644, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS644, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows644 cols644 requiredD644 requiredS644
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem644_eq] at model
  exact MomentData.excluded644 ds ss model
def rows645 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,25,29]
def cols645 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD645 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS645 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,48]
theorem problem645_eq : pairedProblem rows645 cols645 requiredD645 requiredS645 =
    MomentData.problem645 := by rfl
theorem leaf645 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows645++rows645))
    (hc : (q.map Prod.snd).Perm (cols645++cols645))
    (hd : ∀ k ∈ requiredD645, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS645, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows645 cols645 requiredD645 requiredS645
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem645_eq] at model
  exact MomentData.excluded645 ds ss model
def rows646 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,25,29]
def cols646 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD646 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS646 : List Int := [12,24,25,26,27,28,29,30,31,32,33,34,35,36,48]
theorem problem646_eq : pairedProblem rows646 cols646 requiredD646 requiredS646 =
    MomentData.problem646 := by rfl
theorem leaf646 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows646++rows646))
    (hc : (q.map Prod.snd).Perm (cols646++cols646))
    (hd : ∀ k ∈ requiredD646, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS646, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows646 cols646 requiredD646 requiredS646
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem646_eq] at model
  exact MomentData.excluded646 ds ss model
def rows647 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,25,29]
def cols647 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD647 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS647 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem647_eq : pairedProblem rows647 cols647 requiredD647 requiredS647 =
    MomentData.problem647 := by rfl
theorem leaf647 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows647++rows647))
    (hc : (q.map Prod.snd).Perm (cols647++cols647))
    (hd : ∀ k ∈ requiredD647, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS647, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows647 cols647 requiredD647 requiredS647
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem647_eq] at model
  exact MomentData.excluded647 ds ss model
def rows648 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,26]
def cols648 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD648 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS648 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem648_eq : pairedProblem rows648 cols648 requiredD648 requiredS648 =
    MomentData.problem648 := by rfl
theorem leaf648 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows648++rows648))
    (hc : (q.map Prod.snd).Perm (cols648++cols648))
    (hd : ∀ k ∈ requiredD648, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS648, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows648 cols648 requiredD648 requiredS648
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem648_eq] at model
  exact MomentData.excluded648 ds ss model
def rows649 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols649 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,27,28,29]
def requiredD649 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS649 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem649_eq : pairedProblem rows649 cols649 requiredD649 requiredS649 =
    MomentData.problem649 := by rfl
theorem leaf649 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows649++rows649))
    (hc : (q.map Prod.snd).Perm (cols649++cols649))
    (hd : ∀ k ∈ requiredD649, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS649, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows649 cols649 requiredD649 requiredS649
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem649_eq] at model
  exact MomentData.excluded649 ds ss model
def rows650 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,28,29]
def cols650 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,28,29]
def requiredD650 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS650 : List Int := [12,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem650_eq : pairedProblem rows650 cols650 requiredD650 requiredS650 =
    MomentData.problem650 := by rfl
theorem leaf650 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows650++rows650))
    (hc : (q.map Prod.snd).Perm (cols650++cols650))
    (hd : ∀ k ∈ requiredD650, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS650, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows650 cols650 requiredD650 requiredS650
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem650_eq] at model
  exact MomentData.excluded650 ds ss model
def rows651 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,22,29]
def cols651 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,22,29]
def requiredD651 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS651 : List Int := [14,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem651_eq : pairedProblem rows651 cols651 requiredD651 requiredS651 =
    MomentData.problem651 := by rfl
theorem leaf651 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows651++rows651))
    (hc : (q.map Prod.snd).Perm (cols651++cols651))
    (hd : ∀ k ∈ requiredD651, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS651, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows651 cols651 requiredD651 requiredS651
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem651_eq] at model
  exact MomentData.excluded651 ds ss model
def rows652 : List Int := [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23]
def cols652 : List Int := [0,1,2,3,13,14,15,16,17,18,19,20,21,22,23]
def requiredD652 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS652 : List Int := [16,28,29,30,31,32,33,34,35,36,37,38,39,40,41]
theorem problem652_eq : pairedProblem rows652 cols652 requiredD652 requiredS652 =
    MomentData.problem652 := by rfl
theorem leaf652 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows652++rows652))
    (hc : (q.map Prod.snd).Perm (cols652++cols652))
    (hd : ∀ k ∈ requiredD652, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS652, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows652 cols652 requiredD652 requiredS652
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem652_eq] at model
  exact MomentData.excluded652 ds ss model
def rows653 : List Int := [8,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols653 : List Int := [8,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD653 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS653 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem653_eq : pairedProblem rows653 cols653 requiredD653 requiredS653 =
    MomentData.problem653 := by rfl
theorem leaf653 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows653++rows653))
    (hc : (q.map Prod.snd).Perm (cols653++cols653))
    (hd : ∀ k ∈ requiredD653, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS653, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows653 cols653 requiredD653 requiredS653
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem653_eq] at model
  exact MomentData.excluded653 ds ss model
def rows654 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols654 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD654 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS654 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem654_eq : pairedProblem rows654 cols654 requiredD654 requiredS654 =
    MomentData.problem654 := by rfl
theorem leaf654 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows654++rows654))
    (hc : (q.map Prod.snd).Perm (cols654++cols654))
    (hd : ∀ k ∈ requiredD654, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS654, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows654 cols654 requiredD654 requiredS654
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem654_eq] at model
  exact MomentData.excluded654 ds ss model
def rows655 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols655 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD655 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS655 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem655_eq : pairedProblem rows655 cols655 requiredD655 requiredS655 =
    MomentData.problem655 := by rfl
theorem leaf655 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows655++rows655))
    (hc : (q.map Prod.snd).Perm (cols655++cols655))
    (hd : ∀ k ∈ requiredD655, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS655, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows655 cols655 requiredD655 requiredS655
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem655_eq] at model
  exact MomentData.excluded655 ds ss model
def rows656 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols656 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD656 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS656 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem656_eq : pairedProblem rows656 cols656 requiredD656 requiredS656 =
    MomentData.problem656 := by rfl
theorem leaf656 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows656++rows656))
    (hc : (q.map Prod.snd).Perm (cols656++cols656))
    (hd : ∀ k ∈ requiredD656, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS656, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows656 cols656 requiredD656 requiredS656
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem656_eq] at model
  exact MomentData.excluded656 ds ss model
def rows657 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols657 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD657 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS657 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem657_eq : pairedProblem rows657 cols657 requiredD657 requiredS657 =
    MomentData.problem657 := by rfl
theorem leaf657 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows657++rows657))
    (hc : (q.map Prod.snd).Perm (cols657++cols657))
    (hd : ∀ k ∈ requiredD657, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS657, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows657 cols657 requiredD657 requiredS657
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem657_eq] at model
  exact MomentData.excluded657 ds ss model
def rows658 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols658 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD658 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS658 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem658_eq : pairedProblem rows658 cols658 requiredD658 requiredS658 =
    MomentData.problem658 := by rfl
theorem leaf658 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows658++rows658))
    (hc : (q.map Prod.snd).Perm (cols658++cols658))
    (hd : ∀ k ∈ requiredD658, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS658, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows658 cols658 requiredD658 requiredS658
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem658_eq] at model
  exact MomentData.excluded658 ds ss model
def rows659 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols659 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD659 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS659 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem659_eq : pairedProblem rows659 cols659 requiredD659 requiredS659 =
    MomentData.problem659 := by rfl
theorem leaf659 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows659++rows659))
    (hc : (q.map Prod.snd).Perm (cols659++cols659))
    (hd : ∀ k ∈ requiredD659, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS659, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows659 cols659 requiredD659 requiredS659
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem659_eq] at model
  exact MomentData.excluded659 ds ss model
def rows660 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols660 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD660 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS660 : List Int := [11,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem660_eq : pairedProblem rows660 cols660 requiredD660 requiredS660 =
    MomentData.problem660 := by rfl
theorem leaf660 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows660++rows660))
    (hc : (q.map Prod.snd).Perm (cols660++cols660))
    (hd : ∀ k ∈ requiredD660, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS660, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows660 cols660 requiredD660 requiredS660
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem660_eq] at model
  exact MomentData.excluded660 ds ss model
def rows661 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols661 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD661 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS661 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem661_eq : pairedProblem rows661 cols661 requiredD661 requiredS661 =
    MomentData.problem661 := by rfl
theorem leaf661 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows661++rows661))
    (hc : (q.map Prod.snd).Perm (cols661++cols661))
    (hd : ∀ k ∈ requiredD661, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS661, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows661 cols661 requiredD661 requiredS661
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem661_eq] at model
  exact MomentData.excluded661 ds ss model
def rows662 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols662 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD662 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS662 : List Int := [13,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem662_eq : pairedProblem rows662 cols662 requiredD662 requiredS662 =
    MomentData.problem662 := by rfl
theorem leaf662 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows662++rows662))
    (hc : (q.map Prod.snd).Perm (cols662++cols662))
    (hd : ∀ k ∈ requiredD662, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS662, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows662 cols662 requiredD662 requiredS662
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem662_eq] at model
  exact MomentData.excluded662 ds ss model
def rows663 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols663 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD663 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS663 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem663_eq : pairedProblem rows663 cols663 requiredD663 requiredS663 =
    MomentData.problem663 := by rfl
theorem leaf663 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows663++rows663))
    (hc : (q.map Prod.snd).Perm (cols663++cols663))
    (hd : ∀ k ∈ requiredD663, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS663, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows663 cols663 requiredD663 requiredS663
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem663_eq] at model
  exact MomentData.excluded663 ds ss model
def rows664 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols664 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD664 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS664 : List Int := [13,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem664_eq : pairedProblem rows664 cols664 requiredD664 requiredS664 =
    MomentData.problem664 := by rfl
theorem leaf664 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows664++rows664))
    (hc : (q.map Prod.snd).Perm (cols664++cols664))
    (hd : ∀ k ∈ requiredD664, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS664, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows664 cols664 requiredD664 requiredS664
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem664_eq] at model
  exact MomentData.excluded664 ds ss model
def rows665 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols665 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD665 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS665 : List Int := [13,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem665_eq : pairedProblem rows665 cols665 requiredD665 requiredS665 =
    MomentData.problem665 := by rfl
theorem leaf665 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows665++rows665))
    (hc : (q.map Prod.snd).Perm (cols665++cols665))
    (hd : ∀ k ∈ requiredD665, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS665, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows665 cols665 requiredD665 requiredS665
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem665_eq] at model
  exact MomentData.excluded665 ds ss model
def rows666 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols666 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def requiredD666 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS666 : List Int := [15,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem666_eq : pairedProblem rows666 cols666 requiredD666 requiredS666 =
    MomentData.problem666 := by rfl
theorem leaf666 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows666++rows666))
    (hc : (q.map Prod.snd).Perm (cols666++cols666))
    (hd : ∀ k ∈ requiredD666, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS666, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows666 cols666 requiredD666 requiredS666
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem666_eq] at model
  exact MomentData.excluded666 ds ss model
def rows667 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols667 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def requiredD667 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS667 : List Int := [27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem667_eq : pairedProblem rows667 cols667 requiredD667 requiredS667 =
    MomentData.problem667 := by rfl
theorem leaf667 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows667++rows667))
    (hc : (q.map Prod.snd).Perm (cols667++cols667))
    (hd : ∀ k ∈ requiredD667, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS667, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows667 cols667 requiredD667 requiredS667
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem667_eq] at model
  exact MomentData.excluded667 ds ss model
def rows668 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols668 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def requiredD668 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS668 : List Int := [15,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem668_eq : pairedProblem rows668 cols668 requiredD668 requiredS668 =
    MomentData.problem668 := by rfl
theorem leaf668 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows668++rows668))
    (hc : (q.map Prod.snd).Perm (cols668++cols668))
    (hd : ∀ k ∈ requiredD668, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS668, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows668 cols668 requiredD668 requiredS668
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem668_eq] at model
  exact MomentData.excluded668 ds ss model
def rows669 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols669 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def requiredD669 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS669 : List Int := [15,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem669_eq : pairedProblem rows669 cols669 requiredD669 requiredS669 =
    MomentData.problem669 := by rfl
theorem leaf669 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows669++rows669))
    (hc : (q.map Prod.snd).Perm (cols669++cols669))
    (hd : ∀ k ∈ requiredD669, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS669, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows669 cols669 requiredD669 requiredS669
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem669_eq] at model
  exact MomentData.excluded669 ds ss model
def rows670 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols670 : List Int := [3,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD670 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS670 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem670_eq : pairedProblem rows670 cols670 requiredD670 requiredS670 =
    MomentData.problem670 := by rfl
theorem leaf670 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows670++rows670))
    (hc : (q.map Prod.snd).Perm (cols670++cols670))
    (hd : ∀ k ∈ requiredD670, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS670, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows670 cols670 requiredD670 requiredS670
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem670_eq] at model
  exact MomentData.excluded670 ds ss model
def rows671 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols671 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD671 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS671 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem671_eq : pairedProblem rows671 cols671 requiredD671 requiredS671 =
    MomentData.problem671 := by rfl
theorem leaf671 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows671++rows671))
    (hc : (q.map Prod.snd).Perm (cols671++cols671))
    (hd : ∀ k ∈ requiredD671, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS671, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows671 cols671 requiredD671 requiredS671
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem671_eq] at model
  exact MomentData.excluded671 ds ss model
def rows672 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols672 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD672 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS672 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem672_eq : pairedProblem rows672 cols672 requiredD672 requiredS672 =
    MomentData.problem672 := by rfl
theorem leaf672 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows672++rows672))
    (hc : (q.map Prod.snd).Perm (cols672++cols672))
    (hd : ∀ k ∈ requiredD672, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS672, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows672 cols672 requiredD672 requiredS672
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem672_eq] at model
  exact MomentData.excluded672 ds ss model
def rows673 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols673 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD673 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS673 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem673_eq : pairedProblem rows673 cols673 requiredD673 requiredS673 =
    MomentData.problem673 := by rfl
theorem leaf673 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows673++rows673))
    (hc : (q.map Prod.snd).Perm (cols673++cols673))
    (hd : ∀ k ∈ requiredD673, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS673, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows673 cols673 requiredD673 requiredS673
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem673_eq] at model
  exact MomentData.excluded673 ds ss model
def rows674 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols674 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD674 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS674 : List Int := [12,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem674_eq : pairedProblem rows674 cols674 requiredD674 requiredS674 =
    MomentData.problem674 := by rfl
theorem leaf674 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows674++rows674))
    (hc : (q.map Prod.snd).Perm (cols674++cols674))
    (hd : ∀ k ∈ requiredD674, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS674, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows674 cols674 requiredD674 requiredS674
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem674_eq] at model
  exact MomentData.excluded674 ds ss model
def rows675 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols675 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD675 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS675 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem675_eq : pairedProblem rows675 cols675 requiredD675 requiredS675 =
    MomentData.problem675 := by rfl
theorem leaf675 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows675++rows675))
    (hc : (q.map Prod.snd).Perm (cols675++cols675))
    (hd : ∀ k ∈ requiredD675, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS675, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows675 cols675 requiredD675 requiredS675
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem675_eq] at model
  exact MomentData.excluded675 ds ss model
def rows676 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,29]
def cols676 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD676 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS676 : List Int := [12,24,25,26,27,28,29,30,31,32,33,34,35,36,48]
theorem problem676_eq : pairedProblem rows676 cols676 requiredD676 requiredS676 =
    MomentData.problem676 := by rfl
theorem leaf676 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows676++rows676))
    (hc : (q.map Prod.snd).Perm (cols676++cols676))
    (hd : ∀ k ∈ requiredD676, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS676, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows676 cols676 requiredD676 requiredS676
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem676_eq] at model
  exact MomentData.excluded676 ds ss model
def rows677 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols677 : List Int := [0,1,2,6,11,12,13,14,15,16,17,18,19,20,29]
def requiredD677 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS677 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem677_eq : pairedProblem rows677 cols677 requiredD677 requiredS677 =
    MomentData.problem677 := by rfl
theorem leaf677 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows677++rows677))
    (hc : (q.map Prod.snd).Perm (cols677++cols677))
    (hd : ∀ k ∈ requiredD677, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS677, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows677 cols677 requiredD677 requiredS677
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem677_eq] at model
  exact MomentData.excluded677 ds ss model
def rows678 : List Int := [0,1,2,3,12,13,14,15,16,17,18,19,20,21,22]
def cols678 : List Int := [0,1,2,6,11,12,13,14,15,16,17,18,19,20,29]
def requiredD678 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS678 : List Int := [14,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem678_eq : pairedProblem rows678 cols678 requiredD678 requiredS678 =
    MomentData.problem678 := by rfl
theorem leaf678 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows678++rows678))
    (hc : (q.map Prod.snd).Perm (cols678++cols678))
    (hd : ∀ k ∈ requiredD678, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS678, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows678 cols678 requiredD678 requiredS678
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem678_eq] at model
  exact MomentData.excluded678 ds ss model
def rows679 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols679 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD679 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS679 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem679_eq : pairedProblem rows679 cols679 requiredD679 requiredS679 =
    MomentData.problem679 := by rfl
theorem leaf679 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows679++rows679))
    (hc : (q.map Prod.snd).Perm (cols679++cols679))
    (hd : ∀ k ∈ requiredD679, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS679, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows679 cols679 requiredD679 requiredS679
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem679_eq] at model
  exact MomentData.excluded679 ds ss model
def rows680 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols680 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD680 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS680 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem680_eq : pairedProblem rows680 cols680 requiredD680 requiredS680 =
    MomentData.problem680 := by rfl
theorem leaf680 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows680++rows680))
    (hc : (q.map Prod.snd).Perm (cols680++cols680))
    (hd : ∀ k ∈ requiredD680, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS680, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows680 cols680 requiredD680 requiredS680
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem680_eq] at model
  exact MomentData.excluded680 ds ss model
def rows681 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols681 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD681 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS681 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,43]
theorem problem681_eq : pairedProblem rows681 cols681 requiredD681 requiredS681 =
    MomentData.problem681 := by rfl
theorem leaf681 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows681++rows681))
    (hc : (q.map Prod.snd).Perm (cols681++cols681))
    (hd : ∀ k ∈ requiredD681, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS681, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows681 cols681 requiredD681 requiredS681
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem681_eq] at model
  exact MomentData.excluded681 ds ss model
def rows682 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols682 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD682 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS682 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem682_eq : pairedProblem rows682 cols682 requiredD682 requiredS682 =
    MomentData.problem682 := by rfl
theorem leaf682 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows682++rows682))
    (hc : (q.map Prod.snd).Perm (cols682++cols682))
    (hd : ∀ k ∈ requiredD682, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS682, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows682 cols682 requiredD682 requiredS682
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem682_eq] at model
  exact MomentData.excluded682 ds ss model
def rows683 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols683 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD683 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS683 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem683_eq : pairedProblem rows683 cols683 requiredD683 requiredS683 =
    MomentData.problem683 := by rfl
theorem leaf683 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows683++rows683))
    (hc : (q.map Prod.snd).Perm (cols683++cols683))
    (hd : ∀ k ∈ requiredD683, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS683, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows683 cols683 requiredD683 requiredS683
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem683_eq] at model
  exact MomentData.excluded683 ds ss model
def rows684 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols684 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD684 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS684 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem684_eq : pairedProblem rows684 cols684 requiredD684 requiredS684 =
    MomentData.problem684 := by rfl
theorem leaf684 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows684++rows684))
    (hc : (q.map Prod.snd).Perm (cols684++cols684))
    (hd : ∀ k ∈ requiredD684, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS684, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows684 cols684 requiredD684 requiredS684
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem684_eq] at model
  exact MomentData.excluded684 ds ss model
def rows685 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols685 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD685 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS685 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem685_eq : pairedProblem rows685 cols685 requiredD685 requiredS685 =
    MomentData.problem685 := by rfl
theorem leaf685 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows685++rows685))
    (hc : (q.map Prod.snd).Perm (cols685++cols685))
    (hd : ∀ k ∈ requiredD685, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS685, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows685 cols685 requiredD685 requiredS685
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem685_eq] at model
  exact MomentData.excluded685 ds ss model
def rows686 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols686 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD686 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS686 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem686_eq : pairedProblem rows686 cols686 requiredD686 requiredS686 =
    MomentData.problem686 := by rfl
theorem leaf686 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows686++rows686))
    (hc : (q.map Prod.snd).Perm (cols686++cols686))
    (hd : ∀ k ∈ requiredD686, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS686, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows686 cols686 requiredD686 requiredS686
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem686_eq] at model
  exact MomentData.excluded686 ds ss model
def rows687 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols687 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD687 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS687 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem687_eq : pairedProblem rows687 cols687 requiredD687 requiredS687 =
    MomentData.problem687 := by rfl
theorem leaf687 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows687++rows687))
    (hc : (q.map Prod.snd).Perm (cols687++cols687))
    (hd : ∀ k ∈ requiredD687, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS687, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows687 cols687 requiredD687 requiredS687
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem687_eq] at model
  exact MomentData.excluded687 ds ss model
def rows688 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols688 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD688 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS688 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem688_eq : pairedProblem rows688 cols688 requiredD688 requiredS688 =
    MomentData.problem688 := by rfl
theorem leaf688 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows688++rows688))
    (hc : (q.map Prod.snd).Perm (cols688++cols688))
    (hd : ∀ k ∈ requiredD688, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS688, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows688 cols688 requiredD688 requiredS688
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem688_eq] at model
  exact MomentData.excluded688 ds ss model
def rows689 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols689 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD689 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS689 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem689_eq : pairedProblem rows689 cols689 requiredD689 requiredS689 =
    MomentData.problem689 := by rfl
theorem leaf689 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows689++rows689))
    (hc : (q.map Prod.snd).Perm (cols689++cols689))
    (hd : ∀ k ∈ requiredD689, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS689, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows689 cols689 requiredD689 requiredS689
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem689_eq] at model
  exact MomentData.excluded689 ds ss model
def rows690 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols690 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD690 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS690 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem690_eq : pairedProblem rows690 cols690 requiredD690 requiredS690 =
    MomentData.problem690 := by rfl
theorem leaf690 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows690++rows690))
    (hc : (q.map Prod.snd).Perm (cols690++cols690))
    (hd : ∀ k ∈ requiredD690, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS690, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows690 cols690 requiredD690 requiredS690
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem690_eq] at model
  exact MomentData.excluded690 ds ss model
def rows691 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def cols691 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD691 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS691 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,49]
theorem problem691_eq : pairedProblem rows691 cols691 requiredD691 requiredS691 =
    MomentData.problem691 := by rfl
theorem leaf691 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows691++rows691))
    (hc : (q.map Prod.snd).Perm (cols691++cols691))
    (hd : ∀ k ∈ requiredD691, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS691, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows691 cols691 requiredD691 requiredS691
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem691_eq] at model
  exact MomentData.excluded691 ds ss model
def rows692 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def cols692 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD692 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS692 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,49]
theorem problem692_eq : pairedProblem rows692 cols692 requiredD692 requiredS692 =
    MomentData.problem692 := by rfl
theorem leaf692 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows692++rows692))
    (hc : (q.map Prod.snd).Perm (cols692++cols692))
    (hd : ∀ k ∈ requiredD692, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS692, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows692 cols692 requiredD692 requiredS692
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem692_eq] at model
  exact MomentData.excluded692 ds ss model
def rows693 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def cols693 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD693 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS693 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,49]
theorem problem693_eq : pairedProblem rows693 cols693 requiredD693 requiredS693 =
    MomentData.problem693 := by rfl
theorem leaf693 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows693++rows693))
    (hc : (q.map Prod.snd).Perm (cols693++cols693))
    (hd : ∀ k ∈ requiredD693, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS693, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows693 cols693 requiredD693 requiredS693
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem693_eq] at model
  exact MomentData.excluded693 ds ss model
def rows694 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def cols694 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD694 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS694 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem694_eq : pairedProblem rows694 cols694 requiredD694 requiredS694 =
    MomentData.problem694 := by rfl
theorem leaf694 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows694++rows694))
    (hc : (q.map Prod.snd).Perm (cols694++cols694))
    (hd : ∀ k ∈ requiredD694, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS694, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows694 cols694 requiredD694 requiredS694
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem694_eq] at model
  exact MomentData.excluded694 ds ss model
def rows695 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21]
def cols695 : List Int := [0,1,2,3,11,12,13,14,15,16,17,18,19,20,21]
def requiredD695 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS695 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem695_eq : pairedProblem rows695 cols695 requiredD695 requiredS695 =
    MomentData.problem695 := by rfl
theorem leaf695 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows695++rows695))
    (hc : (q.map Prod.snd).Perm (cols695++cols695))
    (hd : ∀ k ∈ requiredD695, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS695, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows695 cols695 requiredD695 requiredS695
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem695_eq] at model
  exact MomentData.excluded695 ds ss model
def rows696 : List Int := [6,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def cols696 : List Int := [6,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def requiredD696 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS696 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,42]
theorem problem696_eq : pairedProblem rows696 cols696 requiredD696 requiredS696 =
    MomentData.problem696 := by rfl
theorem leaf696 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows696++rows696))
    (hc : (q.map Prod.snd).Perm (cols696++cols696))
    (hd : ∀ k ∈ requiredD696, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS696, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows696 cols696 requiredD696 requiredS696
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem696_eq] at model
  exact MomentData.excluded696 ds ss model
def rows697 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols697 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD697 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS697 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,44]
theorem problem697_eq : pairedProblem rows697 cols697 requiredD697 requiredS697 =
    MomentData.problem697 := by rfl
theorem leaf697 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows697++rows697))
    (hc : (q.map Prod.snd).Perm (cols697++cols697))
    (hd : ∀ k ∈ requiredD697, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS697, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows697 cols697 requiredD697 requiredS697
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem697_eq] at model
  exact MomentData.excluded697 ds ss model
def rows698 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,18,28,29]
def cols698 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD698 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS698 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem698_eq : pairedProblem rows698 cols698 requiredD698 requiredS698 =
    MomentData.problem698 := by rfl
theorem leaf698 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows698++rows698))
    (hc : (q.map Prod.snd).Perm (cols698++cols698))
    (hd : ∀ k ∈ requiredD698, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS698, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows698 cols698 requiredD698 requiredS698
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem698_eq] at model
  exact MomentData.excluded698 ds ss model
def rows699 : List Int := [0,1,2,9,10,11,12,13,14,15,16,17,18,19,29]
def cols699 : List Int := [0,1,2,9,10,11,12,13,14,15,16,17,18,19,29]
def requiredD699 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS699 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,48]
theorem problem699_eq : pairedProblem rows699 cols699 requiredD699 requiredS699 =
    MomentData.problem699 := by rfl
theorem leaf699 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows699++rows699))
    (hc : (q.map Prod.snd).Perm (cols699++cols699))
    (hd : ∀ k ∈ requiredD699, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS699, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows699 cols699 requiredD699 requiredS699
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem699_eq] at model
  exact MomentData.excluded699 ds ss model
def rows700 : List Int := [0,1,3,6,9,12,15,18,20,21,23,24,26,27,29]
def cols700 : List Int := [0,1,3,6,9,12,15,18,20,21,23,24,26,27,29]
def requiredD700 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS700 : List Int := [6,9,12,15,18,21,24,27,30,32,33,36,39,42,45]
theorem problem700_eq : pairedProblem rows700 cols700 requiredD700 requiredS700 =
    MomentData.problem700 := by rfl
theorem leaf700 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows700++rows700))
    (hc : (q.map Prod.snd).Perm (cols700++cols700))
    (hd : ∀ k ∈ requiredD700, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS700, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows700 cols700 requiredD700 requiredS700
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem700_eq] at model
  exact MomentData.excluded700 ds ss model
def rows701 : List Int := [0,1,2,4,7,10,13,16,19,21,22,24,25,27,28]
def cols701 : List Int := [0,1,2,4,7,10,13,16,19,21,22,24,25,27,28]
def requiredD701 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS701 : List Int := [8,11,14,17,20,23,26,29,32,34,35,38,41,44,47]
theorem problem701_eq : pairedProblem rows701 cols701 requiredD701 requiredS701 =
    MomentData.problem701 := by rfl
theorem leaf701 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows701++rows701))
    (hc : (q.map Prod.snd).Perm (cols701++cols701))
    (hd : ∀ k ∈ requiredD701, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS701, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows701 cols701 requiredD701 requiredS701
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem701_eq] at model
  exact MomentData.excluded701 ds ss model
def rows702 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols702 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD702 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS702 : List Int := [5,8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem702_eq : pairedProblem rows702 cols702 requiredD702 requiredS702 =
    MomentData.problem702 := by rfl
theorem leaf702 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows702++rows702))
    (hc : (q.map Prod.snd).Perm (cols702++cols702))
    (hd : ∀ k ∈ requiredD702, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS702, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows702 cols702 requiredD702 requiredS702
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem702_eq] at model
  exact MomentData.excluded702 ds ss model
def rows703 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols703 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD703 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS703 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem703_eq : pairedProblem rows703 cols703 requiredD703 requiredS703 =
    MomentData.problem703 := by rfl
theorem leaf703 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows703++rows703))
    (hc : (q.map Prod.snd).Perm (cols703++cols703))
    (hd : ∀ k ∈ requiredD703, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS703, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows703 cols703 requiredD703 requiredS703
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem703_eq] at model
  exact MomentData.excluded703 ds ss model
def rows704 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols704 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD704 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS704 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem704_eq : pairedProblem rows704 cols704 requiredD704 requiredS704 =
    MomentData.problem704 := by rfl
theorem leaf704 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows704++rows704))
    (hc : (q.map Prod.snd).Perm (cols704++cols704))
    (hd : ∀ k ∈ requiredD704, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS704, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows704 cols704 requiredD704 requiredS704
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem704_eq] at model
  exact MomentData.excluded704 ds ss model
def rows705 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols705 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD705 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS705 : List Int := [5,8,11,14,17,20,23,26,29,31,32,35,38,41]
theorem problem705_eq : pairedProblem rows705 cols705 requiredD705 requiredS705 =
    MomentData.problem705 := by rfl
theorem leaf705 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows705++rows705))
    (hc : (q.map Prod.snd).Perm (cols705++cols705))
    (hd : ∀ k ∈ requiredD705, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS705, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows705 cols705 requiredD705 requiredS705
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem705_eq] at model
  exact MomentData.excluded705 ds ss model
def rows706 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols706 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD706 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS706 : List Int := [7,10,13,16,19,22,25,28,31,33,34,37,40,43,46]
theorem problem706_eq : pairedProblem rows706 cols706 requiredD706 requiredS706 =
    MomentData.problem706 := by rfl
theorem leaf706 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows706++rows706))
    (hc : (q.map Prod.snd).Perm (cols706++cols706))
    (hd : ∀ k ∈ requiredD706, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS706, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows706 cols706 requiredD706 requiredS706
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem706_eq] at model
  exact MomentData.excluded706 ds ss model
def rows707 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols707 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD707 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS707 : List Int := [10,13,16,19,22,25,28,31,33,34,37,40,43,46]
theorem problem707_eq : pairedProblem rows707 cols707 requiredD707 requiredS707 =
    MomentData.problem707 := by rfl
theorem leaf707 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows707++rows707))
    (hc : (q.map Prod.snd).Perm (cols707++cols707))
    (hd : ∀ k ∈ requiredD707, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS707, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows707 cols707 requiredD707 requiredS707
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem707_eq] at model
  exact MomentData.excluded707 ds ss model
def rows708 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols708 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD708 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS708 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem708_eq : pairedProblem rows708 cols708 requiredD708 requiredS708 =
    MomentData.problem708 := by rfl
theorem leaf708 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows708++rows708))
    (hc : (q.map Prod.snd).Perm (cols708++cols708))
    (hd : ∀ k ∈ requiredD708, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS708, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows708 cols708 requiredD708 requiredS708
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem708_eq] at model
  exact MomentData.excluded708 ds ss model
def rows709 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols709 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD709 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS709 : List Int := [7,10,13,16,19,22,25,28,31,33,34,37,40,43]
theorem problem709_eq : pairedProblem rows709 cols709 requiredD709 requiredS709 =
    MomentData.problem709 := by rfl
theorem leaf709 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows709++rows709))
    (hc : (q.map Prod.snd).Perm (cols709++cols709))
    (hd : ∀ k ∈ requiredD709, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS709, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows709 cols709 requiredD709 requiredS709
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem709_eq] at model
  exact MomentData.excluded709 ds ss model
def rows710 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols710 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def requiredD710 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS710 : List Int := [9,12,15,18,21,24,27,30,33,35,36,39,42,45,48]
theorem problem710_eq : pairedProblem rows710 cols710 requiredD710 requiredS710 =
    MomentData.problem710 := by rfl
theorem leaf710 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows710++rows710))
    (hc : (q.map Prod.snd).Perm (cols710++cols710))
    (hd : ∀ k ∈ requiredD710, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS710, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows710 cols710 requiredD710 requiredS710
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem710_eq] at model
  exact MomentData.excluded710 ds ss model
def rows711 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols711 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def requiredD711 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS711 : List Int := [12,15,18,21,24,27,30,33,35,36,39,42,45,48]
theorem problem711_eq : pairedProblem rows711 cols711 requiredD711 requiredS711 =
    MomentData.problem711 := by rfl
theorem leaf711 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows711++rows711))
    (hc : (q.map Prod.snd).Perm (cols711++cols711))
    (hd : ∀ k ∈ requiredD711, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS711, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows711 cols711 requiredD711 requiredS711
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem711_eq] at model
  exact MomentData.excluded711 ds ss model
def rows712 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols712 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def requiredD712 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS712 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem712_eq : pairedProblem rows712 cols712 requiredD712 requiredS712 =
    MomentData.problem712 := by rfl
theorem leaf712 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows712++rows712))
    (hc : (q.map Prod.snd).Perm (cols712++cols712))
    (hd : ∀ k ∈ requiredD712, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS712, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows712 cols712 requiredD712 requiredS712
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem712_eq] at model
  exact MomentData.excluded712 ds ss model
def rows713 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols713 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def requiredD713 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS713 : List Int := [9,12,15,18,21,24,27,30,33,35,36,39,42,45]
theorem problem713_eq : pairedProblem rows713 cols713 requiredD713 requiredS713 =
    MomentData.problem713 := by rfl
theorem leaf713 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows713++rows713))
    (hc : (q.map Prod.snd).Perm (cols713++cols713))
    (hd : ∀ k ∈ requiredD713, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS713, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows713 cols713 requiredD713 requiredS713
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem713_eq] at model
  exact MomentData.excluded713 ds ss model
def rows714 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols714 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def requiredD714 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS714 : List Int := [11,14,17,20,23,26,29,32,35,37,38,41,44,47,50]
theorem problem714_eq : pairedProblem rows714 cols714 requiredD714 requiredS714 =
    MomentData.problem714 := by rfl
theorem leaf714 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows714++rows714))
    (hc : (q.map Prod.snd).Perm (cols714++cols714))
    (hd : ∀ k ∈ requiredD714, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS714, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows714 cols714 requiredD714 requiredS714
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem714_eq] at model
  exact MomentData.excluded714 ds ss model
def rows715 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols715 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def requiredD715 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS715 : List Int := [14,17,20,23,26,29,32,35,37,38,41,44,47,50]
theorem problem715_eq : pairedProblem rows715 cols715 requiredD715 requiredS715 =
    MomentData.problem715 := by rfl
theorem leaf715 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows715++rows715))
    (hc : (q.map Prod.snd).Perm (cols715++cols715))
    (hd : ∀ k ∈ requiredD715, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS715, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows715 cols715 requiredD715 requiredS715
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem715_eq] at model
  exact MomentData.excluded715 ds ss model
def rows716 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols716 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def requiredD716 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS716 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem716_eq : pairedProblem rows716 cols716 requiredD716 requiredS716 =
    MomentData.problem716 := by rfl
theorem leaf716 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows716++rows716))
    (hc : (q.map Prod.snd).Perm (cols716++cols716))
    (hd : ∀ k ∈ requiredD716, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS716, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows716 cols716 requiredD716 requiredS716
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem716_eq] at model
  exact MomentData.excluded716 ds ss model
def rows717 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols717 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def requiredD717 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS717 : List Int := [11,14,17,20,23,26,29,32,35,37,38,41,44,47]
theorem problem717_eq : pairedProblem rows717 cols717 requiredD717 requiredS717 =
    MomentData.problem717 := by rfl
theorem leaf717 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows717++rows717))
    (hc : (q.map Prod.snd).Perm (cols717++cols717))
    (hd : ∀ k ∈ requiredD717, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS717, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows717 cols717 requiredD717 requiredS717
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem717_eq] at model
  exact MomentData.excluded717 ds ss model
def rows718 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols718 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def requiredD718 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS718 : List Int := [6,9,12,15,18,21,24,27,30,32,33,36,39,42,45]
theorem problem718_eq : pairedProblem rows718 cols718 requiredD718 requiredS718 =
    MomentData.problem718 := by rfl
theorem leaf718 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows718++rows718))
    (hc : (q.map Prod.snd).Perm (cols718++cols718))
    (hd : ∀ k ∈ requiredD718, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS718, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows718 cols718 requiredD718 requiredS718
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem718_eq] at model
  exact MomentData.excluded718 ds ss model
def rows719 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols719 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def requiredD719 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS719 : List Int := [9,12,15,18,21,22,24,27,30,32,33,36,39,42,45]
theorem problem719_eq : pairedProblem rows719 cols719 requiredD719 requiredS719 =
    MomentData.problem719 := by rfl
theorem leaf719 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows719++rows719))
    (hc : (q.map Prod.snd).Perm (cols719++cols719))
    (hd : ∀ k ∈ requiredD719, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS719, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows719 cols719 requiredD719 requiredS719
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem719_eq] at model
  exact MomentData.excluded719 ds ss model
def rows720 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols720 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def requiredD720 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS720 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem720_eq : pairedProblem rows720 cols720 requiredD720 requiredS720 =
    MomentData.problem720 := by rfl
theorem leaf720 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows720++rows720))
    (hc : (q.map Prod.snd).Perm (cols720++cols720))
    (hd : ∀ k ∈ requiredD720, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS720, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows720 cols720 requiredD720 requiredS720
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem720_eq] at model
  exact MomentData.excluded720 ds ss model
def rows721 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols721 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def requiredD721 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS721 : List Int := [8,11,14,17,20,23,26,29,32,34,35,38,41,44,47]
theorem problem721_eq : pairedProblem rows721 cols721 requiredD721 requiredS721 =
    MomentData.problem721 := by rfl
theorem leaf721 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows721++rows721))
    (hc : (q.map Prod.snd).Perm (cols721++cols721))
    (hd : ∀ k ∈ requiredD721, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS721, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows721 cols721 requiredD721 requiredS721
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem721_eq] at model
  exact MomentData.excluded721 ds ss model
def rows722 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols722 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def requiredD722 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS722 : List Int := [11,14,17,20,23,24,26,29,32,34,35,38,41,44,47]
theorem problem722_eq : pairedProblem rows722 cols722 requiredD722 requiredS722 =
    MomentData.problem722 := by rfl
theorem leaf722 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows722++rows722))
    (hc : (q.map Prod.snd).Perm (cols722++cols722))
    (hd : ∀ k ∈ requiredD722, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS722, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows722 cols722 requiredD722 requiredS722
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem722_eq] at model
  exact MomentData.excluded722 ds ss model
def rows723 : List Int := [0,1,3,4,6,9,12,15,18,21,23,24,26,27,29]
def cols723 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def requiredD723 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS723 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem723_eq : pairedProblem rows723 cols723 requiredD723 requiredS723 =
    MomentData.problem723 := by rfl
theorem leaf723 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows723++rows723))
    (hc : (q.map Prod.snd).Perm (cols723++cols723))
    (hd : ∀ k ∈ requiredD723, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS723, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows723 cols723 requiredD723 requiredS723
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem723_eq] at model
  exact MomentData.excluded723 ds ss model
def rows724 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols724 : List Int := [0,1,3,4,6,8,9,12,15,18,21,24,26,27,29]
def requiredD724 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS724 : List Int := [10,13,16,19,22,25,28,31,34,36,37,40,43,46,49]
theorem problem724_eq : pairedProblem rows724 cols724 requiredD724 requiredS724 =
    MomentData.problem724 := by rfl
theorem leaf724 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows724++rows724))
    (hc : (q.map Prod.snd).Perm (cols724++cols724))
    (hd : ∀ k ∈ requiredD724, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS724, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows724 cols724 requiredD724 requiredS724
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem724_eq] at model
  exact MomentData.excluded724 ds ss model
def rows725 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols725 : List Int := [0,1,3,4,6,8,9,12,15,18,21,24,26,27,29]
def requiredD725 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS725 : List Int := [13,16,19,22,25,26,28,31,34,36,37,40,43,46,49]
theorem problem725_eq : pairedProblem rows725 cols725 requiredD725 requiredS725 =
    MomentData.problem725 := by rfl
theorem leaf725 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows725++rows725))
    (hc : (q.map Prod.snd).Perm (cols725++cols725))
    (hd : ∀ k ∈ requiredD725, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS725, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows725 cols725 requiredD725 requiredS725
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem725_eq] at model
  exact MomentData.excluded725 ds ss model
def rows726 : List Int := [0,1,2,4,5,7,10,13,16,19,22,24,25,27,28]
def cols726 : List Int := [0,1,3,4,6,8,9,12,15,18,21,24,26,27,29]
def requiredD726 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS726 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem726_eq : pairedProblem rows726 cols726 requiredD726 requiredS726 =
    MomentData.problem726 := by rfl
theorem leaf726 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows726++rows726))
    (hc : (q.map Prod.snd).Perm (cols726++cols726))
    (hd : ∀ k ∈ requiredD726, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS726, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows726 cols726 requiredD726 requiredS726
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem726_eq] at model
  exact MomentData.excluded726 ds ss model
def rows727 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def cols727 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD727 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS727 : List Int := [9,12,15,18,21,22,24,27,30,33,36,39,42,45,48]
theorem problem727_eq : pairedProblem rows727 cols727 requiredD727 requiredS727 =
    MomentData.problem727 := by rfl
theorem leaf727 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows727++rows727))
    (hc : (q.map Prod.snd).Perm (cols727++cols727))
    (hd : ∀ k ∈ requiredD727, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS727, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows727 cols727 requiredD727 requiredS727
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem727_eq] at model
  exact MomentData.excluded727 ds ss model
def rows728 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def cols728 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD728 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS728 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem728_eq : pairedProblem rows728 cols728 requiredD728 requiredS728 =
    MomentData.problem728 := by rfl
theorem leaf728 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows728++rows728))
    (hc : (q.map Prod.snd).Perm (cols728++cols728))
    (hd : ∀ k ∈ requiredD728, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS728, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows728 cols728 requiredD728 requiredS728
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem728_eq] at model
  exact MomentData.excluded728 ds ss model
def rows729 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def cols729 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD729 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS729 : List Int := [9,12,15,18,21,22,24,27,30,32,33,36,39,42,45]
theorem problem729_eq : pairedProblem rows729 cols729 requiredD729 requiredS729 =
    MomentData.problem729 := by rfl
theorem leaf729 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows729++rows729))
    (hc : (q.map Prod.snd).Perm (cols729++cols729))
    (hd : ∀ k ∈ requiredD729, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS729, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows729 cols729 requiredD729 requiredS729
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem729_eq] at model
  exact MomentData.excluded729 ds ss model
def rows730 : List Int := [0,1,3,4,6,9,12,15,18,21,22,24,26,27,29]
def cols730 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD730 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS730 : List Int := [11,14,17,20,23,24,26,29,32,35,38,41,44,47,50]
theorem problem730_eq : pairedProblem rows730 cols730 requiredD730 requiredS730 =
    MomentData.problem730 := by rfl
theorem leaf730 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows730++rows730))
    (hc : (q.map Prod.snd).Perm (cols730++cols730))
    (hd : ∀ k ∈ requiredD730, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS730, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows730 cols730 requiredD730 requiredS730
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem730_eq] at model
  exact MomentData.excluded730 ds ss model
def rows731 : List Int := [0,1,3,4,6,9,12,15,18,21,22,24,26,27,29]
def cols731 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD731 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS731 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem731_eq : pairedProblem rows731 cols731 requiredD731 requiredS731 =
    MomentData.problem731 := by rfl
theorem leaf731 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows731++rows731))
    (hc : (q.map Prod.snd).Perm (cols731++cols731))
    (hd : ∀ k ∈ requiredD731, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS731, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows731 cols731 requiredD731 requiredS731
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem731_eq] at model
  exact MomentData.excluded731 ds ss model
def rows732 : List Int := [0,1,3,4,6,9,12,15,18,21,22,24,26,27,29]
def cols732 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD732 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS732 : List Int := [11,14,17,20,23,24,26,29,32,34,35,38,41,44,47]
theorem problem732_eq : pairedProblem rows732 cols732 requiredD732 requiredS732 =
    MomentData.problem732 := by rfl
theorem leaf732 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows732++rows732))
    (hc : (q.map Prod.snd).Perm (cols732++cols732))
    (hd : ∀ k ∈ requiredD732, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS732, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows732 cols732 requiredD732 requiredS732
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem732_eq] at model
  exact MomentData.excluded732 ds ss model
def rows733 : List Int := [0,1,2,4,5,7,10,13,16,19,22,23,25,27,28]
def cols733 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD733 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,6,7,10,13,16,19]
def requiredS733 : List Int := [13,16,19,22,25,26,28,31,34,37,40,43,46,49,52]
theorem problem733_eq : pairedProblem rows733 cols733 requiredD733 requiredS733 =
    MomentData.problem733 := by rfl
theorem leaf733 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows733++rows733))
    (hc : (q.map Prod.snd).Perm (cols733++cols733))
    (hd : ∀ k ∈ requiredD733, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS733, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows733 cols733 requiredD733 requiredS733
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem733_eq] at model
  exact MomentData.excluded733 ds ss model
def rows734 : List Int := [0,1,2,4,5,7,10,13,16,19,22,23,25,27,28]
def cols734 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD734 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS734 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49,52]
theorem problem734_eq : pairedProblem rows734 cols734 requiredD734 requiredS734 =
    MomentData.problem734 := by rfl
theorem leaf734 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows734++rows734))
    (hc : (q.map Prod.snd).Perm (cols734++cols734))
    (hd : ∀ k ∈ requiredD734, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS734, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows734 cols734 requiredD734 requiredS734
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem734_eq] at model
  exact MomentData.excluded734 ds ss model
def rows735 : List Int := [0,1,2,4,5,7,10,13,16,19,22,23,25,27,28]
def cols735 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD735 : List Int := [-17,-14,-11,-8,-5,-4,-2,1,4,6,7,10,13,16,19]
def requiredS735 : List Int := [13,16,19,22,25,26,28,31,34,36,37,40,43,46,49]
theorem problem735_eq : pairedProblem rows735 cols735 requiredD735 requiredS735 =
    MomentData.problem735 := by rfl
theorem leaf735 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows735++rows735))
    (hc : (q.map Prod.snd).Perm (cols735++cols735))
    (hd : ∀ k ∈ requiredD735, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS735, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows735 cols735 requiredD735 requiredS735
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem735_eq] at model
  exact MomentData.excluded735 ds ss model
def rows736 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols736 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD736 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS736 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44,47]
theorem problem736_eq : pairedProblem rows736 cols736 requiredD736 requiredS736 =
    MomentData.problem736 := by rfl
theorem leaf736 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows736++rows736))
    (hc : (q.map Prod.snd).Perm (cols736++cols736))
    (hd : ∀ k ∈ requiredD736, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS736, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows736 cols736 requiredD736 requiredS736
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem736_eq] at model
  exact MomentData.excluded736 ds ss model
def rows737 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols737 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD737 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS737 : List Int := [11,14,17,20,21,23,26,29,32,35,38,41,44,47]
theorem problem737_eq : pairedProblem rows737 cols737 requiredD737 requiredS737 =
    MomentData.problem737 := by rfl
theorem leaf737 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows737++rows737))
    (hc : (q.map Prod.snd).Perm (cols737++cols737))
    (hd : ∀ k ∈ requiredD737, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS737, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows737 cols737 requiredD737 requiredS737
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem737_eq] at model
  exact MomentData.excluded737 ds ss model
def rows738 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols738 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD738 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS738 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem738_eq : pairedProblem rows738 cols738 requiredD738 requiredS738 =
    MomentData.problem738 := by rfl
theorem leaf738 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows738++rows738))
    (hc : (q.map Prod.snd).Perm (cols738++cols738))
    (hd : ∀ k ∈ requiredD738, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS738, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows738 cols738 requiredD738 requiredS738
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem738_eq] at model
  exact MomentData.excluded738 ds ss model
def rows739 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols739 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD739 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS739 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem739_eq : pairedProblem rows739 cols739 requiredD739 requiredS739 =
    MomentData.problem739 := by rfl
theorem leaf739 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows739++rows739))
    (hc : (q.map Prod.snd).Perm (cols739++cols739))
    (hd : ∀ k ∈ requiredD739, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS739, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows739 cols739 requiredD739 requiredS739
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem739_eq] at model
  exact MomentData.excluded739 ds ss model
def rows740 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols740 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD740 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS740 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46,49]
theorem problem740_eq : pairedProblem rows740 cols740 requiredD740 requiredS740 =
    MomentData.problem740 := by rfl
theorem leaf740 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows740++rows740))
    (hc : (q.map Prod.snd).Perm (cols740++cols740))
    (hd : ∀ k ∈ requiredD740, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS740, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows740 cols740 requiredD740 requiredS740
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem740_eq] at model
  exact MomentData.excluded740 ds ss model
def rows741 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols741 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD741 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS741 : List Int := [13,16,19,22,23,25,28,31,34,37,40,43,46,49]
theorem problem741_eq : pairedProblem rows741 cols741 requiredD741 requiredS741 =
    MomentData.problem741 := by rfl
theorem leaf741 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows741++rows741))
    (hc : (q.map Prod.snd).Perm (cols741++cols741))
    (hd : ∀ k ∈ requiredD741, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS741, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows741 cols741 requiredD741 requiredS741
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem741_eq] at model
  exact MomentData.excluded741 ds ss model
def rows742 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols742 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD742 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS742 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem742_eq : pairedProblem rows742 cols742 requiredD742 requiredS742 =
    MomentData.problem742 := by rfl
theorem leaf742 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows742++rows742))
    (hc : (q.map Prod.snd).Perm (cols742++cols742))
    (hd : ∀ k ∈ requiredD742, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS742, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows742 cols742 requiredD742 requiredS742
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem742_eq] at model
  exact MomentData.excluded742 ds ss model
def rows743 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols743 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD743 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS743 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem743_eq : pairedProblem rows743 cols743 requiredD743 requiredS743 =
    MomentData.problem743 := by rfl
theorem leaf743 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows743++rows743))
    (hc : (q.map Prod.snd).Perm (cols743++cols743))
    (hd : ∀ k ∈ requiredD743, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS743, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows743 cols743 requiredD743 requiredS743
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem743_eq] at model
  exact MomentData.excluded743 ds ss model
def rows744 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def cols744 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD744 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS744 : List Int := [12,15,18,21,24,25,27,30,33,36,39,42,45,48,51]
theorem problem744_eq : pairedProblem rows744 cols744 requiredD744 requiredS744 =
    MomentData.problem744 := by rfl
theorem leaf744 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows744++rows744))
    (hc : (q.map Prod.snd).Perm (cols744++cols744))
    (hd : ∀ k ∈ requiredD744, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS744, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows744 cols744 requiredD744 requiredS744
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem744_eq] at model
  exact MomentData.excluded744 ds ss model
def rows745 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def cols745 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD745 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS745 : List Int := [15,18,21,24,25,27,30,33,36,39,42,45,48,51]
theorem problem745_eq : pairedProblem rows745 cols745 requiredD745 requiredS745 =
    MomentData.problem745 := by rfl
theorem leaf745 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows745++rows745))
    (hc : (q.map Prod.snd).Perm (cols745++cols745))
    (hd : ∀ k ∈ requiredD745, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS745, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows745 cols745 requiredD745 requiredS745
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem745_eq] at model
  exact MomentData.excluded745 ds ss model
def rows746 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def cols746 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD746 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS746 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem746_eq : pairedProblem rows746 cols746 requiredD746 requiredS746 =
    MomentData.problem746 := by rfl
theorem leaf746 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows746++rows746))
    (hc : (q.map Prod.snd).Perm (cols746++cols746))
    (hd : ∀ k ∈ requiredD746, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS746, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows746 cols746 requiredD746 requiredS746
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem746_eq] at model
  exact MomentData.excluded746 ds ss model
def rows747 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def cols747 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,26,27,29]
def requiredD747 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS747 : List Int := [12,15,18,21,24,25,27,30,33,36,39,42,45,48]
theorem problem747_eq : pairedProblem rows747 cols747 requiredD747 requiredS747 =
    MomentData.problem747 := by rfl
theorem leaf747 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows747++rows747))
    (hc : (q.map Prod.snd).Perm (cols747++cols747))
    (hd : ∀ k ∈ requiredD747, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS747, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows747 cols747 requiredD747 requiredS747
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem747_eq] at model
  exact MomentData.excluded747 ds ss model
def rows748 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def cols748 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def requiredD748 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS748 : List Int := [14,17,20,23,26,27,29,32,35,38,41,44,47,50,53]
theorem problem748_eq : pairedProblem rows748 cols748 requiredD748 requiredS748 =
    MomentData.problem748 := by rfl
theorem leaf748 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows748++rows748))
    (hc : (q.map Prod.snd).Perm (cols748++cols748))
    (hd : ∀ k ∈ requiredD748, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS748, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows748 cols748 requiredD748 requiredS748
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem748_eq] at model
  exact MomentData.excluded748 ds ss model
def rows749 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def cols749 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def requiredD749 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS749 : List Int := [17,20,23,26,27,29,32,35,38,41,44,47,50,53]
theorem problem749_eq : pairedProblem rows749 cols749 requiredD749 requiredS749 =
    MomentData.problem749 := by rfl
theorem leaf749 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows749++rows749))
    (hc : (q.map Prod.snd).Perm (cols749++cols749))
    (hd : ∀ k ∈ requiredD749, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS749, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows749 cols749 requiredD749 requiredS749
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem749_eq] at model
  exact MomentData.excluded749 ds ss model
def rows750 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def cols750 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def requiredD750 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS750 : List Int := [14,17,20,23,26,29,32,35,38,41,44,47,50,53]
theorem problem750_eq : pairedProblem rows750 cols750 requiredD750 requiredS750 =
    MomentData.problem750 := by rfl
theorem leaf750 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows750++rows750))
    (hc : (q.map Prod.snd).Perm (cols750++cols750))
    (hd : ∀ k ∈ requiredD750, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS750, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows750 cols750 requiredD750 requiredS750
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem750_eq] at model
  exact MomentData.excluded750 ds ss model
def rows751 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def cols751 : List Int := [0,1,2,4,5,7,8,10,13,16,19,22,25,27,28]
def requiredD751 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS751 : List Int := [14,17,20,23,26,27,29,32,35,38,41,44,47,50]
theorem problem751_eq : pairedProblem rows751 cols751 requiredD751 requiredS751 =
    MomentData.problem751 := by rfl
theorem leaf751 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows751++rows751))
    (hc : (q.map Prod.snd).Perm (cols751++cols751))
    (hd : ∀ k ∈ requiredD751, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS751, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows751 cols751 requiredD751 requiredS751
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem751_eq] at model
  exact MomentData.excluded751 ds ss model
def rows752 : List Int := [1,2,4,5,7,8,10,13,16,19,22,25,27,28,29]
def cols752 : List Int := [1,2,4,5,7,8,10,13,16,19,22,25,27,28,29]
def requiredD752 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS752 : List Int := [11,14,17,20,23,24,26,29,32,35,38,41,44,47,50]
theorem problem752_eq : pairedProblem rows752 cols752 requiredD752 requiredS752 =
    MomentData.problem752 := by rfl
theorem leaf752 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows752++rows752))
    (hc : (q.map Prod.snd).Perm (cols752++cols752))
    (hd : ∀ k ∈ requiredD752, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS752, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows752 cols752 requiredD752 requiredS752
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem752_eq] at model
  exact MomentData.excluded752 ds ss model
def rows753 : List Int := [0,2,3,5,6,8,9,11,14,17,20,23,26,28,29]
def cols753 : List Int := [0,2,3,5,6,8,9,11,14,17,20,23,26,28,29]
def requiredD753 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS753 : List Int := [13,16,19,22,25,26,28,31,34,37,40,43,46,49,52]
theorem problem753_eq : pairedProblem rows753 cols753 requiredD753 requiredS753 =
    MomentData.problem753 := by rfl
theorem leaf753 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows753++rows753))
    (hc : (q.map Prod.snd).Perm (cols753++cols753))
    (hd : ∀ k ∈ requiredD753, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS753, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows753 cols753 requiredD753 requiredS753
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem753_eq] at model
  exact MomentData.excluded753 ds ss model
def rows754 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols754 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD754 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS754 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,46]
theorem problem754_eq : pairedProblem rows754 cols754 requiredD754 requiredS754 =
    MomentData.problem754 := by rfl
theorem leaf754 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows754++rows754))
    (hc : (q.map Prod.snd).Perm (cols754++cols754))
    (hd : ∀ k ∈ requiredD754, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS754, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows754 cols754 requiredD754 requiredS754
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem754_eq] at model
  exact MomentData.excluded754 ds ss model
def rows755 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols755 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD755 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS755 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem755_eq : pairedProblem rows755 cols755 requiredD755 requiredS755 =
    MomentData.problem755 := by rfl
theorem leaf755 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows755++rows755))
    (hc : (q.map Prod.snd).Perm (cols755++cols755))
    (hd : ∀ k ∈ requiredD755, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS755, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows755 cols755 requiredD755 requiredS755
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem755_eq] at model
  exact MomentData.excluded755 ds ss model
def rows756 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols756 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD756 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS756 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,48]
theorem problem756_eq : pairedProblem rows756 cols756 requiredD756 requiredS756 =
    MomentData.problem756 := by rfl
theorem leaf756 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows756++rows756))
    (hc : (q.map Prod.snd).Perm (cols756++cols756))
    (hd : ∀ k ∈ requiredD756, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS756, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows756 cols756 requiredD756 requiredS756
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem756_eq] at model
  exact MomentData.excluded756 ds ss model
def rows757 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols757 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD757 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,20]
def requiredS757 : List Int := [10,23,24,25,26,27,28,29,30,31,32,33,34,35,48]
theorem problem757_eq : pairedProblem rows757 cols757 requiredD757 requiredS757 =
    MomentData.problem757 := by rfl
theorem leaf757 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows757++rows757))
    (hc : (q.map Prod.snd).Perm (cols757++cols757))
    (hd : ∀ k ∈ requiredD757, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS757, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows757 cols757 requiredD757 requiredS757
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem757_eq] at model
  exact MomentData.excluded757 ds ss model
def rows758 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols758 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD758 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS758 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem758_eq : pairedProblem rows758 cols758 requiredD758 requiredS758 =
    MomentData.problem758 := by rfl
theorem leaf758 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows758++rows758))
    (hc : (q.map Prod.snd).Perm (cols758++cols758))
    (hd : ∀ k ∈ requiredD758, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS758, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows758 cols758 requiredD758 requiredS758
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem758_eq] at model
  exact MomentData.excluded758 ds ss model
def rows759 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,25]
def cols759 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD759 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS759 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem759_eq : pairedProblem rows759 cols759 requiredD759 requiredS759 =
    MomentData.problem759 := by rfl
theorem leaf759 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows759++rows759))
    (hc : (q.map Prod.snd).Perm (cols759++cols759))
    (hd : ∀ k ∈ requiredD759, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS759, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows759 cols759 requiredD759 requiredS759
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem759_eq] at model
  exact MomentData.excluded759 ds ss model
def rows760 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,28,29]
def cols760 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,28,29]
def requiredD760 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS760 : List Int := [10,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem760_eq : pairedProblem rows760 cols760 requiredD760 requiredS760 =
    MomentData.problem760 := by rfl
theorem leaf760 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows760++rows760))
    (hc : (q.map Prod.snd).Perm (cols760++cols760))
    (hd : ∀ k ∈ requiredD760, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS760, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows760 cols760 requiredD760 requiredS760
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem760_eq] at model
  exact MomentData.excluded760 ds ss model
def rows761 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,22,29]
def cols761 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,22,29]
def requiredD761 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS761 : List Int := [12,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem761_eq : pairedProblem rows761 cols761 requiredD761 requiredS761 =
    MomentData.problem761 := by rfl
theorem leaf761 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows761++rows761))
    (hc : (q.map Prod.snd).Perm (cols761++cols761))
    (hd : ∀ k ∈ requiredD761, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS761, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows761 cols761 requiredD761 requiredS761
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem761_eq] at model
  exact MomentData.excluded761 ds ss model
def rows762 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,22,23]
def cols762 : List Int := [0,1,2,12,13,14,15,16,17,18,19,20,21,22,23]
def requiredD762 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS762 : List Int := [14,27,28,29,30,31,32,33,34,35,36,37,38,39,40]
theorem problem762_eq : pairedProblem rows762 cols762 requiredD762 requiredS762 =
    MomentData.problem762 := by rfl
theorem leaf762 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows762++rows762))
    (hc : (q.map Prod.snd).Perm (cols762++cols762))
    (hd : ∀ k ∈ requiredD762, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS762, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows762 cols762 requiredD762 requiredS762
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem762_eq] at model
  exact MomentData.excluded762 ds ss model
def rows763 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols763 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD763 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS763 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem763_eq : pairedProblem rows763 cols763 requiredD763 requiredS763 =
    MomentData.problem763 := by rfl
theorem leaf763 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows763++rows763))
    (hc : (q.map Prod.snd).Perm (cols763++cols763))
    (hd : ∀ k ∈ requiredD763, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS763, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows763 cols763 requiredD763 requiredS763
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem763_eq] at model
  exact MomentData.excluded763 ds ss model
def rows764 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols764 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD764 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS764 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem764_eq : pairedProblem rows764 cols764 requiredD764 requiredS764 =
    MomentData.problem764 := by rfl
theorem leaf764 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows764++rows764))
    (hc : (q.map Prod.snd).Perm (cols764++cols764))
    (hd : ∀ k ∈ requiredD764, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS764, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows764 cols764 requiredD764 requiredS764
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem764_eq] at model
  exact MomentData.excluded764 ds ss model
def rows765 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols765 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD765 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS765 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem765_eq : pairedProblem rows765 cols765 requiredD765 requiredS765 =
    MomentData.problem765 := by rfl
theorem leaf765 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows765++rows765))
    (hc : (q.map Prod.snd).Perm (cols765++cols765))
    (hd : ∀ k ∈ requiredD765, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS765, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows765 cols765 requiredD765 requiredS765
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem765_eq] at model
  exact MomentData.excluded765 ds ss model
def rows766 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols766 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD766 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS766 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem766_eq : pairedProblem rows766 cols766 requiredD766 requiredS766 =
    MomentData.problem766 := by rfl
theorem leaf766 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows766++rows766))
    (hc : (q.map Prod.snd).Perm (cols766++cols766))
    (hd : ∀ k ∈ requiredD766, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS766, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows766 cols766 requiredD766 requiredS766
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem766_eq] at model
  exact MomentData.excluded766 ds ss model
def rows767 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols767 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD767 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS767 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem767_eq : pairedProblem rows767 cols767 requiredD767 requiredS767 =
    MomentData.problem767 := by rfl
theorem leaf767 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows767++rows767))
    (hc : (q.map Prod.snd).Perm (cols767++cols767))
    (hd : ∀ k ∈ requiredD767, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS767, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows767 cols767 requiredD767 requiredS767
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem767_eq] at model
  exact MomentData.excluded767 ds ss model
#print axioms leaf640
end Gardner.Kernel.MomentContexts
