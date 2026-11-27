import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows768 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols768 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD768 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS768 : List Int := [11,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem768_eq : pairedProblem rows768 cols768 requiredD768 requiredS768 =
    MomentData.problem768 := by rfl
theorem leaf768 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows768++rows768))
    (hc : (q.map Prod.snd).Perm (cols768++cols768))
    (hd : ∀ k ∈ requiredD768, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS768, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows768 cols768 requiredD768 requiredS768
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem768_eq] at model
  exact MomentData.excluded768 ds ss model
def rows769 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols769 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD769 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS769 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem769_eq : pairedProblem rows769 cols769 requiredD769 requiredS769 =
    MomentData.problem769 := by rfl
theorem leaf769 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows769++rows769))
    (hc : (q.map Prod.snd).Perm (cols769++cols769))
    (hd : ∀ k ∈ requiredD769, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS769, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows769 cols769 requiredD769 requiredS769
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem769_eq] at model
  exact MomentData.excluded769 ds ss model
def rows770 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols770 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD770 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS770 : List Int := [11,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem770_eq : pairedProblem rows770 cols770 requiredD770 requiredS770 =
    MomentData.problem770 := by rfl
theorem leaf770 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows770++rows770))
    (hc : (q.map Prod.snd).Perm (cols770++cols770))
    (hd : ∀ k ∈ requiredD770, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS770, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows770 cols770 requiredD770 requiredS770
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem770_eq] at model
  exact MomentData.excluded770 ds ss model
def rows771 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols771 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD771 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS771 : List Int := [11,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem771_eq : pairedProblem rows771 cols771 requiredD771 requiredS771 =
    MomentData.problem771 := by rfl
theorem leaf771 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows771++rows771))
    (hc : (q.map Prod.snd).Perm (cols771++cols771))
    (hd : ∀ k ∈ requiredD771, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS771, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows771 cols771 requiredD771 requiredS771
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem771_eq] at model
  exact MomentData.excluded771 ds ss model
def rows772 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols772 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD772 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS772 : List Int := [13,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem772_eq : pairedProblem rows772 cols772 requiredD772 requiredS772 =
    MomentData.problem772 := by rfl
theorem leaf772 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows772++rows772))
    (hc : (q.map Prod.snd).Perm (cols772++cols772))
    (hd : ∀ k ∈ requiredD772, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS772, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows772 cols772 requiredD772 requiredS772
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem772_eq] at model
  exact MomentData.excluded772 ds ss model
def rows773 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols773 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD773 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS773 : List Int := [26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem773_eq : pairedProblem rows773 cols773 requiredD773 requiredS773 =
    MomentData.problem773 := by rfl
theorem leaf773 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows773++rows773))
    (hc : (q.map Prod.snd).Perm (cols773++cols773))
    (hd : ∀ k ∈ requiredD773, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS773, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows773 cols773 requiredD773 requiredS773
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem773_eq] at model
  exact MomentData.excluded773 ds ss model
def rows774 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols774 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD774 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS774 : List Int := [13,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem774_eq : pairedProblem rows774 cols774 requiredD774 requiredS774 =
    MomentData.problem774 := by rfl
theorem leaf774 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows774++rows774))
    (hc : (q.map Prod.snd).Perm (cols774++cols774))
    (hd : ∀ k ∈ requiredD774, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS774, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows774 cols774 requiredD774 requiredS774
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem774_eq] at model
  exact MomentData.excluded774 ds ss model
def rows775 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols775 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD775 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS775 : List Int := [13,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem775_eq : pairedProblem rows775 cols775 requiredD775 requiredS775 =
    MomentData.problem775 := by rfl
theorem leaf775 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows775++rows775))
    (hc : (q.map Prod.snd).Perm (cols775++cols775))
    (hd : ∀ k ∈ requiredD775, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS775, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows775 cols775 requiredD775 requiredS775
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem775_eq] at model
  exact MomentData.excluded775 ds ss model
def rows776 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols776 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD776 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS776 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem776_eq : pairedProblem rows776 cols776 requiredD776 requiredS776 =
    MomentData.problem776 := by rfl
theorem leaf776 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows776++rows776))
    (hc : (q.map Prod.snd).Perm (cols776++cols776))
    (hd : ∀ k ∈ requiredD776, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS776, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows776 cols776 requiredD776 requiredS776
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem776_eq] at model
  exact MomentData.excluded776 ds ss model
def rows777 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols777 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD777 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS777 : List Int := [10,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem777_eq : pairedProblem rows777 cols777 requiredD777 requiredS777 =
    MomentData.problem777 := by rfl
theorem leaf777 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows777++rows777))
    (hc : (q.map Prod.snd).Perm (cols777++cols777))
    (hd : ∀ k ∈ requiredD777, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS777, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows777 cols777 requiredD777 requiredS777
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem777_eq] at model
  exact MomentData.excluded777 ds ss model
def rows778 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols778 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD778 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS778 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem778_eq : pairedProblem rows778 cols778 requiredD778 requiredS778 =
    MomentData.problem778 := by rfl
theorem leaf778 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows778++rows778))
    (hc : (q.map Prod.snd).Perm (cols778++cols778))
    (hd : ∀ k ∈ requiredD778, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS778, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows778 cols778 requiredD778 requiredS778
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem778_eq] at model
  exact MomentData.excluded778 ds ss model
def rows779 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols779 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD779 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,20]
def requiredS779 : List Int := [10,23,24,25,26,27,28,29,30,31,32,33,34,35,48]
theorem problem779_eq : pairedProblem rows779 cols779 requiredD779 requiredS779 =
    MomentData.problem779 := by rfl
theorem leaf779 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows779++rows779))
    (hc : (q.map Prod.snd).Perm (cols779++cols779))
    (hd : ∀ k ∈ requiredD779, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS779, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows779 cols779 requiredD779 requiredS779
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem779_eq] at model
  exact MomentData.excluded779 ds ss model
def rows780 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols780 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD780 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS780 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem780_eq : pairedProblem rows780 cols780 requiredD780 requiredS780 =
    MomentData.problem780 := by rfl
theorem leaf780 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows780++rows780))
    (hc : (q.map Prod.snd).Perm (cols780++cols780))
    (hd : ∀ k ∈ requiredD780, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS780, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows780 cols780 requiredD780 requiredS780
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem780_eq] at model
  exact MomentData.excluded780 ds ss model
def rows781 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,20,21,22]
def cols781 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD781 : List Int := [-18,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS781 : List Int := [12,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem781_eq : pairedProblem rows781 cols781 requiredD781 requiredS781 =
    MomentData.problem781 := by rfl
theorem leaf781 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows781++rows781))
    (hc : (q.map Prod.snd).Perm (cols781++cols781))
    (hd : ∀ k ∈ requiredD781, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS781, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows781 cols781 requiredD781 requiredS781
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem781_eq] at model
  exact MomentData.excluded781 ds ss model
def rows782 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols782 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD782 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS782 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem782_eq : pairedProblem rows782 cols782 requiredD782 requiredS782 =
    MomentData.problem782 := by rfl
theorem leaf782 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows782++rows782))
    (hc : (q.map Prod.snd).Perm (cols782++cols782))
    (hd : ∀ k ∈ requiredD782, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS782, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows782 cols782 requiredD782 requiredS782
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem782_eq] at model
  exact MomentData.excluded782 ds ss model
def rows783 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols783 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD783 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS783 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem783_eq : pairedProblem rows783 cols783 requiredD783 requiredS783 =
    MomentData.problem783 := by rfl
theorem leaf783 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows783++rows783))
    (hc : (q.map Prod.snd).Perm (cols783++cols783))
    (hd : ∀ k ∈ requiredD783, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS783, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows783 cols783 requiredD783 requiredS783
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem783_eq] at model
  exact MomentData.excluded783 ds ss model
def rows784 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols784 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD784 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS784 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,45]
theorem problem784_eq : pairedProblem rows784 cols784 requiredD784 requiredS784 =
    MomentData.problem784 := by rfl
theorem leaf784 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows784++rows784))
    (hc : (q.map Prod.snd).Perm (cols784++cols784))
    (hd : ∀ k ∈ requiredD784, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS784, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows784 cols784 requiredD784 requiredS784
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem784_eq] at model
  exact MomentData.excluded784 ds ss model
def rows785 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols785 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD785 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS785 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem785_eq : pairedProblem rows785 cols785 requiredD785 requiredS785 =
    MomentData.problem785 := by rfl
theorem leaf785 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows785++rows785))
    (hc : (q.map Prod.snd).Perm (cols785++cols785))
    (hd : ∀ k ∈ requiredD785, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS785, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows785 cols785 requiredD785 requiredS785
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem785_eq] at model
  exact MomentData.excluded785 ds ss model
def rows786 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols786 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD786 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS786 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem786_eq : pairedProblem rows786 cols786 requiredD786 requiredS786 =
    MomentData.problem786 := by rfl
theorem leaf786 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows786++rows786))
    (hc : (q.map Prod.snd).Perm (cols786++cols786))
    (hd : ∀ k ∈ requiredD786, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS786, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows786 cols786 requiredD786 requiredS786
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem786_eq] at model
  exact MomentData.excluded786 ds ss model
def rows787 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols787 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD787 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS787 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem787_eq : pairedProblem rows787 cols787 requiredD787 requiredS787 =
    MomentData.problem787 := by rfl
theorem leaf787 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows787++rows787))
    (hc : (q.map Prod.snd).Perm (cols787++cols787))
    (hd : ∀ k ∈ requiredD787, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS787, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows787 cols787 requiredD787 requiredS787
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem787_eq] at model
  exact MomentData.excluded787 ds ss model
def rows788 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols788 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD788 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS788 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem788_eq : pairedProblem rows788 cols788 requiredD788 requiredS788 =
    MomentData.problem788 := by rfl
theorem leaf788 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows788++rows788))
    (hc : (q.map Prod.snd).Perm (cols788++cols788))
    (hd : ∀ k ∈ requiredD788, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS788, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows788 cols788 requiredD788 requiredS788
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem788_eq] at model
  exact MomentData.excluded788 ds ss model
def rows789 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols789 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD789 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS789 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem789_eq : pairedProblem rows789 cols789 requiredD789 requiredS789 =
    MomentData.problem789 := by rfl
theorem leaf789 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows789++rows789))
    (hc : (q.map Prod.snd).Perm (cols789++cols789))
    (hd : ∀ k ∈ requiredD789, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS789, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows789 cols789 requiredD789 requiredS789
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem789_eq] at model
  exact MomentData.excluded789 ds ss model
def rows790 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols790 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD790 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS790 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,49]
theorem problem790_eq : pairedProblem rows790 cols790 requiredD790 requiredS790 =
    MomentData.problem790 := by rfl
theorem leaf790 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows790++rows790))
    (hc : (q.map Prod.snd).Perm (cols790++cols790))
    (hd : ∀ k ∈ requiredD790, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS790, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows790 cols790 requiredD790 requiredS790
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem790_eq] at model
  exact MomentData.excluded790 ds ss model
def rows791 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols791 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD791 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS791 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,49]
theorem problem791_eq : pairedProblem rows791 cols791 requiredD791 requiredS791 =
    MomentData.problem791 := by rfl
theorem leaf791 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows791++rows791))
    (hc : (q.map Prod.snd).Perm (cols791++cols791))
    (hd : ∀ k ∈ requiredD791, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS791, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows791 cols791 requiredD791 requiredS791
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem791_eq] at model
  exact MomentData.excluded791 ds ss model
def rows792 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols792 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD792 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS792 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem792_eq : pairedProblem rows792 cols792 requiredD792 requiredS792 =
    MomentData.problem792 := by rfl
theorem leaf792 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows792++rows792))
    (hc : (q.map Prod.snd).Perm (cols792++cols792))
    (hd : ∀ k ∈ requiredD792, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS792, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows792 cols792 requiredD792 requiredS792
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem792_eq] at model
  exact MomentData.excluded792 ds ss model
def rows793 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols793 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD793 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS793 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem793_eq : pairedProblem rows793 cols793 requiredD793 requiredS793 =
    MomentData.problem793 := by rfl
theorem leaf793 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows793++rows793))
    (hc : (q.map Prod.snd).Perm (cols793++cols793))
    (hd : ∀ k ∈ requiredD793, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS793, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows793 cols793 requiredD793 requiredS793
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem793_eq] at model
  exact MomentData.excluded793 ds ss model
def rows794 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,21]
def cols794 : List Int := [0,1,2,10,11,12,13,14,15,16,17,18,19,20,21]
def requiredD794 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS794 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem794_eq : pairedProblem rows794 cols794 requiredD794 requiredS794 =
    MomentData.problem794 := by rfl
theorem leaf794 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows794++rows794))
    (hc : (q.map Prod.snd).Perm (cols794++cols794))
    (hd : ∀ k ∈ requiredD794, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS794, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows794 cols794 requiredD794 requiredS794
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem794_eq] at model
  exact MomentData.excluded794 ds ss model
def rows795 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols795 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD795 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS795 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,44]
theorem problem795_eq : pairedProblem rows795 cols795 requiredD795 requiredS795 =
    MomentData.problem795 := by rfl
theorem leaf795 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows795++rows795))
    (hc : (q.map Prod.snd).Perm (cols795++cols795))
    (hd : ∀ k ∈ requiredD795, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS795, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows795 cols795 requiredD795 requiredS795
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem795_eq] at model
  exact MomentData.excluded795 ds ss model
def rows796 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def cols796 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD796 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS796 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,46]
theorem problem796_eq : pairedProblem rows796 cols796 requiredD796 requiredS796 =
    MomentData.problem796 := by rfl
theorem leaf796 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows796++rows796))
    (hc : (q.map Prod.snd).Perm (cols796++cols796))
    (hd : ∀ k ∈ requiredD796, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS796, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows796 cols796 requiredD796 requiredS796
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem796_eq] at model
  exact MomentData.excluded796 ds ss model
def rows797 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,18,19,29]
def cols797 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,18,19,29]
def requiredD797 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS797 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,48]
theorem problem797_eq : pairedProblem rows797 cols797 requiredD797 requiredS797 =
    MomentData.problem797 := by rfl
theorem leaf797 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows797++rows797))
    (hc : (q.map Prod.snd).Perm (cols797++cols797))
    (hd : ∀ k ∈ requiredD797, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS797, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows797 cols797 requiredD797 requiredS797
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem797_eq] at model
  exact MomentData.excluded797 ds ss model
def rows798 : List Int := [0,2,4,6,8,10,13,15,17,19,21,23,25,27,29]
def cols798 : List Int := [0,2,4,6,8,10,13,15,17,19,21,23,25,27,29]
def requiredD798 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS798 : List Int := [13,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem798_eq : pairedProblem rows798 cols798 requiredD798 requiredS798 =
    MomentData.problem798 := by rfl
theorem leaf798 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows798++rows798))
    (hc : (q.map Prod.snd).Perm (cols798++cols798))
    (hd : ∀ k ∈ requiredD798, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS798, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows798 cols798 requiredD798 requiredS798
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem798_eq] at model
  exact MomentData.excluded798 ds ss model
def rows799 : List Int := [1,3,5,7,9,11,14,16,18,20,22,24,26,28,29]
def cols799 : List Int := [1,3,5,7,9,11,14,16,18,20,22,24,26,28,29]
def requiredD799 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS799 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem799_eq : pairedProblem rows799 cols799 requiredD799 requiredS799 =
    MomentData.problem799 := by rfl
theorem leaf799 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows799++rows799))
    (hc : (q.map Prod.snd).Perm (cols799++cols799))
    (hd : ∀ k ∈ requiredD799, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS799, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows799 cols799 requiredD799 requiredS799
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem799_eq] at model
  exact MomentData.excluded799 ds ss model
def rows800 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols800 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD800 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS800 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem800_eq : pairedProblem rows800 cols800 requiredD800 requiredS800 =
    MomentData.problem800 := by rfl
theorem leaf800 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows800++rows800))
    (hc : (q.map Prod.snd).Perm (cols800++cols800))
    (hd : ∀ k ∈ requiredD800, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS800, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows800 cols800 requiredD800 requiredS800
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem800_eq] at model
  exact MomentData.excluded800 ds ss model
def rows801 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols801 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD801 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS801 : List Int := [17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem801_eq : pairedProblem rows801 cols801 requiredD801 requiredS801 =
    MomentData.problem801 := by rfl
theorem leaf801 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows801++rows801))
    (hc : (q.map Prod.snd).Perm (cols801++cols801))
    (hd : ∀ k ∈ requiredD801, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS801, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows801 cols801 requiredD801 requiredS801
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem801_eq] at model
  exact MomentData.excluded801 ds ss model
def rows802 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols802 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD802 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS802 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,42]
theorem problem802_eq : pairedProblem rows802 cols802 requiredD802 requiredS802 =
    MomentData.problem802 := by rfl
theorem leaf802 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows802++rows802))
    (hc : (q.map Prod.snd).Perm (cols802++cols802))
    (hd : ∀ k ∈ requiredD802, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS802, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows802 cols802 requiredD802 requiredS802
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem802_eq] at model
  exact MomentData.excluded802 ds ss model
def rows803 : List Int := [0,1,3,5,7,9,11,13,16,18,20,22,24,26,28]
def cols803 : List Int := [0,1,3,5,7,9,11,13,16,18,20,22,24,26,28]
def requiredD803 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS803 : List Int := [17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem803_eq : pairedProblem rows803 cols803 requiredD803 requiredS803 =
    MomentData.problem803 := by rfl
theorem leaf803 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows803++rows803))
    (hc : (q.map Prod.snd).Perm (cols803++cols803))
    (hd : ∀ k ∈ requiredD803, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS803, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows803 cols803 requiredD803 requiredS803
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem803_eq] at model
  exact MomentData.excluded803 ds ss model
def rows804 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,28,29]
def cols804 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,28,29]
def requiredD804 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS804 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem804_eq : pairedProblem rows804 cols804 requiredD804 requiredS804 =
    MomentData.problem804 := by rfl
theorem leaf804 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows804++rows804))
    (hc : (q.map Prod.snd).Perm (cols804++cols804))
    (hd : ∀ k ∈ requiredD804, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS804, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows804 cols804 requiredD804 requiredS804
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem804_eq] at model
  exact MomentData.excluded804 ds ss model
def rows805 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def cols805 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def requiredD805 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS805 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem805_eq : pairedProblem rows805 cols805 requiredD805 requiredS805 =
    MomentData.problem805 := by rfl
theorem leaf805 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows805++rows805))
    (hc : (q.map Prod.snd).Perm (cols805++cols805))
    (hd : ∀ k ∈ requiredD805, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS805, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows805 cols805 requiredD805 requiredS805
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem805_eq] at model
  exact MomentData.excluded805 ds ss model
def rows806 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def cols806 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def requiredD806 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS806 : List Int := [16,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem806_eq : pairedProblem rows806 cols806 requiredD806 requiredS806 =
    MomentData.problem806 := by rfl
theorem leaf806 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows806++rows806))
    (hc : (q.map Prod.snd).Perm (cols806++cols806))
    (hd : ∀ k ∈ requiredD806, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS806, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows806 cols806 requiredD806 requiredS806
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem806_eq] at model
  exact MomentData.excluded806 ds ss model
def rows807 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def cols807 : List Int := [0,2,4,6,8,10,12,14,17,19,21,23,25,27,29]
def requiredD807 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS807 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem807_eq : pairedProblem rows807 cols807 requiredD807 requiredS807 =
    MomentData.problem807 := by rfl
theorem leaf807 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows807++rows807))
    (hc : (q.map Prod.snd).Perm (cols807++cols807))
    (hd : ∀ k ∈ requiredD807, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS807, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows807 cols807 requiredD807 requiredS807
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem807_eq] at model
  exact MomentData.excluded807 ds ss model
def rows808 : List Int := [0,1,3,5,7,9,11,13,15,18,20,22,24,26,28]
def cols808 : List Int := [0,1,3,5,7,9,11,13,15,18,20,22,24,26,28]
def requiredD808 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS808 : List Int := [18,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem808_eq : pairedProblem rows808 cols808 requiredD808 requiredS808 =
    MomentData.problem808 := by rfl
theorem leaf808 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows808++rows808))
    (hc : (q.map Prod.snd).Perm (cols808++cols808))
    (hd : ∀ k ∈ requiredD808, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS808, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows808 cols808 requiredD808 requiredS808
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem808_eq] at model
  exact MomentData.excluded808 ds ss model
def rows809 : List Int := [0,2,4,6,8,10,12,14,16,19,21,23,25,27,29]
def cols809 : List Int := [0,2,4,6,8,10,12,14,16,19,21,23,25,27,29]
def requiredD809 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS809 : List Int := [18,19,21,23,25,27,29,31,33,35,37,39,41,43,45]
theorem problem809_eq : pairedProblem rows809 cols809 requiredD809 requiredS809 =
    MomentData.problem809 := by rfl
theorem leaf809 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows809++rows809))
    (hc : (q.map Prod.snd).Perm (cols809++cols809))
    (hd : ∀ k ∈ requiredD809, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS809, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows809 cols809 requiredD809 requiredS809
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem809_eq] at model
  exact MomentData.excluded809 ds ss model
def rows810 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def cols810 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD810 : List Int := [-19,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS810 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,48]
theorem problem810_eq : pairedProblem rows810 cols810 requiredD810 requiredS810 =
    MomentData.problem810 := by rfl
theorem leaf810 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows810++rows810))
    (hc : (q.map Prod.snd).Perm (cols810++cols810))
    (hd : ∀ k ∈ requiredD810, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS810, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows810 cols810 requiredD810 requiredS810
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem810_eq] at model
  exact MomentData.excluded810 ds ss model
def rows811 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def cols811 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD811 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS811 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem811_eq : pairedProblem rows811 cols811 requiredD811 requiredS811 =
    MomentData.problem811 := by rfl
theorem leaf811 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows811++rows811))
    (hc : (q.map Prod.snd).Perm (cols811++cols811))
    (hd : ∀ k ∈ requiredD811, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS811, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows811 cols811 requiredD811 requiredS811
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem811_eq] at model
  exact MomentData.excluded811 ds ss model
def rows812 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,24]
def cols812 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD812 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS812 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem812_eq : pairedProblem rows812 cols812 requiredD812 requiredS812 =
    MomentData.problem812 := by rfl
theorem leaf812 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows812++rows812))
    (hc : (q.map Prod.snd).Perm (cols812++cols812))
    (hd : ∀ k ∈ requiredD812, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS812, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows812 cols812 requiredD812 requiredS812
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem812_eq] at model
  exact MomentData.excluded812 ds ss model
def rows813 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,29]
def cols813 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,29]
def requiredD813 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS813 : List Int := [10,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem813_eq : pairedProblem rows813 cols813 requiredD813 requiredS813 =
    MomentData.problem813 := by rfl
theorem leaf813 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows813++rows813))
    (hc : (q.map Prod.snd).Perm (cols813++cols813))
    (hd : ∀ k ∈ requiredD813, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS813, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows813 cols813 requiredD813 requiredS813
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem813_eq] at model
  exact MomentData.excluded813 ds ss model
def rows814 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23]
def cols814 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,22,23]
def requiredD814 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS814 : List Int := [12,26,27,28,29,30,31,32,33,34,35,36,37,38,39]
theorem problem814_eq : pairedProblem rows814 cols814 requiredD814 requiredS814 =
    MomentData.problem814 := by rfl
theorem leaf814 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows814++rows814))
    (hc : (q.map Prod.snd).Perm (cols814++cols814))
    (hd : ∀ k ∈ requiredD814, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS814, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows814 cols814 requiredD814 requiredS814
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem814_eq] at model
  exact MomentData.excluded814 ds ss model
def rows815 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols815 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD815 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS815 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem815_eq : pairedProblem rows815 cols815 requiredD815 requiredS815 =
    MomentData.problem815 := by rfl
theorem leaf815 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows815++rows815))
    (hc : (q.map Prod.snd).Perm (cols815++cols815))
    (hd : ∀ k ∈ requiredD815, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS815, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows815 cols815 requiredD815 requiredS815
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem815_eq] at model
  exact MomentData.excluded815 ds ss model
def rows816 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols816 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD816 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS816 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem816_eq : pairedProblem rows816 cols816 requiredD816 requiredS816 =
    MomentData.problem816 := by rfl
theorem leaf816 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows816++rows816))
    (hc : (q.map Prod.snd).Perm (cols816++cols816))
    (hd : ∀ k ∈ requiredD816, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS816, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows816 cols816 requiredD816 requiredS816
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem816_eq] at model
  exact MomentData.excluded816 ds ss model
def rows817 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols817 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD817 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS817 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem817_eq : pairedProblem rows817 cols817 requiredD817 requiredS817 =
    MomentData.problem817 := by rfl
theorem leaf817 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows817++rows817))
    (hc : (q.map Prod.snd).Perm (cols817++cols817))
    (hd : ∀ k ∈ requiredD817, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS817, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows817 cols817 requiredD817 requiredS817
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem817_eq] at model
  exact MomentData.excluded817 ds ss model
def rows818 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols818 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD818 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS818 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem818_eq : pairedProblem rows818 cols818 requiredD818 requiredS818 =
    MomentData.problem818 := by rfl
theorem leaf818 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows818++rows818))
    (hc : (q.map Prod.snd).Perm (cols818++cols818))
    (hd : ∀ k ∈ requiredD818, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS818, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows818 cols818 requiredD818 requiredS818
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem818_eq] at model
  exact MomentData.excluded818 ds ss model
def rows819 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols819 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD819 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS819 : List Int := [11,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem819_eq : pairedProblem rows819 cols819 requiredD819 requiredS819 =
    MomentData.problem819 := by rfl
theorem leaf819 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows819++rows819))
    (hc : (q.map Prod.snd).Perm (cols819++cols819))
    (hd : ∀ k ∈ requiredD819, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS819, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows819 cols819 requiredD819 requiredS819
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem819_eq] at model
  exact MomentData.excluded819 ds ss model
def rows820 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols820 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD820 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS820 : List Int := [25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem820_eq : pairedProblem rows820 cols820 requiredD820 requiredS820 =
    MomentData.problem820 := by rfl
theorem leaf820 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows820++rows820))
    (hc : (q.map Prod.snd).Perm (cols820++cols820))
    (hd : ∀ k ∈ requiredD820, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS820, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows820 cols820 requiredD820 requiredS820
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem820_eq] at model
  exact MomentData.excluded820 ds ss model
def rows821 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols821 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD821 : List Int := [-21,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,21]
def requiredS821 : List Int := [11,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem821_eq : pairedProblem rows821 cols821 requiredD821 requiredS821 =
    MomentData.problem821 := by rfl
theorem leaf821 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows821++rows821))
    (hc : (q.map Prod.snd).Perm (cols821++cols821))
    (hd : ∀ k ∈ requiredD821, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS821, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows821 cols821 requiredD821 requiredS821
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem821_eq] at model
  exact MomentData.excluded821 ds ss model
def rows822 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols822 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD822 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS822 : List Int := [11,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem822_eq : pairedProblem rows822 cols822 requiredD822 requiredS822 =
    MomentData.problem822 := by rfl
theorem leaf822 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows822++rows822))
    (hc : (q.map Prod.snd).Perm (cols822++cols822))
    (hd : ∀ k ∈ requiredD822, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS822, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows822 cols822 requiredD822 requiredS822
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem822_eq] at model
  exact MomentData.excluded822 ds ss model
def rows823 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols823 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD823 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS823 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem823_eq : pairedProblem rows823 cols823 requiredD823 requiredS823 =
    MomentData.problem823 := by rfl
theorem leaf823 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows823++rows823))
    (hc : (q.map Prod.snd).Perm (cols823++cols823))
    (hd : ∀ k ∈ requiredD823, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS823, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows823 cols823 requiredD823 requiredS823
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem823_eq] at model
  exact MomentData.excluded823 ds ss model
def rows824 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols824 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD824 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS824 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem824_eq : pairedProblem rows824 cols824 requiredD824 requiredS824 =
    MomentData.problem824 := by rfl
theorem leaf824 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows824++rows824))
    (hc : (q.map Prod.snd).Perm (cols824++cols824))
    (hd : ∀ k ∈ requiredD824, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS824, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows824 cols824 requiredD824 requiredS824
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem824_eq] at model
  exact MomentData.excluded824 ds ss model
def rows825 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols825 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD825 : List Int := [-19,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS825 : List Int := [10,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem825_eq : pairedProblem rows825 cols825 requiredD825 requiredS825 =
    MomentData.problem825 := by rfl
theorem leaf825 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows825++rows825))
    (hc : (q.map Prod.snd).Perm (cols825++cols825))
    (hd : ∀ k ∈ requiredD825, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS825, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows825 cols825 requiredD825 requiredS825
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem825_eq] at model
  exact MomentData.excluded825 ds ss model
def rows826 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols826 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD826 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS826 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem826_eq : pairedProblem rows826 cols826 requiredD826 requiredS826 =
    MomentData.problem826 := by rfl
theorem leaf826 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows826++rows826))
    (hc : (q.map Prod.snd).Perm (cols826++cols826))
    (hd : ∀ k ∈ requiredD826, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS826, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows826 cols826 requiredD826 requiredS826
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem826_eq] at model
  exact MomentData.excluded826 ds ss model
def rows827 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols827 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD827 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS827 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem827_eq : pairedProblem rows827 cols827 requiredD827 requiredS827 =
    MomentData.problem827 := by rfl
theorem leaf827 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows827++rows827))
    (hc : (q.map Prod.snd).Perm (cols827++cols827))
    (hd : ∀ k ∈ requiredD827, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS827, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows827 cols827 requiredD827 requiredS827
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem827_eq] at model
  exact MomentData.excluded827 ds ss model
def rows828 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols828 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD828 : List Int := [-21,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,21]
def requiredS828 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,47]
theorem problem828_eq : pairedProblem rows828 cols828 requiredD828 requiredS828 =
    MomentData.problem828 := by rfl
theorem leaf828 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows828++rows828))
    (hc : (q.map Prod.snd).Perm (cols828++cols828))
    (hd : ∀ k ∈ requiredD828, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS828, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows828 cols828 requiredD828 requiredS828
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem828_eq] at model
  exact MomentData.excluded828 ds ss model
def rows829 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols829 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD829 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS829 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem829_eq : pairedProblem rows829 cols829 requiredD829 requiredS829 =
    MomentData.problem829 := by rfl
theorem leaf829 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows829++rows829))
    (hc : (q.map Prod.snd).Perm (cols829++cols829))
    (hd : ∀ k ∈ requiredD829, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS829, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows829 cols829 requiredD829 requiredS829
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem829_eq] at model
  exact MomentData.excluded829 ds ss model
def rows830 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols830 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD830 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS830 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem830_eq : pairedProblem rows830 cols830 requiredD830 requiredS830 =
    MomentData.problem830 := by rfl
theorem leaf830 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows830++rows830))
    (hc : (q.map Prod.snd).Perm (cols830++cols830))
    (hd : ∀ k ∈ requiredD830, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS830, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows830 cols830 requiredD830 requiredS830
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem830_eq] at model
  exact MomentData.excluded830 ds ss model
def rows831 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols831 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD831 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS831 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem831_eq : pairedProblem rows831 cols831 requiredD831 requiredS831 =
    MomentData.problem831 := by rfl
theorem leaf831 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows831++rows831))
    (hc : (q.map Prod.snd).Perm (cols831++cols831))
    (hd : ∀ k ∈ requiredD831, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS831, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows831 cols831 requiredD831 requiredS831
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem831_eq] at model
  exact MomentData.excluded831 ds ss model
def rows832 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols832 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD832 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS832 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem832_eq : pairedProblem rows832 cols832 requiredD832 requiredS832 =
    MomentData.problem832 := by rfl
theorem leaf832 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows832++rows832))
    (hc : (q.map Prod.snd).Perm (cols832++cols832))
    (hd : ∀ k ∈ requiredD832, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS832, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows832 cols832 requiredD832 requiredS832
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem832_eq] at model
  exact MomentData.excluded832 ds ss model
def rows833 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21]
def cols833 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,19,20,21]
def requiredD833 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS833 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem833_eq : pairedProblem rows833 cols833 requiredD833 requiredS833 =
    MomentData.problem833 := by rfl
theorem leaf833 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows833++rows833))
    (hc : (q.map Prod.snd).Perm (cols833++cols833))
    (hd : ∀ k ∈ requiredD833, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS833, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows833 cols833 requiredD833 requiredS833
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem833_eq] at model
  exact MomentData.excluded833 ds ss model
def rows834 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def cols834 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD834 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS834 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,46]
theorem problem834_eq : pairedProblem rows834 cols834 requiredD834 requiredS834 =
    MomentData.problem834 := by rfl
theorem leaf834 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows834++rows834))
    (hc : (q.map Prod.snd).Perm (cols834++cols834))
    (hd : ∀ k ∈ requiredD834, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS834, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows834 cols834 requiredD834 requiredS834
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem834_eq] at model
  exact MomentData.excluded834 ds ss model
def rows835 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def cols835 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def requiredD835 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS835 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,48]
theorem problem835_eq : pairedProblem rows835 cols835 requiredD835 requiredS835 =
    MomentData.problem835 := by rfl
theorem leaf835 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows835++rows835))
    (hc : (q.map Prod.snd).Perm (cols835++cols835))
    (hd : ∀ k ∈ requiredD835, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS835, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows835 cols835 requiredD835 requiredS835
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem835_eq] at model
  exact MomentData.excluded835 ds ss model
def rows836 : List Int := [0,2,3,5,6,9,12,15,18,21,23,24,25,27,28]
def cols836 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD836 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,8,10,13,16,19]
def requiredS836 : List Int := [11,14,17,20,22,23,26,29,32,35,38,41,44,47,50]
theorem problem836_eq : pairedProblem rows836 cols836 requiredD836 requiredS836 =
    MomentData.problem836 := by rfl
theorem leaf836 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows836++rows836))
    (hc : (q.map Prod.snd).Perm (cols836++cols836))
    (hd : ∀ k ∈ requiredD836, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS836, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows836 cols836 requiredD836 requiredS836
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem836_eq] at model
  exact MomentData.excluded836 ds ss model
def rows837 : List Int := [0,2,3,5,6,9,12,15,18,21,23,24,25,27,28]
def cols837 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD837 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS837 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem837_eq : pairedProblem rows837 cols837 requiredD837 requiredS837 =
    MomentData.problem837 := by rfl
theorem leaf837 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows837++rows837))
    (hc : (q.map Prod.snd).Perm (cols837++cols837))
    (hd : ∀ k ∈ requiredD837, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS837, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows837 cols837 requiredD837 requiredS837
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem837_eq] at model
  exact MomentData.excluded837 ds ss model
def rows838 : List Int := [0,2,3,5,6,9,12,15,18,21,23,24,25,27,28]
def cols838 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD838 : List Int := [-17,-14,-11,-8,-6,-5,-2,1,4,7,8,10,13,16,19]
def requiredS838 : List Int := [11,14,17,20,22,23,26,29,32,35,36,38,41,44,47]
theorem problem838_eq : pairedProblem rows838 cols838 requiredD838 requiredS838 =
    MomentData.problem838 := by rfl
theorem leaf838 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows838++rows838))
    (hc : (q.map Prod.snd).Perm (cols838++cols838))
    (hd : ∀ k ∈ requiredD838, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS838, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows838 cols838 requiredD838 requiredS838
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem838_eq] at model
  exact MomentData.excluded838 ds ss model
def rows839 : List Int := [0,2,3,6,9,12,15,18,19,21,22,24,25,27,28]
def cols839 : List Int := [0,2,3,6,9,12,15,18,19,21,22,24,25,27,28]
def requiredD839 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS839 : List Int := [6,9,12,15,18,21,24,27,30,33,34,36,39,42,45]
theorem problem839_eq : pairedProblem rows839 cols839 requiredD839 requiredS839 =
    MomentData.problem839 := by rfl
theorem leaf839 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows839++rows839))
    (hc : (q.map Prod.snd).Perm (cols839++cols839))
    (hd : ∀ k ∈ requiredD839, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS839, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows839 cols839 requiredD839 requiredS839
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem839_eq] at model
  exact MomentData.excluded839 ds ss model
def rows840 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols840 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD840 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS840 : List Int := [7,10,13,16,19,22,25,28,31,34,35,37,40,43,46]
theorem problem840_eq : pairedProblem rows840 cols840 requiredD840 requiredS840 =
    MomentData.problem840 := by rfl
theorem leaf840 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows840++rows840))
    (hc : (q.map Prod.snd).Perm (cols840++cols840))
    (hd : ∀ k ∈ requiredD840, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS840, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows840 cols840 requiredD840 requiredS840
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem840_eq] at model
  exact MomentData.excluded840 ds ss model
def rows841 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols841 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD841 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS841 : List Int := [10,13,16,19,22,25,28,31,34,35,37,40,43,46]
theorem problem841_eq : pairedProblem rows841 cols841 requiredD841 requiredS841 =
    MomentData.problem841 := by rfl
theorem leaf841 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows841++rows841))
    (hc : (q.map Prod.snd).Perm (cols841++cols841))
    (hd : ∀ k ∈ requiredD841, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS841, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows841 cols841 requiredD841 requiredS841
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem841_eq] at model
  exact MomentData.excluded841 ds ss model
def rows842 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols842 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD842 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS842 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem842_eq : pairedProblem rows842 cols842 requiredD842 requiredS842 =
    MomentData.problem842 := by rfl
theorem leaf842 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows842++rows842))
    (hc : (q.map Prod.snd).Perm (cols842++cols842))
    (hd : ∀ k ∈ requiredD842, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS842, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows842 cols842 requiredD842 requiredS842
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem842_eq] at model
  exact MomentData.excluded842 ds ss model
def rows843 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols843 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD843 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS843 : List Int := [7,10,13,16,19,22,25,28,31,34,35,37,40,43]
theorem problem843_eq : pairedProblem rows843 cols843 requiredD843 requiredS843 =
    MomentData.problem843 := by rfl
theorem leaf843 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows843++rows843))
    (hc : (q.map Prod.snd).Perm (cols843++cols843))
    (hd : ∀ k ∈ requiredD843, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS843, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows843 cols843 requiredD843 requiredS843
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem843_eq] at model
  exact MomentData.excluded843 ds ss model
def rows844 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols844 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def requiredD844 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS844 : List Int := [9,12,15,18,21,24,27,30,33,36,37,39,42,45,48]
theorem problem844_eq : pairedProblem rows844 cols844 requiredD844 requiredS844 =
    MomentData.problem844 := by rfl
theorem leaf844 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows844++rows844))
    (hc : (q.map Prod.snd).Perm (cols844++cols844))
    (hd : ∀ k ∈ requiredD844, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS844, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows844 cols844 requiredD844 requiredS844
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem844_eq] at model
  exact MomentData.excluded844 ds ss model
def rows845 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols845 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def requiredD845 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS845 : List Int := [12,15,18,21,24,27,30,33,36,37,39,42,45,48]
theorem problem845_eq : pairedProblem rows845 cols845 requiredD845 requiredS845 =
    MomentData.problem845 := by rfl
theorem leaf845 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows845++rows845))
    (hc : (q.map Prod.snd).Perm (cols845++cols845))
    (hd : ∀ k ∈ requiredD845, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS845, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows845 cols845 requiredD845 requiredS845
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem845_eq] at model
  exact MomentData.excluded845 ds ss model
def rows846 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols846 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def requiredD846 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS846 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem846_eq : pairedProblem rows846 cols846 requiredD846 requiredS846 =
    MomentData.problem846 := by rfl
theorem leaf846 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows846++rows846))
    (hc : (q.map Prod.snd).Perm (cols846++cols846))
    (hd : ∀ k ∈ requiredD846, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS846, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows846 cols846 requiredD846 requiredS846
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem846_eq] at model
  exact MomentData.excluded846 ds ss model
def rows847 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols847 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def requiredD847 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS847 : List Int := [9,12,15,18,21,24,27,30,33,36,37,39,42,45]
theorem problem847_eq : pairedProblem rows847 cols847 requiredD847 requiredS847 =
    MomentData.problem847 := by rfl
theorem leaf847 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows847++rows847))
    (hc : (q.map Prod.snd).Perm (cols847++cols847))
    (hd : ∀ k ∈ requiredD847, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS847, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows847 cols847 requiredD847 requiredS847
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem847_eq] at model
  exact MomentData.excluded847 ds ss model
def rows848 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols848 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def requiredD848 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,8,10,13,16,19]
def requiredS848 : List Int := [8,11,14,17,20,23,26,29,32,35,36,38,41,44,47]
theorem problem848_eq : pairedProblem rows848 cols848 requiredD848 requiredS848 =
    MomentData.problem848 := by rfl
theorem leaf848 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows848++rows848))
    (hc : (q.map Prod.snd).Perm (cols848++cols848))
    (hd : ∀ k ∈ requiredD848, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS848, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows848 cols848 requiredD848 requiredS848
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem848_eq] at model
  exact MomentData.excluded848 ds ss model
def rows849 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols849 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def requiredD849 : List Int := [-17,-14,-11,-8,-6,-5,-2,1,4,7,8,10,13,16,19]
def requiredS849 : List Int := [11,14,17,20,22,23,26,29,32,35,36,38,41,44,47]
theorem problem849_eq : pairedProblem rows849 cols849 requiredD849 requiredS849 =
    MomentData.problem849 := by rfl
theorem leaf849 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows849++rows849))
    (hc : (q.map Prod.snd).Perm (cols849++cols849))
    (hd : ∀ k ∈ requiredD849, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS849, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows849 cols849 requiredD849 requiredS849
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem849_eq] at model
  exact MomentData.excluded849 ds ss model
def rows850 : List Int := [0,2,3,5,6,9,12,15,18,21,22,24,25,27,28]
def cols850 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def requiredD850 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,4,7,10,13,16,19,22]
def requiredS850 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem850_eq : pairedProblem rows850 cols850 requiredD850 requiredS850 =
    MomentData.problem850 := by rfl
theorem leaf850 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows850++rows850))
    (hc : (q.map Prod.snd).Perm (cols850++cols850))
    (hd : ∀ k ∈ requiredD850, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS850, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows850 cols850 requiredD850 requiredS850
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem850_eq] at model
  exact MomentData.excluded850 ds ss model
def rows851 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols851 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD851 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS851 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46,49]
theorem problem851_eq : pairedProblem rows851 cols851 requiredD851 requiredS851 =
    MomentData.problem851 := by rfl
theorem leaf851 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows851++rows851))
    (hc : (q.map Prod.snd).Perm (cols851++cols851))
    (hd : ∀ k ∈ requiredD851, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS851, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows851 cols851 requiredD851 requiredS851
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem851_eq] at model
  exact MomentData.excluded851 ds ss model
def rows852 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols852 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD852 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS852 : List Int := [13,16,19,21,22,25,28,31,34,37,40,43,46,49]
theorem problem852_eq : pairedProblem rows852 cols852 requiredD852 requiredS852 =
    MomentData.problem852 := by rfl
theorem leaf852 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows852++rows852))
    (hc : (q.map Prod.snd).Perm (cols852++cols852))
    (hd : ∀ k ∈ requiredD852, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS852, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows852 cols852 requiredD852 requiredS852
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem852_eq] at model
  exact MomentData.excluded852 ds ss model
def rows853 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols853 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD853 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS853 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem853_eq : pairedProblem rows853 cols853 requiredD853 requiredS853 =
    MomentData.problem853 := by rfl
theorem leaf853 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows853++rows853))
    (hc : (q.map Prod.snd).Perm (cols853++cols853))
    (hd : ∀ k ∈ requiredD853, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS853, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows853 cols853 requiredD853 requiredS853
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem853_eq] at model
  exact MomentData.excluded853 ds ss model
def rows854 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols854 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD854 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS854 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem854_eq : pairedProblem rows854 cols854 requiredD854 requiredS854 =
    MomentData.problem854 := by rfl
theorem leaf854 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows854++rows854))
    (hc : (q.map Prod.snd).Perm (cols854++cols854))
    (hd : ∀ k ∈ requiredD854, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS854, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows854 cols854 requiredD854 requiredS854
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem854_eq] at model
  exact MomentData.excluded854 ds ss model
def rows855 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def cols855 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def requiredD855 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS855 : List Int := [12,15,18,21,23,24,27,30,33,36,39,42,45,48,51]
theorem problem855_eq : pairedProblem rows855 cols855 requiredD855 requiredS855 =
    MomentData.problem855 := by rfl
theorem leaf855 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows855++rows855))
    (hc : (q.map Prod.snd).Perm (cols855++cols855))
    (hd : ∀ k ∈ requiredD855, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS855, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows855 cols855 requiredD855 requiredS855
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem855_eq] at model
  exact MomentData.excluded855 ds ss model
def rows856 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def cols856 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def requiredD856 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS856 : List Int := [15,18,21,23,24,27,30,33,36,39,42,45,48,51]
theorem problem856_eq : pairedProblem rows856 cols856 requiredD856 requiredS856 =
    MomentData.problem856 := by rfl
theorem leaf856 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows856++rows856))
    (hc : (q.map Prod.snd).Perm (cols856++cols856))
    (hd : ∀ k ∈ requiredD856, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS856, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows856 cols856 requiredD856 requiredS856
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem856_eq] at model
  exact MomentData.excluded856 ds ss model
def rows857 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def cols857 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def requiredD857 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS857 : List Int := [12,15,18,21,24,27,30,33,36,39,42,45,48,51]
theorem problem857_eq : pairedProblem rows857 cols857 requiredD857 requiredS857 =
    MomentData.problem857 := by rfl
theorem leaf857 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows857++rows857))
    (hc : (q.map Prod.snd).Perm (cols857++cols857))
    (hd : ∀ k ∈ requiredD857, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS857, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows857 cols857 requiredD857 requiredS857
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem857_eq] at model
  exact MomentData.excluded857 ds ss model
def rows858 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def cols858 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,25,27,28]
def requiredD858 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS858 : List Int := [12,15,18,21,23,24,27,30,33,36,39,42,45,48]
theorem problem858_eq : pairedProblem rows858 cols858 requiredD858 requiredS858 =
    MomentData.problem858 := by rfl
theorem leaf858 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows858++rows858))
    (hc : (q.map Prod.snd).Perm (cols858++cols858))
    (hd : ∀ k ∈ requiredD858, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS858, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows858 cols858 requiredD858 requiredS858
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem858_eq] at model
  exact MomentData.excluded858 ds ss model
def rows859 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,29]
def cols859 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,29]
def requiredD859 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS859 : List Int := [5,9,13,17,21,25,28,29,33,37,41,45,49,53]
theorem problem859_eq : pairedProblem rows859 cols859 requiredD859 requiredS859 =
    MomentData.problem859 := by rfl
theorem leaf859 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows859++rows859))
    (hc : (q.map Prod.snd).Perm (cols859++cols859))
    (hd : ∀ k ∈ requiredD859, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS859, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows859 cols859 requiredD859 requiredS859
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem859_eq] at model
  exact MomentData.excluded859 ds ss model
def rows860 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def cols860 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def requiredD860 : List Int := [-24,-20,-16,-12,-8,-4,0,4,8,12,16,20,24]
def requiredS860 : List Int := [3,7,11,15,19,23,27,30,31,35,39,43,47,51,55]
theorem problem860_eq : pairedProblem rows860 cols860 requiredD860 requiredS860 =
    MomentData.problem860 := by rfl
theorem leaf860 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows860++rows860))
    (hc : (q.map Prod.snd).Perm (cols860++cols860))
    (hd : ∀ k ∈ requiredD860, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS860, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows860 cols860 requiredD860 requiredS860
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem860_eq] at model
  exact MomentData.excluded860 ds ss model
def rows861 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def cols861 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def requiredD861 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS861 : List Int := [7,11,15,19,23,27,30,31,35,39,43,47,51,55]
theorem problem861_eq : pairedProblem rows861 cols861 requiredD861 requiredS861 =
    MomentData.problem861 := by rfl
theorem leaf861 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows861++rows861))
    (hc : (q.map Prod.snd).Perm (cols861++cols861))
    (hd : ∀ k ∈ requiredD861, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS861, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows861 cols861 requiredD861 requiredS861
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem861_eq] at model
  exact MomentData.excluded861 ds ss model
def rows862 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def cols862 : List Int := [0,3,4,7,8,11,12,15,16,19,20,23,24,27,28]
def requiredD862 : List Int := [-24,-20,-16,-12,-8,-4,-3,0,3,4,8,12,16,20,24]
def requiredS862 : List Int := [3,7,11,15,19,23,27,30,31,35,39,43,47,51]
theorem problem862_eq : pairedProblem rows862 cols862 requiredD862 requiredS862 =
    MomentData.problem862 := by rfl
theorem leaf862 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows862++rows862))
    (hc : (q.map Prod.snd).Perm (cols862++cols862))
    (hd : ∀ k ∈ requiredD862, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS862, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows862 cols862 requiredD862 requiredS862
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem862_eq] at model
  exact MomentData.excluded862 ds ss model
def rows863 : List Int := [1,2,4,5,7,8,10,11,14,17,20,23,26,27,29]
def cols863 : List Int := [1,2,4,5,7,8,10,11,14,17,20,23,26,27,29]
def requiredD863 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS863 : List Int := [13,16,19,22,24,25,28,31,34,37,40,43,46,49,52]
theorem problem863_eq : pairedProblem rows863 cols863 requiredD863 requiredS863 =
    MomentData.problem863 := by rfl
theorem leaf863 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows863++rows863))
    (hc : (q.map Prod.snd).Perm (cols863++cols863))
    (hd : ∀ k ∈ requiredD863, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS863, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows863 cols863 requiredD863 requiredS863
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem863_eq] at model
  exact MomentData.excluded863 ds ss model
def rows864 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols864 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD864 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS864 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,42,44]
theorem problem864_eq : pairedProblem rows864 cols864 requiredD864 requiredS864 =
    MomentData.problem864 := by rfl
theorem leaf864 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows864++rows864))
    (hc : (q.map Prod.snd).Perm (cols864++cols864))
    (hd : ∀ k ∈ requiredD864, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS864, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows864 cols864 requiredD864 requiredS864
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem864_eq] at model
  exact MomentData.excluded864 ds ss model
def rows865 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols865 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD865 : List Int := [-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14]
def requiredS865 : List Int := [12,16,18,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem865_eq : pairedProblem rows865 cols865 requiredD865 requiredS865 =
    MomentData.problem865 := by rfl
theorem leaf865 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows865++rows865))
    (hc : (q.map Prod.snd).Perm (cols865++cols865))
    (hd : ∀ k ∈ requiredD865, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS865, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows865 cols865 requiredD865 requiredS865
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem865_eq] at model
  exact MomentData.excluded865 ds ss model
def rows866 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols866 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD866 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS866 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem866_eq : pairedProblem rows866 cols866 requiredD866 requiredS866 =
    MomentData.problem866 := by rfl
theorem leaf866 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows866++rows866))
    (hc : (q.map Prod.snd).Perm (cols866++cols866))
    (hd : ∀ k ∈ requiredD866, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS866, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows866 cols866 requiredD866 requiredS866
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem866_eq] at model
  exact MomentData.excluded866 ds ss model
def rows867 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols867 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD867 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS867 : List Int := [14,16,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem867_eq : pairedProblem rows867 cols867 requiredD867 requiredS867 =
    MomentData.problem867 := by rfl
theorem leaf867 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows867++rows867))
    (hc : (q.map Prod.snd).Perm (cols867++cols867))
    (hd : ∀ k ∈ requiredD867, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS867, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows867 cols867 requiredD867 requiredS867
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem867_eq] at model
  exact MomentData.excluded867 ds ss model
def rows868 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols868 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD868 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS868 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem868_eq : pairedProblem rows868 cols868 requiredD868 requiredS868 =
    MomentData.problem868 := by rfl
theorem leaf868 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows868++rows868))
    (hc : (q.map Prod.snd).Perm (cols868++cols868))
    (hd : ∀ k ∈ requiredD868, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS868, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows868 cols868 requiredD868 requiredS868
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem868_eq] at model
  exact MomentData.excluded868 ds ss model
def rows869 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols869 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD869 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS869 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40]
theorem problem869_eq : pairedProblem rows869 cols869 requiredD869 requiredS869 =
    MomentData.problem869 := by rfl
theorem leaf869 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows869++rows869))
    (hc : (q.map Prod.snd).Perm (cols869++cols869))
    (hd : ∀ k ∈ requiredD869, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS869, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows869 cols869 requiredD869 requiredS869
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem869_eq] at model
  exact MomentData.excluded869 ds ss model
def rows870 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols870 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD870 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS870 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,40,42,46]
theorem problem870_eq : pairedProblem rows870 cols870 requiredD870 requiredS870 =
    MomentData.problem870 := by rfl
theorem leaf870 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows870++rows870))
    (hc : (q.map Prod.snd).Perm (cols870++cols870))
    (hd : ∀ k ∈ requiredD870, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS870, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows870 cols870 requiredD870 requiredS870
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem870_eq] at model
  exact MomentData.excluded870 ds ss model
def rows871 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols871 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD871 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS871 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem871_eq : pairedProblem rows871 cols871 requiredD871 requiredS871 =
    MomentData.problem871 := by rfl
theorem leaf871 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows871++rows871))
    (hc : (q.map Prod.snd).Perm (cols871++cols871))
    (hd : ∀ k ∈ requiredD871, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS871, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows871 cols871 requiredD871 requiredS871
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem871_eq] at model
  exact MomentData.excluded871 ds ss model
def rows872 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols872 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD872 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS872 : List Int := [12,16,20,22,24,26,28,30,32,34,36,38,40,44,48]
theorem problem872_eq : pairedProblem rows872 cols872 requiredD872 requiredS872 =
    MomentData.problem872 := by rfl
theorem leaf872 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows872++rows872))
    (hc : (q.map Prod.snd).Perm (cols872++cols872))
    (hd : ∀ k ∈ requiredD872, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS872, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows872 cols872 requiredD872 requiredS872
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem872_eq] at model
  exact MomentData.excluded872 ds ss model
def rows873 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols873 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD873 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS873 : List Int := [12,16,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem873_eq : pairedProblem rows873 cols873 requiredD873 requiredS873 =
    MomentData.problem873 := by rfl
theorem leaf873 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows873++rows873))
    (hc : (q.map Prod.snd).Perm (cols873++cols873))
    (hd : ∀ k ∈ requiredD873, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS873, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows873 cols873 requiredD873 requiredS873
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem873_eq] at model
  exact MomentData.excluded873 ds ss model
def rows874 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols874 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD874 : List Int := [-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18]
def requiredS874 : List Int := [8,12,16,20,22,24,26,28,30,32,34,36,40,44,48]
theorem problem874_eq : pairedProblem rows874 cols874 requiredD874 requiredS874 =
    MomentData.problem874 := by rfl
theorem leaf874 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows874++rows874))
    (hc : (q.map Prod.snd).Perm (cols874++cols874))
    (hd : ∀ k ∈ requiredD874, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS874, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows874 cols874 requiredD874 requiredS874
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem874_eq] at model
  exact MomentData.excluded874 ds ss model
def rows875 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols875 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD875 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS875 : List Int := [12,16,20,22,24,26,28,30,32,34,36,40,44,48]
theorem problem875_eq : pairedProblem rows875 cols875 requiredD875 requiredS875 =
    MomentData.problem875 := by rfl
theorem leaf875 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows875++rows875))
    (hc : (q.map Prod.snd).Perm (cols875++cols875))
    (hd : ∀ k ∈ requiredD875, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS875, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows875 cols875 requiredD875 requiredS875
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem875_eq] at model
  exact MomentData.excluded875 ds ss model
def rows876 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols876 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD876 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS876 : List Int := [12,16,20,22,24,26,28,30,32,34,36,40,44]
theorem problem876_eq : pairedProblem rows876 cols876 requiredD876 requiredS876 =
    MomentData.problem876 := by rfl
theorem leaf876 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows876++rows876))
    (hc : (q.map Prod.snd).Perm (cols876++cols876))
    (hd : ∀ k ∈ requiredD876, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS876, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows876 cols876 requiredD876 requiredS876
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem876_eq] at model
  exact MomentData.excluded876 ds ss model
def rows877 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols877 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD877 : List Int := [-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16]
def requiredS877 : List Int := [10,14,18,20,22,24,26,28,30,32,34,36,38,42,46]
theorem problem877_eq : pairedProblem rows877 cols877 requiredD877 requiredS877 =
    MomentData.problem877 := by rfl
theorem leaf877 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows877++rows877))
    (hc : (q.map Prod.snd).Perm (cols877++cols877))
    (hd : ∀ k ∈ requiredD877, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS877, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows877 cols877 requiredD877 requiredS877
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem877_eq] at model
  exact MomentData.excluded877 ds ss model
def rows878 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols878 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD878 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS878 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,42,46]
theorem problem878_eq : pairedProblem rows878 cols878 requiredD878 requiredS878 =
    MomentData.problem878 := by rfl
theorem leaf878 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows878++rows878))
    (hc : (q.map Prod.snd).Perm (cols878++cols878))
    (hd : ∀ k ∈ requiredD878, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS878, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows878 cols878 requiredD878 requiredS878
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem878_eq] at model
  exact MomentData.excluded878 ds ss model
def rows879 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols879 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD879 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS879 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,42]
theorem problem879_eq : pairedProblem rows879 cols879 requiredD879 requiredS879 =
    MomentData.problem879 := by rfl
theorem leaf879 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows879++rows879))
    (hc : (q.map Prod.snd).Perm (cols879++cols879))
    (hd : ∀ k ∈ requiredD879, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS879, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows879 cols879 requiredD879 requiredS879
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem879_eq] at model
  exact MomentData.excluded879 ds ss model
def rows880 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols880 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD880 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS880 : List Int := [10,14,18,22,24,26,28,30,32,34,36,38,42,46,50]
theorem problem880_eq : pairedProblem rows880 cols880 requiredD880 requiredS880 =
    MomentData.problem880 := by rfl
theorem leaf880 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows880++rows880))
    (hc : (q.map Prod.snd).Perm (cols880++cols880))
    (hd : ∀ k ∈ requiredD880, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS880, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows880 cols880 requiredD880 requiredS880
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem880_eq] at model
  exact MomentData.excluded880 ds ss model
def rows881 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols881 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD881 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS881 : List Int := [10,14,18,22,24,26,28,30,32,34,36,38,42,46]
theorem problem881_eq : pairedProblem rows881 cols881 requiredD881 requiredS881 =
    MomentData.problem881 := by rfl
theorem leaf881 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows881++rows881))
    (hc : (q.map Prod.snd).Perm (cols881++cols881))
    (hd : ∀ k ∈ requiredD881, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS881, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows881 cols881 requiredD881 requiredS881
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem881_eq] at model
  exact MomentData.excluded881 ds ss model
def rows882 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols882 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD882 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS882 : List Int := [8,12,16,20,24,26,28,30,32,34,36,40,44,48,52]
theorem problem882_eq : pairedProblem rows882 cols882 requiredD882 requiredS882 =
    MomentData.problem882 := by rfl
theorem leaf882 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows882++rows882))
    (hc : (q.map Prod.snd).Perm (cols882++cols882))
    (hd : ∀ k ∈ requiredD882, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS882, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows882 cols882 requiredD882 requiredS882
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem882_eq] at model
  exact MomentData.excluded882 ds ss model
def rows883 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols883 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD883 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS883 : List Int := [8,12,16,20,24,26,28,30,32,34,36,40,44,48]
theorem problem883_eq : pairedProblem rows883 cols883 requiredD883 requiredS883 =
    MomentData.problem883 := by rfl
theorem leaf883 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows883++rows883))
    (hc : (q.map Prod.snd).Perm (cols883++cols883))
    (hd : ∀ k ∈ requiredD883, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS883, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows883 cols883 requiredD883 requiredS883
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem883_eq] at model
  exact MomentData.excluded883 ds ss model
def rows884 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols884 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD884 : List Int := [-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22]
def requiredS884 : List Int := [4,8,12,16,20,24,26,28,30,32,36,40,44,48,52]
theorem problem884_eq : pairedProblem rows884 cols884 requiredD884 requiredS884 =
    MomentData.problem884 := by rfl
theorem leaf884 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows884++rows884))
    (hc : (q.map Prod.snd).Perm (cols884++cols884))
    (hd : ∀ k ∈ requiredD884, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS884, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows884 cols884 requiredD884 requiredS884
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem884_eq] at model
  exact MomentData.excluded884 ds ss model
def rows885 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols885 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD885 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS885 : List Int := [8,12,16,20,24,26,28,30,32,36,40,44,48,52]
theorem problem885_eq : pairedProblem rows885 cols885 requiredD885 requiredS885 =
    MomentData.problem885 := by rfl
theorem leaf885 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows885++rows885))
    (hc : (q.map Prod.snd).Perm (cols885++cols885))
    (hd : ∀ k ∈ requiredD885, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS885, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows885 cols885 requiredD885 requiredS885
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem885_eq] at model
  exact MomentData.excluded885 ds ss model
def rows886 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols886 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD886 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS886 : List Int := [8,12,16,20,24,26,28,30,32,36,40,44,48]
theorem problem886_eq : pairedProblem rows886 cols886 requiredD886 requiredS886 =
    MomentData.problem886 := by rfl
theorem leaf886 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows886++rows886))
    (hc : (q.map Prod.snd).Perm (cols886++cols886))
    (hd : ∀ k ∈ requiredD886, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS886, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows886 cols886 requiredD886 requiredS886
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem886_eq] at model
  exact MomentData.excluded886 ds ss model
def rows887 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols887 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD887 : List Int := [-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20]
def requiredS887 : List Int := [6,10,14,18,22,24,26,28,30,32,34,38,42,46,50]
theorem problem887_eq : pairedProblem rows887 cols887 requiredD887 requiredS887 =
    MomentData.problem887 := by rfl
theorem leaf887 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows887++rows887))
    (hc : (q.map Prod.snd).Perm (cols887++cols887))
    (hd : ∀ k ∈ requiredD887, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS887, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows887 cols887 requiredD887 requiredS887
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem887_eq] at model
  exact MomentData.excluded887 ds ss model
def rows888 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols888 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD888 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS888 : List Int := [10,14,18,22,24,26,28,30,32,34,38,42,46,50]
theorem problem888_eq : pairedProblem rows888 cols888 requiredD888 requiredS888 =
    MomentData.problem888 := by rfl
theorem leaf888 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows888++rows888))
    (hc : (q.map Prod.snd).Perm (cols888++cols888))
    (hd : ∀ k ∈ requiredD888, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS888, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows888 cols888 requiredD888 requiredS888
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem888_eq] at model
  exact MomentData.excluded888 ds ss model
def rows889 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols889 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD889 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS889 : List Int := [10,14,18,22,24,26,28,30,32,34,38,42,46]
theorem problem889_eq : pairedProblem rows889 cols889 requiredD889 requiredS889 =
    MomentData.problem889 := by rfl
theorem leaf889 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows889++rows889))
    (hc : (q.map Prod.snd).Perm (cols889++cols889))
    (hd : ∀ k ∈ requiredD889, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS889, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows889 cols889 requiredD889 requiredS889
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem889_eq] at model
  exact MomentData.excluded889 ds ss model
def rows890 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols890 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD890 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS890 : List Int := [6,10,14,18,22,26,28,30,32,34,38,42,46,50]
theorem problem890_eq : pairedProblem rows890 cols890 requiredD890 requiredS890 =
    MomentData.problem890 := by rfl
theorem leaf890 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows890++rows890))
    (hc : (q.map Prod.snd).Perm (cols890++cols890))
    (hd : ∀ k ∈ requiredD890, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS890, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows890 cols890 requiredD890 requiredS890
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem890_eq] at model
  exact MomentData.excluded890 ds ss model
def rows891 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols891 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD891 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS891 : List Int := [4,8,12,16,20,24,28,30,32,36,40,44,48,52]
theorem problem891_eq : pairedProblem rows891 cols891 requiredD891 requiredS891 =
    MomentData.problem891 := by rfl
theorem leaf891 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows891++rows891))
    (hc : (q.map Prod.snd).Perm (cols891++cols891))
    (hd : ∀ k ∈ requiredD891, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS891, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows891 cols891 requiredD891 requiredS891
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem891_eq] at model
  exact MomentData.excluded891 ds ss model
def rows892 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols892 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD892 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS892 : List Int := [4,8,12,16,20,24,28,32,36,40,44,48,52]
theorem problem892_eq : pairedProblem rows892 cols892 requiredD892 requiredS892 =
    MomentData.problem892 := by rfl
theorem leaf892 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows892++rows892))
    (hc : (q.map Prod.snd).Perm (cols892++cols892))
    (hd : ∀ k ∈ requiredD892, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS892, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows892 cols892 requiredD892 requiredS892
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem892_eq] at model
  exact MomentData.excluded892 ds ss model
def rows893 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols893 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD893 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS893 : List Int := [6,10,14,18,22,26,28,30,34,38,42,46,50]
theorem problem893_eq : pairedProblem rows893 cols893 requiredD893 requiredS893 =
    MomentData.problem893 := by rfl
theorem leaf893 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows893++rows893))
    (hc : (q.map Prod.snd).Perm (cols893++cols893))
    (hd : ∀ k ∈ requiredD893, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS893, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows893 cols893 requiredD893 requiredS893
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem893_eq] at model
  exact MomentData.excluded893 ds ss model
def rows894 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols894 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD894 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS894 : List Int := [18,20,22,24,26,28,30,32,34,36,38,40,42,44,46]
theorem problem894_eq : pairedProblem rows894 cols894 requiredD894 requiredS894 =
    MomentData.problem894 := by rfl
theorem leaf894 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows894++rows894))
    (hc : (q.map Prod.snd).Perm (cols894++cols894))
    (hd : ∀ k ∈ requiredD894, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS894, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows894 cols894 requiredD894 requiredS894
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem894_eq] at model
  exact MomentData.excluded894 ds ss model
def rows895 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols895 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD895 : List Int := [-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14]
def requiredS895 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,40,42,46]
theorem problem895_eq : pairedProblem rows895 cols895 requiredD895 requiredS895 =
    MomentData.problem895 := by rfl
theorem leaf895 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows895++rows895))
    (hc : (q.map Prod.snd).Perm (cols895++cols895))
    (hd : ∀ k ∈ requiredD895, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS895, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows895 cols895 requiredD895 requiredS895
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem895_eq] at model
  exact MomentData.excluded895 ds ss model
#print axioms leaf768
end Gardner.Kernel.MomentContexts
