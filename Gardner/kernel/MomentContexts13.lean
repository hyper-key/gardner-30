import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1664 : List Int := [0,2,3,6,9,12,15,18,19,21,24,25,27,28,29]
def cols1664 : List Int := [0,2,3,6,9,12,15,18,19,21,24,25,27,28,29]
def requiredD1664 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1664 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1664_eq : pairedProblem rows1664 cols1664 requiredD1664 requiredS1664 =
    MomentData.problem1664 := by rfl
theorem leaf1664 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1664++rows1664))
    (hc : (q.map Prod.snd).Perm (cols1664++cols1664))
    (hd : ∀ k ∈ requiredD1664, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1664, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1664 cols1664 requiredD1664 requiredS1664
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1664_eq] at model
  exact MomentData.excluded1664 ds ss model
def rows1665 : List Int := [1,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1665 : List Int := [1,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1665 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1665 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1665_eq : pairedProblem rows1665 cols1665 requiredD1665 requiredS1665 =
    MomentData.problem1665 := by rfl
theorem leaf1665 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1665++rows1665))
    (hc : (q.map Prod.snd).Perm (cols1665++cols1665))
    (hd : ∀ k ∈ requiredD1665, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1665, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1665 cols1665 requiredD1665 requiredS1665
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1665_eq] at model
  exact MomentData.excluded1665 ds ss model
def rows1666 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1666 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1666 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1666 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem1666_eq : pairedProblem rows1666 cols1666 requiredD1666 requiredS1666 =
    MomentData.problem1666 := by rfl
theorem leaf1666 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1666++rows1666))
    (hc : (q.map Prod.snd).Perm (cols1666++cols1666))
    (hd : ∀ k ∈ requiredD1666, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1666, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1666 cols1666 requiredD1666 requiredS1666
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1666_eq] at model
  exact MomentData.excluded1666 ds ss model
def rows1667 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1667 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1667 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1667 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem1667_eq : pairedProblem rows1667 cols1667 requiredD1667 requiredS1667 =
    MomentData.problem1667 := by rfl
theorem leaf1667 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1667++rows1667))
    (hc : (q.map Prod.snd).Perm (cols1667++cols1667))
    (hd : ∀ k ∈ requiredD1667, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1667, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1667 cols1667 requiredD1667 requiredS1667
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1667_eq] at model
  exact MomentData.excluded1667 ds ss model
def rows1668 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1668 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1668 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1668 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1668_eq : pairedProblem rows1668 cols1668 requiredD1668 requiredS1668 =
    MomentData.problem1668 := by rfl
theorem leaf1668 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1668++rows1668))
    (hc : (q.map Prod.snd).Perm (cols1668++cols1668))
    (hd : ∀ k ∈ requiredD1668, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1668, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1668 cols1668 requiredD1668 requiredS1668
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1668_eq] at model
  exact MomentData.excluded1668 ds ss model
def rows1669 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1669 : List Int := [1,2,4,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1669 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1669 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43]
theorem problem1669_eq : pairedProblem rows1669 cols1669 requiredD1669 requiredS1669 =
    MomentData.problem1669 := by rfl
theorem leaf1669 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1669++rows1669))
    (hc : (q.map Prod.snd).Perm (cols1669++cols1669))
    (hd : ∀ k ∈ requiredD1669, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1669, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1669 cols1669 requiredD1669 requiredS1669
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1669_eq] at model
  exact MomentData.excluded1669 ds ss model
def rows1670 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def cols1670 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def requiredD1670 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1670 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1670_eq : pairedProblem rows1670 cols1670 requiredD1670 requiredS1670 =
    MomentData.problem1670 := by rfl
theorem leaf1670 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1670++rows1670))
    (hc : (q.map Prod.snd).Perm (cols1670++cols1670))
    (hd : ∀ k ∈ requiredD1670, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1670, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1670 cols1670 requiredD1670 requiredS1670
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1670_eq] at model
  exact MomentData.excluded1670 ds ss model
def rows1671 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def cols1671 : List Int := [0,2,3,6,9,12,15,18,20,21,24,25,27,28,29]
def requiredD1671 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1671 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1671_eq : pairedProblem rows1671 cols1671 requiredD1671 requiredS1671 =
    MomentData.problem1671 := by rfl
theorem leaf1671 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1671++rows1671))
    (hc : (q.map Prod.snd).Perm (cols1671++cols1671))
    (hd : ∀ k ∈ requiredD1671, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1671, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1671 cols1671 requiredD1671 requiredS1671
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1671_eq] at model
  exact MomentData.excluded1671 ds ss model
def rows1672 : List Int := [2,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1672 : List Int := [2,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1672 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1672 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1672_eq : pairedProblem rows1672 cols1672 requiredD1672 requiredS1672 =
    MomentData.problem1672 := by rfl
theorem leaf1672 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1672++rows1672))
    (hc : (q.map Prod.snd).Perm (cols1672++cols1672))
    (hd : ∀ k ∈ requiredD1672, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1672, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1672 cols1672 requiredD1672 requiredS1672
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1672_eq] at model
  exact MomentData.excluded1672 ds ss model
def rows1673 : List Int := [3,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1673 : List Int := [3,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1673 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1673 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1673_eq : pairedProblem rows1673 cols1673 requiredD1673 requiredS1673 =
    MomentData.problem1673 := by rfl
theorem leaf1673 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1673++rows1673))
    (hc : (q.map Prod.snd).Perm (cols1673++cols1673))
    (hd : ∀ k ∈ requiredD1673, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1673, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1673 cols1673 requiredD1673 requiredS1673
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1673_eq] at model
  exact MomentData.excluded1673 ds ss model
def rows1674 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1674 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD1674 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1674 : List Int := [6,9,12,15,18,21,24,27,30,31,33,36,39,42,45]
theorem problem1674_eq : pairedProblem rows1674 cols1674 requiredD1674 requiredS1674 =
    MomentData.problem1674 := by rfl
theorem leaf1674 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1674++rows1674))
    (hc : (q.map Prod.snd).Perm (cols1674++cols1674))
    (hd : ∀ k ∈ requiredD1674, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1674, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1674 cols1674 requiredD1674 requiredS1674
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1674_eq] at model
  exact MomentData.excluded1674 ds ss model
def rows1675 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1675 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD1675 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1675 : List Int := [9,12,15,18,21,24,27,30,31,33,36,39,42,45]
theorem problem1675_eq : pairedProblem rows1675 cols1675 requiredD1675 requiredS1675 =
    MomentData.problem1675 := by rfl
theorem leaf1675 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1675++rows1675))
    (hc : (q.map Prod.snd).Perm (cols1675++cols1675))
    (hd : ∀ k ∈ requiredD1675, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1675, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1675 cols1675 requiredD1675 requiredS1675
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1675_eq] at model
  exact MomentData.excluded1675 ds ss model
def rows1676 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1676 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD1676 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1676 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1676_eq : pairedProblem rows1676 cols1676 requiredD1676 requiredS1676 =
    MomentData.problem1676 := by rfl
theorem leaf1676 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1676++rows1676))
    (hc : (q.map Prod.snd).Perm (cols1676++cols1676))
    (hd : ∀ k ∈ requiredD1676, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1676, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1676 cols1676 requiredD1676 requiredS1676
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1676_eq] at model
  exact MomentData.excluded1676 ds ss model
def rows1677 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1677 : List Int := [0,2,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD1677 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1677 : List Int := [6,9,12,15,18,21,24,27,30,31,33,36,39,42]
theorem problem1677_eq : pairedProblem rows1677 cols1677 requiredD1677 requiredS1677 =
    MomentData.problem1677 := by rfl
theorem leaf1677 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1677++rows1677))
    (hc : (q.map Prod.snd).Perm (cols1677++cols1677))
    (hd : ∀ k ∈ requiredD1677, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1677, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1677 cols1677 requiredD1677 requiredS1677
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1677_eq] at model
  exact MomentData.excluded1677 ds ss model
def rows1678 : List Int := [1,2,5,6,8,11,14,17,20,23,24,26,27,28,29]
def cols1678 : List Int := [1,2,5,6,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1678 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1678 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1678_eq : pairedProblem rows1678 cols1678 requiredD1678 requiredS1678 =
    MomentData.problem1678 := by rfl
theorem leaf1678 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1678++rows1678))
    (hc : (q.map Prod.snd).Perm (cols1678++cols1678))
    (hd : ∀ k ∈ requiredD1678, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1678, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1678 cols1678 requiredD1678 requiredS1678
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1678_eq] at model
  exact MomentData.excluded1678 ds ss model
def rows1679 : List Int := [1,3,5,6,7,9,16,18,20,22,24,26,27,28,29]
def cols1679 : List Int := [1,3,5,6,7,9,16,18,20,22,24,26,27,28,29]
def requiredD1679 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1679 : List Int := [13,14,15,17,19,21,23,25,27,29,31,33,35,36,37]
theorem problem1679_eq : pairedProblem rows1679 cols1679 requiredD1679 requiredS1679 =
    MomentData.problem1679 := by rfl
theorem leaf1679 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1679++rows1679))
    (hc : (q.map Prod.snd).Perm (cols1679++cols1679))
    (hd : ∀ k ∈ requiredD1679, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1679, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1679 cols1679 requiredD1679 requiredS1679
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1679_eq] at model
  exact MomentData.excluded1679 ds ss model
def rows1680 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1680 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1680 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1680 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1680_eq : pairedProblem rows1680 cols1680 requiredD1680 requiredS1680 =
    MomentData.problem1680 := by rfl
theorem leaf1680 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1680++rows1680))
    (hc : (q.map Prod.snd).Perm (cols1680++cols1680))
    (hd : ∀ k ∈ requiredD1680, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1680, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1680 cols1680 requiredD1680 requiredS1680
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1680_eq] at model
  exact MomentData.excluded1680 ds ss model
def rows1681 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1681 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1681 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1681 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1681_eq : pairedProblem rows1681 cols1681 requiredD1681 requiredS1681 =
    MomentData.problem1681 := by rfl
theorem leaf1681 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1681++rows1681))
    (hc : (q.map Prod.snd).Perm (cols1681++cols1681))
    (hd : ∀ k ∈ requiredD1681, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1681, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1681 cols1681 requiredD1681 requiredS1681
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1681_eq] at model
  exact MomentData.excluded1681 ds ss model
def rows1682 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1682 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1682 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1682 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1682_eq : pairedProblem rows1682 cols1682 requiredD1682 requiredS1682 =
    MomentData.problem1682 := by rfl
theorem leaf1682 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1682++rows1682))
    (hc : (q.map Prod.snd).Perm (cols1682++cols1682))
    (hd : ∀ k ∈ requiredD1682, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1682, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1682 cols1682 requiredD1682 requiredS1682
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1682_eq] at model
  exact MomentData.excluded1682 ds ss model
def rows1683 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1683 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1683 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1683 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1683_eq : pairedProblem rows1683 cols1683 requiredD1683 requiredS1683 =
    MomentData.problem1683 := by rfl
theorem leaf1683 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1683++rows1683))
    (hc : (q.map Prod.snd).Perm (cols1683++cols1683))
    (hd : ∀ k ∈ requiredD1683, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1683, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1683 cols1683 requiredD1683 requiredS1683
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1683_eq] at model
  exact MomentData.excluded1683 ds ss model
def rows1684 : List Int := [4,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1684 : List Int := [4,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1684 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1684 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1684_eq : pairedProblem rows1684 cols1684 requiredD1684 requiredS1684 =
    MomentData.problem1684 := by rfl
theorem leaf1684 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1684++rows1684))
    (hc : (q.map Prod.snd).Perm (cols1684++cols1684))
    (hd : ∀ k ∈ requiredD1684, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1684, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1684 cols1684 requiredD1684 requiredS1684
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1684_eq] at model
  exact MomentData.excluded1684 ds ss model
def rows1685 : List Int := [0,2,3,6,9,12,15,18,21,23,24,25,27,28,29]
def cols1685 : List Int := [0,2,3,6,9,12,15,18,21,23,24,25,27,28,29]
def requiredD1685 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1685 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1685_eq : pairedProblem rows1685 cols1685 requiredD1685 requiredS1685 =
    MomentData.problem1685 := by rfl
theorem leaf1685 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1685++rows1685))
    (hc : (q.map Prod.snd).Perm (cols1685++cols1685))
    (hd : ∀ k ∈ requiredD1685, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1685, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1685 cols1685 requiredD1685 requiredS1685
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1685_eq] at model
  exact MomentData.excluded1685 ds ss model
def rows1686 : List Int := [0,2,3,6,9,12,15,18,21,23,24,25,27,28,29]
def cols1686 : List Int := [0,2,3,6,9,12,15,18,21,23,24,25,27,28,29]
def requiredD1686 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1686 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1686_eq : pairedProblem rows1686 cols1686 requiredD1686 requiredS1686 =
    MomentData.problem1686 := by rfl
theorem leaf1686 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1686++rows1686))
    (hc : (q.map Prod.snd).Perm (cols1686++cols1686))
    (hd : ∀ k ∈ requiredD1686, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1686, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1686 cols1686 requiredD1686 requiredS1686
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1686_eq] at model
  exact MomentData.excluded1686 ds ss model
def rows1687 : List Int := [0,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1687 : List Int := [0,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1687 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1687 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1687_eq : pairedProblem rows1687 cols1687 requiredD1687 requiredS1687 =
    MomentData.problem1687 := by rfl
theorem leaf1687 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1687++rows1687))
    (hc : (q.map Prod.snd).Perm (cols1687++cols1687))
    (hd : ∀ k ∈ requiredD1687, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1687, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1687 cols1687 requiredD1687 requiredS1687
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1687_eq] at model
  exact MomentData.excluded1687 ds ss model
def rows1688 : List Int := [0,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1688 : List Int := [0,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1688 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1688 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1688_eq : pairedProblem rows1688 cols1688 requiredD1688 requiredS1688 =
    MomentData.problem1688 := by rfl
theorem leaf1688 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1688++rows1688))
    (hc : (q.map Prod.snd).Perm (cols1688++cols1688))
    (hd : ∀ k ∈ requiredD1688, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1688, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1688 cols1688 requiredD1688 requiredS1688
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1688_eq] at model
  exact MomentData.excluded1688 ds ss model
def rows1689 : List Int := [1,2,5,7,8,11,14,17,20,23,24,26,27,28,29]
def cols1689 : List Int := [1,2,5,7,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1689 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1689 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1689_eq : pairedProblem rows1689 cols1689 requiredD1689 requiredS1689 =
    MomentData.problem1689 := by rfl
theorem leaf1689 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1689++rows1689))
    (hc : (q.map Prod.snd).Perm (cols1689++cols1689))
    (hd : ∀ k ∈ requiredD1689, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1689, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1689 cols1689 requiredD1689 requiredS1689
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1689_eq] at model
  exact MomentData.excluded1689 ds ss model
def rows1690 : List Int := [0,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1690 : List Int := [0,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1690 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1690 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1690_eq : pairedProblem rows1690 cols1690 requiredD1690 requiredS1690 =
    MomentData.problem1690 := by rfl
theorem leaf1690 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1690++rows1690))
    (hc : (q.map Prod.snd).Perm (cols1690++cols1690))
    (hd : ∀ k ∈ requiredD1690, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1690, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1690 cols1690 requiredD1690 requiredS1690
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1690_eq] at model
  exact MomentData.excluded1690 ds ss model
def rows1691 : List Int := [0,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1691 : List Int := [0,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1691 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1691 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1691_eq : pairedProblem rows1691 cols1691 requiredD1691 requiredS1691 =
    MomentData.problem1691 := by rfl
theorem leaf1691 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1691++rows1691))
    (hc : (q.map Prod.snd).Perm (cols1691++cols1691))
    (hd : ∀ k ∈ requiredD1691, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1691, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1691 cols1691 requiredD1691 requiredS1691
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1691_eq] at model
  exact MomentData.excluded1691 ds ss model
def rows1692 : List Int := [0,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1692 : List Int := [5,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1692 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1692 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1692_eq : pairedProblem rows1692 cols1692 requiredD1692 requiredS1692 =
    MomentData.problem1692 := by rfl
theorem leaf1692 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1692++rows1692))
    (hc : (q.map Prod.snd).Perm (cols1692++cols1692))
    (hd : ∀ k ∈ requiredD1692, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1692, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1692 cols1692 requiredD1692 requiredS1692
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1692_eq] at model
  exact MomentData.excluded1692 ds ss model
def rows1693 : List Int := [5,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1693 : List Int := [5,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1693 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1693 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1693_eq : pairedProblem rows1693 cols1693 requiredD1693 requiredS1693 =
    MomentData.problem1693 := by rfl
theorem leaf1693 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1693++rows1693))
    (hc : (q.map Prod.snd).Perm (cols1693++cols1693))
    (hd : ∀ k ∈ requiredD1693, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1693, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1693 cols1693 requiredD1693 requiredS1693
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1693_eq] at model
  exact MomentData.excluded1693 ds ss model
def rows1694 : List Int := [1,3,5,7,8,9,16,18,20,22,24,26,27,28,29]
def cols1694 : List Int := [1,3,5,7,8,9,16,18,20,22,24,26,27,28,29]
def requiredD1694 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1694 : List Int := [13,14,15,17,19,21,23,25,27,29,31,33,35,36,37]
theorem problem1694_eq : pairedProblem rows1694 cols1694 requiredD1694 requiredS1694 =
    MomentData.problem1694 := by rfl
theorem leaf1694 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1694++rows1694))
    (hc : (q.map Prod.snd).Perm (cols1694++cols1694))
    (hd : ∀ k ∈ requiredD1694, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1694, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1694 cols1694 requiredD1694 requiredS1694
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1694_eq] at model
  exact MomentData.excluded1694 ds ss model
def rows1695 : List Int := [0,1,4,7,10,13,16,19,20,22,23,25,26,28,29]
def cols1695 : List Int := [0,1,4,7,10,13,16,19,20,22,23,25,26,28,29]
def requiredD1695 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1695 : List Int := [5,8,11,14,17,20,23,26,29,30,32,35,38,41,44]
theorem problem1695_eq : pairedProblem rows1695 cols1695 requiredD1695 requiredS1695 =
    MomentData.problem1695 := by rfl
theorem leaf1695 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1695++rows1695))
    (hc : (q.map Prod.snd).Perm (cols1695++cols1695))
    (hd : ∀ k ∈ requiredD1695, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1695, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1695 cols1695 requiredD1695 requiredS1695
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1695_eq] at model
  exact MomentData.excluded1695 ds ss model
def rows1696 : List Int := [0,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1696 : List Int := [0,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1696 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1696 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1696_eq : pairedProblem rows1696 cols1696 requiredD1696 requiredS1696 =
    MomentData.problem1696 := by rfl
theorem leaf1696 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1696++rows1696))
    (hc : (q.map Prod.snd).Perm (cols1696++cols1696))
    (hd : ∀ k ∈ requiredD1696, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1696, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1696 cols1696 requiredD1696 requiredS1696
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1696_eq] at model
  exact MomentData.excluded1696 ds ss model
def rows1697 : List Int := [0,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1697 : List Int := [0,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1697 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1697 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1697_eq : pairedProblem rows1697 cols1697 requiredD1697 requiredS1697 =
    MomentData.problem1697 := by rfl
theorem leaf1697 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1697++rows1697))
    (hc : (q.map Prod.snd).Perm (cols1697++cols1697))
    (hd : ∀ k ∈ requiredD1697, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1697, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1697 cols1697 requiredD1697 requiredS1697
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1697_eq] at model
  exact MomentData.excluded1697 ds ss model
def rows1698 : List Int := [6,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1698 : List Int := [6,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1698 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1698 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1698_eq : pairedProblem rows1698 cols1698 requiredD1698 requiredS1698 =
    MomentData.problem1698 := by rfl
theorem leaf1698 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1698++rows1698))
    (hc : (q.map Prod.snd).Perm (cols1698++cols1698))
    (hd : ∀ k ∈ requiredD1698, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1698, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1698 cols1698 requiredD1698 requiredS1698
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1698_eq] at model
  exact MomentData.excluded1698 ds ss model
def rows1699 : List Int := [1,2,5,8,9,11,14,17,20,23,24,26,27,28,29]
def cols1699 : List Int := [1,2,5,8,9,11,14,17,20,23,24,26,27,28,29]
def requiredD1699 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1699 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1699_eq : pairedProblem rows1699 cols1699 requiredD1699 requiredS1699 =
    MomentData.problem1699 := by rfl
theorem leaf1699 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1699++rows1699))
    (hc : (q.map Prod.snd).Perm (cols1699++cols1699))
    (hd : ∀ k ∈ requiredD1699, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1699, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1699 cols1699 requiredD1699 requiredS1699
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1699_eq] at model
  exact MomentData.excluded1699 ds ss model
def rows1700 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1700 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1700 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1700 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1700_eq : pairedProblem rows1700 cols1700 requiredD1700 requiredS1700 =
    MomentData.problem1700 := by rfl
theorem leaf1700 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1700++rows1700))
    (hc : (q.map Prod.snd).Perm (cols1700++cols1700))
    (hd : ∀ k ∈ requiredD1700, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1700, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1700 cols1700 requiredD1700 requiredS1700
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1700_eq] at model
  exact MomentData.excluded1700 ds ss model
def rows1701 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1701 : List Int := [0,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1701 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1701 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1701_eq : pairedProblem rows1701 cols1701 requiredD1701 requiredS1701 =
    MomentData.problem1701 := by rfl
theorem leaf1701 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1701++rows1701))
    (hc : (q.map Prod.snd).Perm (cols1701++cols1701))
    (hd : ∀ k ∈ requiredD1701, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1701, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1701 cols1701 requiredD1701 requiredS1701
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1701_eq] at model
  exact MomentData.excluded1701 ds ss model
def rows1702 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1702 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1702 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1702 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem1702_eq : pairedProblem rows1702 cols1702 requiredD1702 requiredS1702 =
    MomentData.problem1702 := by rfl
theorem leaf1702 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1702++rows1702))
    (hc : (q.map Prod.snd).Perm (cols1702++cols1702))
    (hd : ∀ k ∈ requiredD1702, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1702, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1702 cols1702 requiredD1702 requiredS1702
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1702_eq] at model
  exact MomentData.excluded1702 ds ss model
def rows1703 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1703 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1703 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1703 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem1703_eq : pairedProblem rows1703 cols1703 requiredD1703 requiredS1703 =
    MomentData.problem1703 := by rfl
theorem leaf1703 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1703++rows1703))
    (hc : (q.map Prod.snd).Perm (cols1703++cols1703))
    (hd : ∀ k ∈ requiredD1703, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1703, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1703 cols1703 requiredD1703 requiredS1703
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1703_eq] at model
  exact MomentData.excluded1703 ds ss model
def rows1704 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1704 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1704 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1704 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,43]
theorem problem1704_eq : pairedProblem rows1704 cols1704 requiredD1704 requiredS1704 =
    MomentData.problem1704 := by rfl
theorem leaf1704 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1704++rows1704))
    (hc : (q.map Prod.snd).Perm (cols1704++cols1704))
    (hd : ∀ k ∈ requiredD1704, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1704, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1704 cols1704 requiredD1704 requiredS1704
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1704_eq] at model
  exact MomentData.excluded1704 ds ss model
def rows1705 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1705 : List Int := [7,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1705 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1705 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1705_eq : pairedProblem rows1705 cols1705 requiredD1705 requiredS1705 =
    MomentData.problem1705 := by rfl
theorem leaf1705 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1705++rows1705))
    (hc : (q.map Prod.snd).Perm (cols1705++cols1705))
    (hd : ∀ k ∈ requiredD1705, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1705, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1705 cols1705 requiredD1705 requiredS1705
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1705_eq] at model
  exact MomentData.excluded1705 ds ss model
def rows1706 : List Int := [0,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1706 : List Int := [0,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1706 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1706 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1706_eq : pairedProblem rows1706 cols1706 requiredD1706 requiredS1706 =
    MomentData.problem1706 := by rfl
theorem leaf1706 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1706++rows1706))
    (hc : (q.map Prod.snd).Perm (cols1706++cols1706))
    (hd : ∀ k ∈ requiredD1706, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1706, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1706 cols1706 requiredD1706 requiredS1706
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1706_eq] at model
  exact MomentData.excluded1706 ds ss model
def rows1707 : List Int := [0,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1707 : List Int := [0,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1707 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1707 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1707_eq : pairedProblem rows1707 cols1707 requiredD1707 requiredS1707 =
    MomentData.problem1707 := by rfl
theorem leaf1707 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1707++rows1707))
    (hc : (q.map Prod.snd).Perm (cols1707++cols1707))
    (hd : ∀ k ∈ requiredD1707, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1707, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1707 cols1707 requiredD1707 requiredS1707
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1707_eq] at model
  exact MomentData.excluded1707 ds ss model
def rows1708 : List Int := [1,2,5,8,10,11,14,17,20,23,24,26,27,28,29]
def cols1708 : List Int := [1,2,5,8,10,11,14,17,20,23,24,26,27,28,29]
def requiredD1708 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1708 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1708_eq : pairedProblem rows1708 cols1708 requiredD1708 requiredS1708 =
    MomentData.problem1708 := by rfl
theorem leaf1708 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1708++rows1708))
    (hc : (q.map Prod.snd).Perm (cols1708++cols1708))
    (hd : ∀ k ∈ requiredD1708, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1708, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1708 cols1708 requiredD1708 requiredS1708
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1708_eq] at model
  exact MomentData.excluded1708 ds ss model
def rows1709 : List Int := [1,3,5,7,9,10,16,18,20,22,24,26,27,28,29]
def cols1709 : List Int := [1,3,5,7,9,10,16,18,20,22,24,26,27,28,29]
def requiredD1709 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1709 : List Int := [13,14,15,17,19,21,23,25,27,29,31,33,35,36,37]
theorem problem1709_eq : pairedProblem rows1709 cols1709 requiredD1709 requiredS1709 =
    MomentData.problem1709 := by rfl
theorem leaf1709 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1709++rows1709))
    (hc : (q.map Prod.snd).Perm (cols1709++cols1709))
    (hd : ∀ k ∈ requiredD1709, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1709, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1709 cols1709 requiredD1709 requiredS1709
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1709_eq] at model
  exact MomentData.excluded1709 ds ss model
def rows1710 : List Int := [0,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1710 : List Int := [0,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1710 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1710 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1710_eq : pairedProblem rows1710 cols1710 requiredD1710 requiredS1710 =
    MomentData.problem1710 := by rfl
theorem leaf1710 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1710++rows1710))
    (hc : (q.map Prod.snd).Perm (cols1710++cols1710))
    (hd : ∀ k ∈ requiredD1710, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1710, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1710 cols1710 requiredD1710 requiredS1710
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1710_eq] at model
  exact MomentData.excluded1710 ds ss model
def rows1711 : List Int := [0,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1711 : List Int := [0,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1711 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1711 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1711_eq : pairedProblem rows1711 cols1711 requiredD1711 requiredS1711 =
    MomentData.problem1711 := by rfl
theorem leaf1711 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1711++rows1711))
    (hc : (q.map Prod.snd).Perm (cols1711++cols1711))
    (hd : ∀ k ∈ requiredD1711, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1711, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1711 cols1711 requiredD1711 requiredS1711
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1711_eq] at model
  exact MomentData.excluded1711 ds ss model
def rows1712 : List Int := [1,2,5,8,11,12,14,17,20,23,24,26,27,28,29]
def cols1712 : List Int := [1,2,5,8,11,12,14,17,20,23,24,26,27,28,29]
def requiredD1712 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1712 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1712_eq : pairedProblem rows1712 cols1712 requiredD1712 requiredS1712 =
    MomentData.problem1712 := by rfl
theorem leaf1712 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1712++rows1712))
    (hc : (q.map Prod.snd).Perm (cols1712++cols1712))
    (hd : ∀ k ∈ requiredD1712, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1712, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1712 cols1712 requiredD1712 requiredS1712
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1712_eq] at model
  exact MomentData.excluded1712 ds ss model
def rows1713 : List Int := [1,3,5,7,9,12,16,18,20,22,24,26,27,28,29]
def cols1713 : List Int := [1,3,5,7,9,12,16,18,20,22,24,26,27,28,29]
def requiredD1713 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1713 : List Int := [13,14,15,17,19,21,23,25,27,29,31,33,35,36,37]
theorem problem1713_eq : pairedProblem rows1713 cols1713 requiredD1713 requiredS1713 =
    MomentData.problem1713 := by rfl
theorem leaf1713 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1713++rows1713))
    (hc : (q.map Prod.snd).Perm (cols1713++cols1713))
    (hd : ∀ k ∈ requiredD1713, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1713, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1713 cols1713 requiredD1713 requiredS1713
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1713_eq] at model
  exact MomentData.excluded1713 ds ss model
def rows1714 : List Int := [1,2,5,8,11,13,14,17,20,23,24,26,27,28,29]
def cols1714 : List Int := [1,2,5,8,11,13,14,17,20,23,24,26,27,28,29]
def requiredD1714 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1714 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1714_eq : pairedProblem rows1714 cols1714 requiredD1714 requiredS1714 =
    MomentData.problem1714 := by rfl
theorem leaf1714 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1714++rows1714))
    (hc : (q.map Prod.snd).Perm (cols1714++cols1714))
    (hd : ∀ k ∈ requiredD1714, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1714, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1714 cols1714 requiredD1714 requiredS1714
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1714_eq] at model
  exact MomentData.excluded1714 ds ss model
def rows1715 : List Int := [1,2,5,8,11,14,15,17,20,23,24,26,27,28,29]
def cols1715 : List Int := [1,2,5,8,11,14,15,17,20,23,24,26,27,28,29]
def requiredD1715 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1715 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1715_eq : pairedProblem rows1715 cols1715 requiredD1715 requiredS1715 =
    MomentData.problem1715 := by rfl
theorem leaf1715 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1715++rows1715))
    (hc : (q.map Prod.snd).Perm (cols1715++cols1715))
    (hd : ∀ k ∈ requiredD1715, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1715, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1715 cols1715 requiredD1715 requiredS1715
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1715_eq] at model
  exact MomentData.excluded1715 ds ss model
def rows1716 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols1716 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,27,28,29]
def requiredD1716 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1716 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1716_eq : pairedProblem rows1716 cols1716 requiredD1716 requiredS1716 =
    MomentData.problem1716 := by rfl
theorem leaf1716 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1716++rows1716))
    (hc : (q.map Prod.snd).Perm (cols1716++cols1716))
    (hd : ∀ k ∈ requiredD1716, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1716, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1716 cols1716 requiredD1716 requiredS1716
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1716_eq] at model
  exact MomentData.excluded1716 ds ss model
def rows1717 : List Int := [1,2,5,8,11,14,16,17,20,23,24,26,27,28,29]
def cols1717 : List Int := [1,2,5,8,11,14,16,17,20,23,24,26,27,28,29]
def requiredD1717 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1717 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1717_eq : pairedProblem rows1717 cols1717 requiredD1717 requiredS1717 =
    MomentData.problem1717 := by rfl
theorem leaf1717 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1717++rows1717))
    (hc : (q.map Prod.snd).Perm (cols1717++cols1717))
    (hd : ∀ k ∈ requiredD1717, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1717, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1717 cols1717 requiredD1717 requiredS1717
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1717_eq] at model
  exact MomentData.excluded1717 ds ss model
def rows1718 : List Int := [1,2,5,8,11,14,17,18,20,23,24,26,27,28,29]
def cols1718 : List Int := [1,2,5,8,11,14,17,18,20,23,24,26,27,28,29]
def requiredD1718 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1718 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1718_eq : pairedProblem rows1718 cols1718 requiredD1718 requiredS1718 =
    MomentData.problem1718 := by rfl
theorem leaf1718 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1718++rows1718))
    (hc : (q.map Prod.snd).Perm (cols1718++cols1718))
    (hd : ∀ k ∈ requiredD1718, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1718, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1718 cols1718 requiredD1718 requiredS1718
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1718_eq] at model
  exact MomentData.excluded1718 ds ss model
def rows1719 : List Int := [1,2,5,8,11,14,17,19,20,23,24,26,27,28,29]
def cols1719 : List Int := [1,2,5,8,11,14,17,19,20,23,24,26,27,28,29]
def requiredD1719 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1719 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1719_eq : pairedProblem rows1719 cols1719 requiredD1719 requiredS1719 =
    MomentData.problem1719 := by rfl
theorem leaf1719 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1719++rows1719))
    (hc : (q.map Prod.snd).Perm (cols1719++cols1719))
    (hd : ∀ k ∈ requiredD1719, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1719, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1719 cols1719 requiredD1719 requiredS1719
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1719_eq] at model
  exact MomentData.excluded1719 ds ss model
def rows1720 : List Int := [8,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1720 : List Int := [8,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1720 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1720 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1720_eq : pairedProblem rows1720 cols1720 requiredD1720 requiredS1720 =
    MomentData.problem1720 := by rfl
theorem leaf1720 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1720++rows1720))
    (hc : (q.map Prod.snd).Perm (cols1720++cols1720))
    (hd : ∀ k ∈ requiredD1720, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1720, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1720 cols1720 requiredD1720 requiredS1720
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1720_eq] at model
  exact MomentData.excluded1720 ds ss model
def rows1721 : List Int := [8,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def cols1721 : List Int := [8,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def requiredD1721 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1721 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1721_eq : pairedProblem rows1721 cols1721 requiredD1721 requiredS1721 =
    MomentData.problem1721 := by rfl
theorem leaf1721 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1721++rows1721))
    (hc : (q.map Prod.snd).Perm (cols1721++cols1721))
    (hd : ∀ k ∈ requiredD1721, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1721, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1721 cols1721 requiredD1721 requiredS1721
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1721_eq] at model
  exact MomentData.excluded1721 ds ss model
def rows1722 : List Int := [1,2,5,8,11,14,17,20,21,23,24,26,27,28,29]
def cols1722 : List Int := [1,2,5,8,11,14,17,20,21,23,24,26,27,28,29]
def requiredD1722 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1722 : List Int := [7,10,13,16,19,22,25,28,29,31,34,37,40,43]
theorem problem1722_eq : pairedProblem rows1722 cols1722 requiredD1722 requiredS1722 =
    MomentData.problem1722 := by rfl
theorem leaf1722 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1722++rows1722))
    (hc : (q.map Prod.snd).Perm (cols1722++cols1722))
    (hd : ∀ k ∈ requiredD1722, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1722, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1722 cols1722 requiredD1722 requiredS1722
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1722_eq] at model
  exact MomentData.excluded1722 ds ss model
def rows1723 : List Int := [8,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1723 : List Int := [8,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1723 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1723 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1723_eq : pairedProblem rows1723 cols1723 requiredD1723 requiredS1723 =
    MomentData.problem1723 := by rfl
theorem leaf1723 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1723++rows1723))
    (hc : (q.map Prod.snd).Perm (cols1723++cols1723))
    (hd : ∀ k ∈ requiredD1723, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1723, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1723 cols1723 requiredD1723 requiredS1723
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1723_eq] at model
  exact MomentData.excluded1723 ds ss model
def rows1724 : List Int := [1,2,5,8,11,14,17,20,22,23,24,26,27,28,29]
def cols1724 : List Int := [1,2,5,8,11,14,17,20,22,23,24,26,27,28,29]
def requiredD1724 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1724 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1724_eq : pairedProblem rows1724 cols1724 requiredD1724 requiredS1724 =
    MomentData.problem1724 := by rfl
theorem leaf1724 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1724++rows1724))
    (hc : (q.map Prod.snd).Perm (cols1724++cols1724))
    (hd : ∀ k ∈ requiredD1724, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1724, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1724 cols1724 requiredD1724 requiredS1724
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1724_eq] at model
  exact MomentData.excluded1724 ds ss model
def rows1725 : List Int := [8,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1725 : List Int := [8,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1725 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1725 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1725_eq : pairedProblem rows1725 cols1725 requiredD1725 requiredS1725 =
    MomentData.problem1725 := by rfl
theorem leaf1725 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1725++rows1725))
    (hc : (q.map Prod.snd).Perm (cols1725++cols1725))
    (hd : ∀ k ∈ requiredD1725, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1725, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1725 cols1725 requiredD1725 requiredS1725
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1725_eq] at model
  exact MomentData.excluded1725 ds ss model
def rows1726 : List Int := [0,3,6,9,12,15,18,19,21,22,24,25,27,28,29]
def cols1726 : List Int := [0,3,6,9,12,15,18,19,21,22,24,25,27,28,29]
def requiredD1726 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1726 : List Int := [3,6,9,12,15,18,21,24,27,28,30,33,36,39,42]
theorem problem1726_eq : pairedProblem rows1726 cols1726 requiredD1726 requiredS1726 =
    MomentData.problem1726 := by rfl
theorem leaf1726 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1726++rows1726))
    (hc : (q.map Prod.snd).Perm (cols1726++cols1726))
    (hd : ∀ k ∈ requiredD1726, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1726, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1726 cols1726 requiredD1726 requiredS1726
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1726_eq] at model
  exact MomentData.excluded1726 ds ss model
def rows1727 : List Int := [8,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def cols1727 : List Int := [8,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1727 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1727 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1727_eq : pairedProblem rows1727 cols1727 requiredD1727 requiredS1727 =
    MomentData.problem1727 := by rfl
theorem leaf1727 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1727++rows1727))
    (hc : (q.map Prod.snd).Perm (cols1727++cols1727))
    (hd : ∀ k ∈ requiredD1727, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1727, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1727 cols1727 requiredD1727 requiredS1727
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1727_eq] at model
  exact MomentData.excluded1727 ds ss model
def rows1728 : List Int := [8,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols1728 : List Int := [8,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def requiredD1728 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1728 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1728_eq : pairedProblem rows1728 cols1728 requiredD1728 requiredS1728 =
    MomentData.problem1728 := by rfl
theorem leaf1728 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1728++rows1728))
    (hc : (q.map Prod.snd).Perm (cols1728++cols1728))
    (hd : ∀ k ∈ requiredD1728, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1728, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1728 cols1728 requiredD1728 requiredS1728
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1728_eq] at model
  exact MomentData.excluded1728 ds ss model
def rows1729 : List Int := [8,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols1729 : List Int := [8,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def requiredD1729 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1729 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1729_eq : pairedProblem rows1729 cols1729 requiredD1729 requiredS1729 =
    MomentData.problem1729 := by rfl
theorem leaf1729 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1729++rows1729))
    (hc : (q.map Prod.snd).Perm (cols1729++cols1729))
    (hd : ∀ k ∈ requiredD1729, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1729, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1729 cols1729 requiredD1729 requiredS1729
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1729_eq] at model
  exact MomentData.excluded1729 ds ss model
def rows1730 : List Int := [0,2,3,4,5,8,11,14,17,20,23,25,26,28,29]
def cols1730 : List Int := [0,2,3,4,5,8,11,14,17,20,23,25,26,28,29]
def requiredD1730 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1730 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1730_eq : pairedProblem rows1730 cols1730 requiredD1730 requiredS1730 =
    MomentData.problem1730 := by rfl
theorem leaf1730 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1730++rows1730))
    (hc : (q.map Prod.snd).Perm (cols1730++cols1730))
    (hd : ∀ k ∈ requiredD1730, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1730, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1730 cols1730 requiredD1730 requiredS1730
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1730_eq] at model
  exact MomentData.excluded1730 ds ss model
def rows1731 : List Int := [0,2,3,4,5,8,11,14,17,20,23,25,26,28,29]
def cols1731 : List Int := [0,2,3,4,5,8,11,14,17,20,23,25,26,28,29]
def requiredD1731 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1731 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1731_eq : pairedProblem rows1731 cols1731 requiredD1731 requiredS1731 =
    MomentData.problem1731 := by rfl
theorem leaf1731 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1731++rows1731))
    (hc : (q.map Prod.snd).Perm (cols1731++cols1731))
    (hd : ∀ k ∈ requiredD1731, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1731, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1731 cols1731 requiredD1731 requiredS1731
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1731_eq] at model
  exact MomentData.excluded1731 ds ss model
def rows1732 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols1732 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD1732 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1732 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46,49]
theorem problem1732_eq : pairedProblem rows1732 cols1732 requiredD1732 requiredS1732 =
    MomentData.problem1732 := by rfl
theorem leaf1732 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1732++rows1732))
    (hc : (q.map Prod.snd).Perm (cols1732++cols1732))
    (hd : ∀ k ∈ requiredD1732, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1732, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1732 cols1732 requiredD1732 requiredS1732
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1732_eq] at model
  exact MomentData.excluded1732 ds ss model
def rows1733 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols1733 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD1733 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1733 : List Int := [13,16,19,22,23,25,28,31,34,37,40,43,46,49]
theorem problem1733_eq : pairedProblem rows1733 cols1733 requiredD1733 requiredS1733 =
    MomentData.problem1733 := by rfl
theorem leaf1733 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1733++rows1733))
    (hc : (q.map Prod.snd).Perm (cols1733++cols1733))
    (hd : ∀ k ∈ requiredD1733, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1733, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1733 cols1733 requiredD1733 requiredS1733
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1733_eq] at model
  exact MomentData.excluded1733 ds ss model
def rows1734 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols1734 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD1734 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1734 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1734_eq : pairedProblem rows1734 cols1734 requiredD1734 requiredS1734 =
    MomentData.problem1734 := by rfl
theorem leaf1734 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1734++rows1734))
    (hc : (q.map Prod.snd).Perm (cols1734++cols1734))
    (hd : ∀ k ∈ requiredD1734, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1734, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1734 cols1734 requiredD1734 requiredS1734
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1734_eq] at model
  exact MomentData.excluded1734 ds ss model
def rows1735 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def cols1735 : List Int := [0,2,3,5,6,8,11,14,17,20,23,25,26,28,29]
def requiredD1735 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1735 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem1735_eq : pairedProblem rows1735 cols1735 requiredD1735 requiredS1735 =
    MomentData.problem1735 := by rfl
theorem leaf1735 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1735++rows1735))
    (hc : (q.map Prod.snd).Perm (cols1735++cols1735))
    (hd : ∀ k ∈ requiredD1735, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1735, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1735 cols1735 requiredD1735 requiredS1735
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1735_eq] at model
  exact MomentData.excluded1735 ds ss model
def rows1736 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def cols1736 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def requiredD1736 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1736 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1736_eq : pairedProblem rows1736 cols1736 requiredD1736 requiredS1736 =
    MomentData.problem1736 := by rfl
theorem leaf1736 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1736++rows1736))
    (hc : (q.map Prod.snd).Perm (cols1736++cols1736))
    (hd : ∀ k ∈ requiredD1736, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1736, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1736 cols1736 requiredD1736 requiredS1736
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1736_eq] at model
  exact MomentData.excluded1736 ds ss model
def rows1737 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def cols1737 : List Int := [0,2,3,5,7,8,11,14,17,20,23,25,26,28,29]
def requiredD1737 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1737 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1737_eq : pairedProblem rows1737 cols1737 requiredD1737 requiredS1737 =
    MomentData.problem1737 := by rfl
theorem leaf1737 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1737++rows1737))
    (hc : (q.map Prod.snd).Perm (cols1737++cols1737))
    (hd : ∀ k ∈ requiredD1737, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1737, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1737 cols1737 requiredD1737 requiredS1737
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1737_eq] at model
  exact MomentData.excluded1737 ds ss model
def rows1738 : List Int := [0,2,3,5,8,9,11,14,17,20,23,25,26,28,29]
def cols1738 : List Int := [0,2,3,5,8,9,11,14,17,20,23,25,26,28,29]
def requiredD1738 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1738 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1738_eq : pairedProblem rows1738 cols1738 requiredD1738 requiredS1738 =
    MomentData.problem1738 := by rfl
theorem leaf1738 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1738++rows1738))
    (hc : (q.map Prod.snd).Perm (cols1738++cols1738))
    (hd : ∀ k ∈ requiredD1738, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1738, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1738 cols1738 requiredD1738 requiredS1738
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1738_eq] at model
  exact MomentData.excluded1738 ds ss model
def rows1739 : List Int := [0,2,3,5,8,9,11,14,17,20,23,25,26,28,29]
def cols1739 : List Int := [0,2,3,5,8,9,11,14,17,20,23,25,26,28,29]
def requiredD1739 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1739 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1739_eq : pairedProblem rows1739 cols1739 requiredD1739 requiredS1739 =
    MomentData.problem1739 := by rfl
theorem leaf1739 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1739++rows1739))
    (hc : (q.map Prod.snd).Perm (cols1739++cols1739))
    (hd : ∀ k ∈ requiredD1739, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1739, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1739 cols1739 requiredD1739 requiredS1739
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1739_eq] at model
  exact MomentData.excluded1739 ds ss model
def rows1740 : List Int := [1,2,4,5,7,8,10,13,16,19,22,25,27,28,29]
def cols1740 : List Int := [1,2,4,5,7,8,10,13,16,19,22,25,27,28,29]
def requiredD1740 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1740 : List Int := [11,14,17,20,23,24,26,29,32,35,38,41,44,47,50]
theorem problem1740_eq : pairedProblem rows1740 cols1740 requiredD1740 requiredS1740 =
    MomentData.problem1740 := by rfl
theorem leaf1740 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1740++rows1740))
    (hc : (q.map Prod.snd).Perm (cols1740++cols1740))
    (hd : ∀ k ∈ requiredD1740, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1740, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1740 cols1740 requiredD1740 requiredS1740
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1740_eq] at model
  exact MomentData.excluded1740 ds ss model
def rows1741 : List Int := [0,2,3,5,8,10,11,14,17,20,23,25,26,28,29]
def cols1741 : List Int := [0,2,3,5,8,10,11,14,17,20,23,25,26,28,29]
def requiredD1741 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1741 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1741_eq : pairedProblem rows1741 cols1741 requiredD1741 requiredS1741 =
    MomentData.problem1741 := by rfl
theorem leaf1741 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1741++rows1741))
    (hc : (q.map Prod.snd).Perm (cols1741++cols1741))
    (hd : ∀ k ∈ requiredD1741, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1741, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1741 cols1741 requiredD1741 requiredS1741
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1741_eq] at model
  exact MomentData.excluded1741 ds ss model
def rows1742 : List Int := [0,2,3,5,8,10,11,14,17,20,23,25,26,28,29]
def cols1742 : List Int := [0,2,3,5,8,10,11,14,17,20,23,25,26,28,29]
def requiredD1742 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1742 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1742_eq : pairedProblem rows1742 cols1742 requiredD1742 requiredS1742 =
    MomentData.problem1742 := by rfl
theorem leaf1742 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1742++rows1742))
    (hc : (q.map Prod.snd).Perm (cols1742++cols1742))
    (hd : ∀ k ∈ requiredD1742, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1742, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1742 cols1742 requiredD1742 requiredS1742
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1742_eq] at model
  exact MomentData.excluded1742 ds ss model
def rows1743 : List Int := [0,2,3,5,8,11,12,14,17,20,23,25,26,28,29]
def cols1743 : List Int := [0,2,3,5,8,11,12,14,17,20,23,25,26,28,29]
def requiredD1743 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1743 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1743_eq : pairedProblem rows1743 cols1743 requiredD1743 requiredS1743 =
    MomentData.problem1743 := by rfl
theorem leaf1743 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1743++rows1743))
    (hc : (q.map Prod.snd).Perm (cols1743++cols1743))
    (hd : ∀ k ∈ requiredD1743, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1743, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1743 cols1743 requiredD1743 requiredS1743
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1743_eq] at model
  exact MomentData.excluded1743 ds ss model
def rows1744 : List Int := [0,2,3,5,8,11,12,14,17,20,23,25,26,28,29]
def cols1744 : List Int := [0,2,3,5,8,11,12,14,17,20,23,25,26,28,29]
def requiredD1744 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1744 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1744_eq : pairedProblem rows1744 cols1744 requiredD1744 requiredS1744 =
    MomentData.problem1744 := by rfl
theorem leaf1744 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1744++rows1744))
    (hc : (q.map Prod.snd).Perm (cols1744++cols1744))
    (hd : ∀ k ∈ requiredD1744, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1744, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1744 cols1744 requiredD1744 requiredS1744
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1744_eq] at model
  exact MomentData.excluded1744 ds ss model
def rows1745 : List Int := [0,2,3,5,8,11,13,14,17,20,23,25,26,28,29]
def cols1745 : List Int := [0,2,3,5,8,11,13,14,17,20,23,25,26,28,29]
def requiredD1745 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1745 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1745_eq : pairedProblem rows1745 cols1745 requiredD1745 requiredS1745 =
    MomentData.problem1745 := by rfl
theorem leaf1745 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1745++rows1745))
    (hc : (q.map Prod.snd).Perm (cols1745++cols1745))
    (hd : ∀ k ∈ requiredD1745, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1745, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1745 cols1745 requiredD1745 requiredS1745
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1745_eq] at model
  exact MomentData.excluded1745 ds ss model
def rows1746 : List Int := [0,2,3,5,8,11,13,14,17,20,23,25,26,28,29]
def cols1746 : List Int := [0,2,3,5,8,11,13,14,17,20,23,25,26,28,29]
def requiredD1746 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1746 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1746_eq : pairedProblem rows1746 cols1746 requiredD1746 requiredS1746 =
    MomentData.problem1746 := by rfl
theorem leaf1746 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1746++rows1746))
    (hc : (q.map Prod.snd).Perm (cols1746++cols1746))
    (hd : ∀ k ∈ requiredD1746, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1746, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1746 cols1746 requiredD1746 requiredS1746
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1746_eq] at model
  exact MomentData.excluded1746 ds ss model
def rows1747 : List Int := [0,2,3,5,8,11,14,15,17,20,23,25,26,28,29]
def cols1747 : List Int := [0,2,3,5,8,11,14,15,17,20,23,25,26,28,29]
def requiredD1747 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1747 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1747_eq : pairedProblem rows1747 cols1747 requiredD1747 requiredS1747 =
    MomentData.problem1747 := by rfl
theorem leaf1747 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1747++rows1747))
    (hc : (q.map Prod.snd).Perm (cols1747++cols1747))
    (hd : ∀ k ∈ requiredD1747, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1747, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1747 cols1747 requiredD1747 requiredS1747
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1747_eq] at model
  exact MomentData.excluded1747 ds ss model
def rows1748 : List Int := [0,2,3,5,8,11,14,15,17,20,23,25,26,28,29]
def cols1748 : List Int := [0,2,3,5,8,11,14,15,17,20,23,25,26,28,29]
def requiredD1748 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1748 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1748_eq : pairedProblem rows1748 cols1748 requiredD1748 requiredS1748 =
    MomentData.problem1748 := by rfl
theorem leaf1748 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1748++rows1748))
    (hc : (q.map Prod.snd).Perm (cols1748++cols1748))
    (hd : ∀ k ∈ requiredD1748, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1748, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1748 cols1748 requiredD1748 requiredS1748
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1748_eq] at model
  exact MomentData.excluded1748 ds ss model
def rows1749 : List Int := [0,2,3,5,8,11,14,16,17,20,23,25,26,28,29]
def cols1749 : List Int := [0,2,3,5,8,11,14,16,17,20,23,25,26,28,29]
def requiredD1749 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1749 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1749_eq : pairedProblem rows1749 cols1749 requiredD1749 requiredS1749 =
    MomentData.problem1749 := by rfl
theorem leaf1749 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1749++rows1749))
    (hc : (q.map Prod.snd).Perm (cols1749++cols1749))
    (hd : ∀ k ∈ requiredD1749, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1749, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1749 cols1749 requiredD1749 requiredS1749
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1749_eq] at model
  exact MomentData.excluded1749 ds ss model
def rows1750 : List Int := [0,2,3,5,8,11,14,16,17,20,23,25,26,28,29]
def cols1750 : List Int := [0,2,3,5,8,11,14,16,17,20,23,25,26,28,29]
def requiredD1750 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1750 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1750_eq : pairedProblem rows1750 cols1750 requiredD1750 requiredS1750 =
    MomentData.problem1750 := by rfl
theorem leaf1750 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1750++rows1750))
    (hc : (q.map Prod.snd).Perm (cols1750++cols1750))
    (hd : ∀ k ∈ requiredD1750, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1750, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1750 cols1750 requiredD1750 requiredS1750
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1750_eq] at model
  exact MomentData.excluded1750 ds ss model
def rows1751 : List Int := [0,2,3,5,8,11,14,17,18,20,23,25,26,28,29]
def cols1751 : List Int := [0,2,3,5,8,11,14,17,18,20,23,25,26,28,29]
def requiredD1751 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1751 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1751_eq : pairedProblem rows1751 cols1751 requiredD1751 requiredS1751 =
    MomentData.problem1751 := by rfl
theorem leaf1751 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1751++rows1751))
    (hc : (q.map Prod.snd).Perm (cols1751++cols1751))
    (hd : ∀ k ∈ requiredD1751, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1751, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1751 cols1751 requiredD1751 requiredS1751
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1751_eq] at model
  exact MomentData.excluded1751 ds ss model
def rows1752 : List Int := [0,2,3,5,8,11,14,17,18,20,23,25,26,28,29]
def cols1752 : List Int := [0,2,3,5,8,11,14,17,18,20,23,25,26,28,29]
def requiredD1752 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1752 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1752_eq : pairedProblem rows1752 cols1752 requiredD1752 requiredS1752 =
    MomentData.problem1752 := by rfl
theorem leaf1752 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1752++rows1752))
    (hc : (q.map Prod.snd).Perm (cols1752++cols1752))
    (hd : ∀ k ∈ requiredD1752, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1752, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1752 cols1752 requiredD1752 requiredS1752
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1752_eq] at model
  exact MomentData.excluded1752 ds ss model
def rows1753 : List Int := [1,2,3,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1753 : List Int := [1,2,3,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1753 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1753 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1753_eq : pairedProblem rows1753 cols1753 requiredD1753 requiredS1753 =
    MomentData.problem1753 := by rfl
theorem leaf1753 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1753++rows1753))
    (hc : (q.map Prod.snd).Perm (cols1753++cols1753))
    (hd : ∀ k ∈ requiredD1753, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1753, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1753 cols1753 requiredD1753 requiredS1753
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1753_eq] at model
  exact MomentData.excluded1753 ds ss model
def rows1754 : List Int := [1,2,3,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1754 : List Int := [1,2,3,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1754 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1754 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1754_eq : pairedProblem rows1754 cols1754 requiredD1754 requiredS1754 =
    MomentData.problem1754 := by rfl
theorem leaf1754 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1754++rows1754))
    (hc : (q.map Prod.snd).Perm (cols1754++cols1754))
    (hd : ∀ k ∈ requiredD1754, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1754, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1754 cols1754 requiredD1754 requiredS1754
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1754_eq] at model
  exact MomentData.excluded1754 ds ss model
def rows1755 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1755 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1755 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1755 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1755_eq : pairedProblem rows1755 cols1755 requiredD1755 requiredS1755 =
    MomentData.problem1755 := by rfl
theorem leaf1755 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1755++rows1755))
    (hc : (q.map Prod.snd).Perm (cols1755++cols1755))
    (hd : ∀ k ∈ requiredD1755, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1755, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1755 cols1755 requiredD1755 requiredS1755
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1755_eq] at model
  exact MomentData.excluded1755 ds ss model
def rows1756 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1756 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1756 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1756 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1756_eq : pairedProblem rows1756 cols1756 requiredD1756 requiredS1756 =
    MomentData.problem1756 := by rfl
theorem leaf1756 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1756++rows1756))
    (hc : (q.map Prod.snd).Perm (cols1756++cols1756))
    (hd : ∀ k ∈ requiredD1756, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1756, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1756 cols1756 requiredD1756 requiredS1756
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1756_eq] at model
  exact MomentData.excluded1756 ds ss model
def rows1757 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1757 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1757 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1757 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1757_eq : pairedProblem rows1757 cols1757 requiredD1757 requiredS1757 =
    MomentData.problem1757 := by rfl
theorem leaf1757 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1757++rows1757))
    (hc : (q.map Prod.snd).Perm (cols1757++cols1757))
    (hd : ∀ k ∈ requiredD1757, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1757, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1757 cols1757 requiredD1757 requiredS1757
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1757_eq] at model
  exact MomentData.excluded1757 ds ss model
def rows1758 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1758 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1758 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1758 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1758_eq : pairedProblem rows1758 cols1758 requiredD1758 requiredS1758 =
    MomentData.problem1758 := by rfl
theorem leaf1758 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1758++rows1758))
    (hc : (q.map Prod.snd).Perm (cols1758++cols1758))
    (hd : ∀ k ∈ requiredD1758, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1758, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1758 cols1758 requiredD1758 requiredS1758
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1758_eq] at model
  exact MomentData.excluded1758 ds ss model
def rows1759 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1759 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1759 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1759 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1759_eq : pairedProblem rows1759 cols1759 requiredD1759 requiredS1759 =
    MomentData.problem1759 := by rfl
theorem leaf1759 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1759++rows1759))
    (hc : (q.map Prod.snd).Perm (cols1759++cols1759))
    (hd : ∀ k ∈ requiredD1759, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1759, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1759 cols1759 requiredD1759 requiredS1759
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1759_eq] at model
  exact MomentData.excluded1759 ds ss model
def rows1760 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1760 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1760 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1760 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1760_eq : pairedProblem rows1760 cols1760 requiredD1760 requiredS1760 =
    MomentData.problem1760 := by rfl
theorem leaf1760 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1760++rows1760))
    (hc : (q.map Prod.snd).Perm (cols1760++cols1760))
    (hd : ∀ k ∈ requiredD1760, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1760, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1760 cols1760 requiredD1760 requiredS1760
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1760_eq] at model
  exact MomentData.excluded1760 ds ss model
def rows1761 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1761 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1761 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1761 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1761_eq : pairedProblem rows1761 cols1761 requiredD1761 requiredS1761 =
    MomentData.problem1761 := by rfl
theorem leaf1761 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1761++rows1761))
    (hc : (q.map Prod.snd).Perm (cols1761++cols1761))
    (hd : ∀ k ∈ requiredD1761, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1761, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1761 cols1761 requiredD1761 requiredS1761
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1761_eq] at model
  exact MomentData.excluded1761 ds ss model
def rows1762 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1762 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1762 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1762 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1762_eq : pairedProblem rows1762 cols1762 requiredD1762 requiredS1762 =
    MomentData.problem1762 := by rfl
theorem leaf1762 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1762++rows1762))
    (hc : (q.map Prod.snd).Perm (cols1762++cols1762))
    (hd : ∀ k ∈ requiredD1762, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1762, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1762 cols1762 requiredD1762 requiredS1762
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1762_eq] at model
  exact MomentData.excluded1762 ds ss model
def rows1763 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1763 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1763 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1763 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1763_eq : pairedProblem rows1763 cols1763 requiredD1763 requiredS1763 =
    MomentData.problem1763 := by rfl
theorem leaf1763 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1763++rows1763))
    (hc : (q.map Prod.snd).Perm (cols1763++cols1763))
    (hd : ∀ k ∈ requiredD1763, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1763, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1763 cols1763 requiredD1763 requiredS1763
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1763_eq] at model
  exact MomentData.excluded1763 ds ss model
def rows1764 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1764 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1764 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1764 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1764_eq : pairedProblem rows1764 cols1764 requiredD1764 requiredS1764 =
    MomentData.problem1764 := by rfl
theorem leaf1764 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1764++rows1764))
    (hc : (q.map Prod.snd).Perm (cols1764++cols1764))
    (hd : ∀ k ∈ requiredD1764, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1764, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1764 cols1764 requiredD1764 requiredS1764
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1764_eq] at model
  exact MomentData.excluded1764 ds ss model
def rows1765 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1765 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1765 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1765 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1765_eq : pairedProblem rows1765 cols1765 requiredD1765 requiredS1765 =
    MomentData.problem1765 := by rfl
theorem leaf1765 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1765++rows1765))
    (hc : (q.map Prod.snd).Perm (cols1765++cols1765))
    (hd : ∀ k ∈ requiredD1765, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1765, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1765 cols1765 requiredD1765 requiredS1765
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1765_eq] at model
  exact MomentData.excluded1765 ds ss model
def rows1766 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1766 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1766 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1766 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1766_eq : pairedProblem rows1766 cols1766 requiredD1766 requiredS1766 =
    MomentData.problem1766 := by rfl
theorem leaf1766 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1766++rows1766))
    (hc : (q.map Prod.snd).Perm (cols1766++cols1766))
    (hd : ∀ k ∈ requiredD1766, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1766, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1766 cols1766 requiredD1766 requiredS1766
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1766_eq] at model
  exact MomentData.excluded1766 ds ss model
def rows1767 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1767 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1767 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1767 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1767_eq : pairedProblem rows1767 cols1767 requiredD1767 requiredS1767 =
    MomentData.problem1767 := by rfl
theorem leaf1767 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1767++rows1767))
    (hc : (q.map Prod.snd).Perm (cols1767++cols1767))
    (hd : ∀ k ∈ requiredD1767, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1767, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1767 cols1767 requiredD1767 requiredS1767
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1767_eq] at model
  exact MomentData.excluded1767 ds ss model
def rows1768 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1768 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1768 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1768 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1768_eq : pairedProblem rows1768 cols1768 requiredD1768 requiredS1768 =
    MomentData.problem1768 := by rfl
theorem leaf1768 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1768++rows1768))
    (hc : (q.map Prod.snd).Perm (cols1768++cols1768))
    (hd : ∀ k ∈ requiredD1768, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1768, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1768 cols1768 requiredD1768 requiredS1768
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1768_eq] at model
  exact MomentData.excluded1768 ds ss model
def rows1769 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1769 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1769 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1769 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1769_eq : pairedProblem rows1769 cols1769 requiredD1769 requiredS1769 =
    MomentData.problem1769 := by rfl
theorem leaf1769 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1769++rows1769))
    (hc : (q.map Prod.snd).Perm (cols1769++cols1769))
    (hd : ∀ k ∈ requiredD1769, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1769, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1769 cols1769 requiredD1769 requiredS1769
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1769_eq] at model
  exact MomentData.excluded1769 ds ss model
def rows1770 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1770 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1770 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1770 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1770_eq : pairedProblem rows1770 cols1770 requiredD1770 requiredS1770 =
    MomentData.problem1770 := by rfl
theorem leaf1770 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1770++rows1770))
    (hc : (q.map Prod.snd).Perm (cols1770++cols1770))
    (hd : ∀ k ∈ requiredD1770, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1770, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1770 cols1770 requiredD1770 requiredS1770
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1770_eq] at model
  exact MomentData.excluded1770 ds ss model
def rows1771 : List Int := [0,2,3,5,8,11,14,17,19,20,23,25,26,28,29]
def cols1771 : List Int := [0,2,3,5,8,11,14,17,19,20,23,25,26,28,29]
def requiredD1771 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1771 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1771_eq : pairedProblem rows1771 cols1771 requiredD1771 requiredS1771 =
    MomentData.problem1771 := by rfl
theorem leaf1771 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1771++rows1771))
    (hc : (q.map Prod.snd).Perm (cols1771++cols1771))
    (hd : ∀ k ∈ requiredD1771, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1771, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1771 cols1771 requiredD1771 requiredS1771
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1771_eq] at model
  exact MomentData.excluded1771 ds ss model
def rows1772 : List Int := [0,2,3,5,8,11,14,17,19,20,23,25,26,28,29]
def cols1772 : List Int := [0,2,3,5,8,11,14,17,19,20,23,25,26,28,29]
def requiredD1772 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1772 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1772_eq : pairedProblem rows1772 cols1772 requiredD1772 requiredS1772 =
    MomentData.problem1772 := by rfl
theorem leaf1772 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1772++rows1772))
    (hc : (q.map Prod.snd).Perm (cols1772++cols1772))
    (hd : ∀ k ∈ requiredD1772, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1772, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1772 cols1772 requiredD1772 requiredS1772
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1772_eq] at model
  exact MomentData.excluded1772 ds ss model
def rows1773 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1773 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1773 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1773 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1773_eq : pairedProblem rows1773 cols1773 requiredD1773 requiredS1773 =
    MomentData.problem1773 := by rfl
theorem leaf1773 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1773++rows1773))
    (hc : (q.map Prod.snd).Perm (cols1773++cols1773))
    (hd : ∀ k ∈ requiredD1773, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1773, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1773 cols1773 requiredD1773 requiredS1773
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1773_eq] at model
  exact MomentData.excluded1773 ds ss model
def rows1774 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1774 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1774 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1774 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1774_eq : pairedProblem rows1774 cols1774 requiredD1774 requiredS1774 =
    MomentData.problem1774 := by rfl
theorem leaf1774 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1774++rows1774))
    (hc : (q.map Prod.snd).Perm (cols1774++cols1774))
    (hd : ∀ k ∈ requiredD1774, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1774, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1774 cols1774 requiredD1774 requiredS1774
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1774_eq] at model
  exact MomentData.excluded1774 ds ss model
def rows1775 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1775 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1775 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1775 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem1775_eq : pairedProblem rows1775 cols1775 requiredD1775 requiredS1775 =
    MomentData.problem1775 := by rfl
theorem leaf1775 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1775++rows1775))
    (hc : (q.map Prod.snd).Perm (cols1775++cols1775))
    (hd : ∀ k ∈ requiredD1775, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1775, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1775 cols1775 requiredD1775 requiredS1775
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1775_eq] at model
  exact MomentData.excluded1775 ds ss model
def rows1776 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1776 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1776 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1776 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1776_eq : pairedProblem rows1776 cols1776 requiredD1776 requiredS1776 =
    MomentData.problem1776 := by rfl
theorem leaf1776 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1776++rows1776))
    (hc : (q.map Prod.snd).Perm (cols1776++cols1776))
    (hd : ∀ k ∈ requiredD1776, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1776, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1776 cols1776 requiredD1776 requiredS1776
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1776_eq] at model
  exact MomentData.excluded1776 ds ss model
def rows1777 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols1777 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD1777 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1777 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,44]
theorem problem1777_eq : pairedProblem rows1777 cols1777 requiredD1777 requiredS1777 =
    MomentData.problem1777 := by rfl
theorem leaf1777 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1777++rows1777))
    (hc : (q.map Prod.snd).Perm (cols1777++cols1777))
    (hd : ∀ k ∈ requiredD1777, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1777, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1777 cols1777 requiredD1777 requiredS1777
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1777_eq] at model
  exact MomentData.excluded1777 ds ss model
def rows1778 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols1778 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1778 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1778 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44,47]
theorem problem1778_eq : pairedProblem rows1778 cols1778 requiredD1778 requiredS1778 =
    MomentData.problem1778 := by rfl
theorem leaf1778 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1778++rows1778))
    (hc : (q.map Prod.snd).Perm (cols1778++cols1778))
    (hd : ∀ k ∈ requiredD1778, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1778, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1778 cols1778 requiredD1778 requiredS1778
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1778_eq] at model
  exact MomentData.excluded1778 ds ss model
def rows1779 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols1779 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1779 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1779 : List Int := [11,14,17,20,21,23,26,29,32,35,38,41,44,47]
theorem problem1779_eq : pairedProblem rows1779 cols1779 requiredD1779 requiredS1779 =
    MomentData.problem1779 := by rfl
theorem leaf1779 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1779++rows1779))
    (hc : (q.map Prod.snd).Perm (cols1779++cols1779))
    (hd : ∀ k ∈ requiredD1779, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1779, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1779 cols1779 requiredD1779 requiredS1779
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1779_eq] at model
  exact MomentData.excluded1779 ds ss model
def rows1780 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols1780 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1780 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1780 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1780_eq : pairedProblem rows1780 cols1780 requiredD1780 requiredS1780 =
    MomentData.problem1780 := by rfl
theorem leaf1780 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1780++rows1780))
    (hc : (q.map Prod.snd).Perm (cols1780++cols1780))
    (hd : ∀ k ∈ requiredD1780, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1780, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1780 cols1780 requiredD1780 requiredS1780
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1780_eq] at model
  exact MomentData.excluded1780 ds ss model
def rows1781 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def cols1781 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1781 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1781 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem1781_eq : pairedProblem rows1781 cols1781 requiredD1781 requiredS1781 =
    MomentData.problem1781 := by rfl
theorem leaf1781 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1781++rows1781))
    (hc : (q.map Prod.snd).Perm (cols1781++cols1781))
    (hd : ∀ k ∈ requiredD1781, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1781, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1781 cols1781 requiredD1781 requiredS1781
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1781_eq] at model
  exact MomentData.excluded1781 ds ss model
def rows1782 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def cols1782 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def requiredD1782 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1782 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1782_eq : pairedProblem rows1782 cols1782 requiredD1782 requiredS1782 =
    MomentData.problem1782 := by rfl
theorem leaf1782 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1782++rows1782))
    (hc : (q.map Prod.snd).Perm (cols1782++cols1782))
    (hd : ∀ k ∈ requiredD1782, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1782, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1782 cols1782 requiredD1782 requiredS1782
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1782_eq] at model
  exact MomentData.excluded1782 ds ss model
def rows1783 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def cols1783 : List Int := [0,2,3,5,8,11,14,17,20,21,23,25,26,28,29]
def requiredD1783 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1783 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1783_eq : pairedProblem rows1783 cols1783 requiredD1783 requiredS1783 =
    MomentData.problem1783 := by rfl
theorem leaf1783 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1783++rows1783))
    (hc : (q.map Prod.snd).Perm (cols1783++cols1783))
    (hd : ∀ k ∈ requiredD1783, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1783, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1783 cols1783 requiredD1783 requiredS1783
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1783_eq] at model
  exact MomentData.excluded1783 ds ss model
def rows1784 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols1784 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD1784 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1784 : List Int := [7,10,13,16,19,22,25,28,31,33,34,37,40,43,46]
theorem problem1784_eq : pairedProblem rows1784 cols1784 requiredD1784 requiredS1784 =
    MomentData.problem1784 := by rfl
theorem leaf1784 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1784++rows1784))
    (hc : (q.map Prod.snd).Perm (cols1784++cols1784))
    (hd : ∀ k ∈ requiredD1784, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1784, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1784 cols1784 requiredD1784 requiredS1784
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1784_eq] at model
  exact MomentData.excluded1784 ds ss model
def rows1785 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols1785 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD1785 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1785 : List Int := [10,13,16,19,22,25,28,31,33,34,37,40,43,46]
theorem problem1785_eq : pairedProblem rows1785 cols1785 requiredD1785 requiredS1785 =
    MomentData.problem1785 := by rfl
theorem leaf1785 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1785++rows1785))
    (hc : (q.map Prod.snd).Perm (cols1785++cols1785))
    (hd : ∀ k ∈ requiredD1785, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1785, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1785 cols1785 requiredD1785 requiredS1785
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1785_eq] at model
  exact MomentData.excluded1785 ds ss model
def rows1786 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols1786 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD1786 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1786 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1786_eq : pairedProblem rows1786 cols1786 requiredD1786 requiredS1786 =
    MomentData.problem1786 := by rfl
theorem leaf1786 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1786++rows1786))
    (hc : (q.map Prod.snd).Perm (cols1786++cols1786))
    (hd : ∀ k ∈ requiredD1786, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1786, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1786 cols1786 requiredD1786 requiredS1786
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1786_eq] at model
  exact MomentData.excluded1786 ds ss model
def rows1787 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def cols1787 : List Int := [0,2,3,5,8,11,14,17,20,22,23,25,26,28,29]
def requiredD1787 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1787 : List Int := [7,10,13,16,19,22,25,28,31,33,34,37,40,43]
theorem problem1787_eq : pairedProblem rows1787 cols1787 requiredD1787 requiredS1787 =
    MomentData.problem1787 := by rfl
theorem leaf1787 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1787++rows1787))
    (hc : (q.map Prod.snd).Perm (cols1787++cols1787))
    (hd : ∀ k ∈ requiredD1787, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1787, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1787 cols1787 requiredD1787 requiredS1787
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1787_eq] at model
  exact MomentData.excluded1787 ds ss model
def rows1788 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def cols1788 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1788 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1788 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1788_eq : pairedProblem rows1788 cols1788 requiredD1788 requiredS1788 =
    MomentData.problem1788 := by rfl
theorem leaf1788 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1788++rows1788))
    (hc : (q.map Prod.snd).Perm (cols1788++cols1788))
    (hd : ∀ k ∈ requiredD1788, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1788, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1788 cols1788 requiredD1788 requiredS1788
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1788_eq] at model
  exact MomentData.excluded1788 ds ss model
def rows1789 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def cols1789 : List Int := [1,2,4,6,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1789 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1789 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1789_eq : pairedProblem rows1789 cols1789 requiredD1789 requiredS1789 =
    MomentData.problem1789 := by rfl
theorem leaf1789 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1789++rows1789))
    (hc : (q.map Prod.snd).Perm (cols1789++cols1789))
    (hd : ∀ k ∈ requiredD1789, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1789, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1789 cols1789 requiredD1789 requiredS1789
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1789_eq] at model
  exact MomentData.excluded1789 ds ss model
def rows1790 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1790 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1790 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1790 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1790_eq : pairedProblem rows1790 cols1790 requiredD1790 requiredS1790 =
    MomentData.problem1790 := by rfl
theorem leaf1790 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1790++rows1790))
    (hc : (q.map Prod.snd).Perm (cols1790++cols1790))
    (hd : ∀ k ∈ requiredD1790, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1790, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1790 cols1790 requiredD1790 requiredS1790
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1790_eq] at model
  exact MomentData.excluded1790 ds ss model
def rows1791 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def cols1791 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD1791 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1791 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,46]
theorem problem1791_eq : pairedProblem rows1791 cols1791 requiredD1791 requiredS1791 =
    MomentData.problem1791 := by rfl
theorem leaf1791 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1791++rows1791))
    (hc : (q.map Prod.snd).Perm (cols1791++cols1791))
    (hd : ∀ k ∈ requiredD1791, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1791, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1791 cols1791 requiredD1791 requiredS1791
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1791_eq] at model
  exact MomentData.excluded1791 ds ss model
#print axioms leaf1664
end Gardner.Kernel.MomentContexts
