import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1792 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1792 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1792 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1792 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1792_eq : pairedProblem rows1792 cols1792 requiredD1792 requiredS1792 =
    MomentData.problem1792 := by rfl
theorem leaf1792 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1792++rows1792))
    (hc : (q.map Prod.snd).Perm (cols1792++cols1792))
    (hd : ∀ k ∈ requiredD1792, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1792, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1792 cols1792 requiredD1792 requiredS1792
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1792_eq] at model
  exact MomentData.excluded1792 ds ss model
def rows1793 : List Int := [0,2,3,5,6,8,9,11,14,17,20,23,26,28,29]
def cols1793 : List Int := [0,2,3,5,6,8,9,11,14,17,20,23,26,28,29]
def requiredD1793 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1793 : List Int := [13,16,19,22,25,26,28,31,34,37,40,43,46,49,52]
theorem problem1793_eq : pairedProblem rows1793 cols1793 requiredD1793 requiredS1793 =
    MomentData.problem1793 := by rfl
theorem leaf1793 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1793++rows1793))
    (hc : (q.map Prod.snd).Perm (cols1793++cols1793))
    (hd : ∀ k ∈ requiredD1793, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1793, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1793 cols1793 requiredD1793 requiredS1793
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1793_eq] at model
  exact MomentData.excluded1793 ds ss model
def rows1794 : List Int := [0,2,3,5,8,11,14,17,20,23,24,25,26,28,29]
def cols1794 : List Int := [0,2,3,5,8,11,14,17,20,23,24,25,26,28,29]
def requiredD1794 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1794 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1794_eq : pairedProblem rows1794 cols1794 requiredD1794 requiredS1794 =
    MomentData.problem1794 := by rfl
theorem leaf1794 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1794++rows1794))
    (hc : (q.map Prod.snd).Perm (cols1794++cols1794))
    (hd : ∀ k ∈ requiredD1794, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1794, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1794 cols1794 requiredD1794 requiredS1794
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1794_eq] at model
  exact MomentData.excluded1794 ds ss model
def rows1795 : List Int := [0,2,3,5,8,11,14,17,20,23,24,25,26,28,29]
def cols1795 : List Int := [0,2,3,5,8,11,14,17,20,23,24,25,26,28,29]
def requiredD1795 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1795 : List Int := [10,13,16,19,22,23,25,28,31,33,34,37,40,43,46]
theorem problem1795_eq : pairedProblem rows1795 cols1795 requiredD1795 requiredS1795 =
    MomentData.problem1795 := by rfl
theorem leaf1795 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1795++rows1795))
    (hc : (q.map Prod.snd).Perm (cols1795++cols1795))
    (hd : ∀ k ∈ requiredD1795, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1795, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1795 cols1795 requiredD1795 requiredS1795
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1795_eq] at model
  exact MomentData.excluded1795 ds ss model
def rows1796 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1796 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1796 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1796 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1796_eq : pairedProblem rows1796 cols1796 requiredD1796 requiredS1796 =
    MomentData.problem1796 := by rfl
theorem leaf1796 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1796++rows1796))
    (hc : (q.map Prod.snd).Perm (cols1796++cols1796))
    (hd : ∀ k ∈ requiredD1796, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1796, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1796 cols1796 requiredD1796 requiredS1796
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1796_eq] at model
  exact MomentData.excluded1796 ds ss model
def rows1797 : List Int := [1,2,4,7,8,10,13,16,19,22,24,25,27,28,29]
def cols1797 : List Int := [1,2,4,7,8,10,13,16,19,22,24,25,27,28,29]
def requiredD1797 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1797 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1797_eq : pairedProblem rows1797 cols1797 requiredD1797 requiredS1797 =
    MomentData.problem1797 := by rfl
theorem leaf1797 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1797++rows1797))
    (hc : (q.map Prod.snd).Perm (cols1797++cols1797))
    (hd : ∀ k ∈ requiredD1797, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1797, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1797 cols1797 requiredD1797 requiredS1797
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1797_eq] at model
  exact MomentData.excluded1797 ds ss model
def rows1798 : List Int := [1,2,4,7,8,10,13,16,19,22,24,25,27,28,29]
def cols1798 : List Int := [1,2,4,7,8,10,13,16,19,22,24,25,27,28,29]
def requiredD1798 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1798 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1798_eq : pairedProblem rows1798 cols1798 requiredD1798 requiredS1798 =
    MomentData.problem1798 := by rfl
theorem leaf1798 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1798++rows1798))
    (hc : (q.map Prod.snd).Perm (cols1798++cols1798))
    (hd : ∀ k ∈ requiredD1798, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1798, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1798 cols1798 requiredD1798 requiredS1798
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1798_eq] at model
  exact MomentData.excluded1798 ds ss model
def rows1799 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1799 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1799 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1799 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1799_eq : pairedProblem rows1799 cols1799 requiredD1799 requiredS1799 =
    MomentData.problem1799 := by rfl
theorem leaf1799 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1799++rows1799))
    (hc : (q.map Prod.snd).Perm (cols1799++cols1799))
    (hd : ∀ k ∈ requiredD1799, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1799, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1799 cols1799 requiredD1799 requiredS1799
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1799_eq] at model
  exact MomentData.excluded1799 ds ss model
def rows1800 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1800 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1800 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1800 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1800_eq : pairedProblem rows1800 cols1800 requiredD1800 requiredS1800 =
    MomentData.problem1800 := by rfl
theorem leaf1800 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1800++rows1800))
    (hc : (q.map Prod.snd).Perm (cols1800++cols1800))
    (hd : ∀ k ∈ requiredD1800, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1800, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1800 cols1800 requiredD1800 requiredS1800
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1800_eq] at model
  exact MomentData.excluded1800 ds ss model
def rows1801 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1801 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1801 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1801 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1801_eq : pairedProblem rows1801 cols1801 requiredD1801 requiredS1801 =
    MomentData.problem1801 := by rfl
theorem leaf1801 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1801++rows1801))
    (hc : (q.map Prod.snd).Perm (cols1801++cols1801))
    (hd : ∀ k ∈ requiredD1801, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1801, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1801 cols1801 requiredD1801 requiredS1801
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1801_eq] at model
  exact MomentData.excluded1801 ds ss model
def rows1802 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1802 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1802 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1802 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1802_eq : pairedProblem rows1802 cols1802 requiredD1802 requiredS1802 =
    MomentData.problem1802 := by rfl
theorem leaf1802 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1802++rows1802))
    (hc : (q.map Prod.snd).Perm (cols1802++cols1802))
    (hd : ∀ k ∈ requiredD1802, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1802, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1802 cols1802 requiredD1802 requiredS1802
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1802_eq] at model
  exact MomentData.excluded1802 ds ss model
def rows1803 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1803 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1803 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1803 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1803_eq : pairedProblem rows1803 cols1803 requiredD1803 requiredS1803 =
    MomentData.problem1803 := by rfl
theorem leaf1803 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1803++rows1803))
    (hc : (q.map Prod.snd).Perm (cols1803++cols1803))
    (hd : ∀ k ∈ requiredD1803, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1803, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1803 cols1803 requiredD1803 requiredS1803
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1803_eq] at model
  exact MomentData.excluded1803 ds ss model
def rows1804 : List Int := [1,2,4,7,9,10,13,16,19,22,24,25,27,28,29]
def cols1804 : List Int := [1,2,4,7,9,10,13,16,19,22,24,25,27,28,29]
def requiredD1804 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1804 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1804_eq : pairedProblem rows1804 cols1804 requiredD1804 requiredS1804 =
    MomentData.problem1804 := by rfl
theorem leaf1804 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1804++rows1804))
    (hc : (q.map Prod.snd).Perm (cols1804++cols1804))
    (hd : ∀ k ∈ requiredD1804, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1804, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1804 cols1804 requiredD1804 requiredS1804
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1804_eq] at model
  exact MomentData.excluded1804 ds ss model
def rows1805 : List Int := [1,2,4,7,9,10,13,16,19,22,24,25,27,28,29]
def cols1805 : List Int := [1,2,4,7,9,10,13,16,19,22,24,25,27,28,29]
def requiredD1805 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1805 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1805_eq : pairedProblem rows1805 cols1805 requiredD1805 requiredS1805 =
    MomentData.problem1805 := by rfl
theorem leaf1805 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1805++rows1805))
    (hc : (q.map Prod.snd).Perm (cols1805++cols1805))
    (hd : ∀ k ∈ requiredD1805, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1805, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1805 cols1805 requiredD1805 requiredS1805
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1805_eq] at model
  exact MomentData.excluded1805 ds ss model
def rows1806 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1806 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1806 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1806 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1806_eq : pairedProblem rows1806 cols1806 requiredD1806 requiredS1806 =
    MomentData.problem1806 := by rfl
theorem leaf1806 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1806++rows1806))
    (hc : (q.map Prod.snd).Perm (cols1806++cols1806))
    (hd : ∀ k ∈ requiredD1806, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1806, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1806 cols1806 requiredD1806 requiredS1806
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1806_eq] at model
  exact MomentData.excluded1806 ds ss model
def rows1807 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def cols1807 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def requiredD1807 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1807 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1807_eq : pairedProblem rows1807 cols1807 requiredD1807 requiredS1807 =
    MomentData.problem1807 := by rfl
theorem leaf1807 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1807++rows1807))
    (hc : (q.map Prod.snd).Perm (cols1807++cols1807))
    (hd : ∀ k ∈ requiredD1807, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1807, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1807 cols1807 requiredD1807 requiredS1807
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1807_eq] at model
  exact MomentData.excluded1807 ds ss model
def rows1808 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def cols1808 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def requiredD1808 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1808 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1808_eq : pairedProblem rows1808 cols1808 requiredD1808 requiredS1808 =
    MomentData.problem1808 := by rfl
theorem leaf1808 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1808++rows1808))
    (hc : (q.map Prod.snd).Perm (cols1808++cols1808))
    (hd : ∀ k ∈ requiredD1808, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1808, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1808 cols1808 requiredD1808 requiredS1808
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1808_eq] at model
  exact MomentData.excluded1808 ds ss model
def rows1809 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1809 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def requiredD1809 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1809 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1809_eq : pairedProblem rows1809 cols1809 requiredD1809 requiredS1809 =
    MomentData.problem1809 := by rfl
theorem leaf1809 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1809++rows1809))
    (hc : (q.map Prod.snd).Perm (cols1809++cols1809))
    (hd : ∀ k ∈ requiredD1809, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1809, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1809 cols1809 requiredD1809 requiredS1809
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1809_eq] at model
  exact MomentData.excluded1809 ds ss model
def rows1810 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1810 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def requiredD1810 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1810 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1810_eq : pairedProblem rows1810 cols1810 requiredD1810 requiredS1810 =
    MomentData.problem1810 := by rfl
theorem leaf1810 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1810++rows1810))
    (hc : (q.map Prod.snd).Perm (cols1810++cols1810))
    (hd : ∀ k ∈ requiredD1810, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1810, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1810 cols1810 requiredD1810 requiredS1810
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1810_eq] at model
  exact MomentData.excluded1810 ds ss model
def rows1811 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1811 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1811 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1811 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1811_eq : pairedProblem rows1811 cols1811 requiredD1811 requiredS1811 =
    MomentData.problem1811 := by rfl
theorem leaf1811 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1811++rows1811))
    (hc : (q.map Prod.snd).Perm (cols1811++cols1811))
    (hd : ∀ k ∈ requiredD1811, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1811, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1811 cols1811 requiredD1811 requiredS1811
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1811_eq] at model
  exact MomentData.excluded1811 ds ss model
def rows1812 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols1812 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def requiredD1812 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1812 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1812_eq : pairedProblem rows1812 cols1812 requiredD1812 requiredS1812 =
    MomentData.problem1812 := by rfl
theorem leaf1812 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1812++rows1812))
    (hc : (q.map Prod.snd).Perm (cols1812++cols1812))
    (hd : ∀ k ∈ requiredD1812, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1812, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1812 cols1812 requiredD1812 requiredS1812
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1812_eq] at model
  exact MomentData.excluded1812 ds ss model
def rows1813 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols1813 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def requiredD1813 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1813 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1813_eq : pairedProblem rows1813 cols1813 requiredD1813 requiredS1813 =
    MomentData.problem1813 := by rfl
theorem leaf1813 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1813++rows1813))
    (hc : (q.map Prod.snd).Perm (cols1813++cols1813))
    (hd : ∀ k ∈ requiredD1813, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1813, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1813 cols1813 requiredD1813 requiredS1813
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1813_eq] at model
  exact MomentData.excluded1813 ds ss model
def rows1814 : List Int := [1,2,4,7,10,11,13,16,19,22,24,25,27,28,29]
def cols1814 : List Int := [1,2,4,7,10,11,13,16,19,22,24,25,27,28,29]
def requiredD1814 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1814 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1814_eq : pairedProblem rows1814 cols1814 requiredD1814 requiredS1814 =
    MomentData.problem1814 := by rfl
theorem leaf1814 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1814++rows1814))
    (hc : (q.map Prod.snd).Perm (cols1814++cols1814))
    (hd : ∀ k ∈ requiredD1814, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1814, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1814 cols1814 requiredD1814 requiredS1814
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1814_eq] at model
  exact MomentData.excluded1814 ds ss model
def rows1815 : List Int := [1,2,4,7,10,11,13,16,19,22,24,25,27,28,29]
def cols1815 : List Int := [1,2,4,7,10,11,13,16,19,22,24,25,27,28,29]
def requiredD1815 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1815 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1815_eq : pairedProblem rows1815 cols1815 requiredD1815 requiredS1815 =
    MomentData.problem1815 := by rfl
theorem leaf1815 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1815++rows1815))
    (hc : (q.map Prod.snd).Perm (cols1815++cols1815))
    (hd : ∀ k ∈ requiredD1815, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1815, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1815 cols1815 requiredD1815 requiredS1815
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1815_eq] at model
  exact MomentData.excluded1815 ds ss model
def rows1816 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1816 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1816 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1816 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem1816_eq : pairedProblem rows1816 cols1816 requiredD1816 requiredS1816 =
    MomentData.problem1816 := by rfl
theorem leaf1816 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1816++rows1816))
    (hc : (q.map Prod.snd).Perm (cols1816++cols1816))
    (hd : ∀ k ∈ requiredD1816, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1816, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1816 cols1816 requiredD1816 requiredS1816
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1816_eq] at model
  exact MomentData.excluded1816 ds ss model
def rows1817 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1817 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1817 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1817 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem1817_eq : pairedProblem rows1817 cols1817 requiredD1817 requiredS1817 =
    MomentData.problem1817 := by rfl
theorem leaf1817 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1817++rows1817))
    (hc : (q.map Prod.snd).Perm (cols1817++cols1817))
    (hd : ∀ k ∈ requiredD1817, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1817, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1817 cols1817 requiredD1817 requiredS1817
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1817_eq] at model
  exact MomentData.excluded1817 ds ss model
def rows1818 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1818 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1818 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1818 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,45]
theorem problem1818_eq : pairedProblem rows1818 cols1818 requiredD1818 requiredS1818 =
    MomentData.problem1818 := by rfl
theorem leaf1818 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1818++rows1818))
    (hc : (q.map Prod.snd).Perm (cols1818++cols1818))
    (hd : ∀ k ∈ requiredD1818, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1818, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1818 cols1818 requiredD1818 requiredS1818
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1818_eq] at model
  exact MomentData.excluded1818 ds ss model
def rows1819 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1819 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1819 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1819 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1819_eq : pairedProblem rows1819 cols1819 requiredD1819 requiredS1819 =
    MomentData.problem1819 := by rfl
theorem leaf1819 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1819++rows1819))
    (hc : (q.map Prod.snd).Perm (cols1819++cols1819))
    (hd : ∀ k ∈ requiredD1819, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1819, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1819 cols1819 requiredD1819 requiredS1819
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1819_eq] at model
  exact MomentData.excluded1819 ds ss model
def rows1820 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols1820 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def requiredD1820 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1820 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1820_eq : pairedProblem rows1820 cols1820 requiredD1820 requiredS1820 =
    MomentData.problem1820 := by rfl
theorem leaf1820 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1820++rows1820))
    (hc : (q.map Prod.snd).Perm (cols1820++cols1820))
    (hd : ∀ k ∈ requiredD1820, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1820, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1820 cols1820 requiredD1820 requiredS1820
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1820_eq] at model
  exact MomentData.excluded1820 ds ss model
def rows1821 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols1821 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def requiredD1821 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1821 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1821_eq : pairedProblem rows1821 cols1821 requiredD1821 requiredS1821 =
    MomentData.problem1821 := by rfl
theorem leaf1821 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1821++rows1821))
    (hc : (q.map Prod.snd).Perm (cols1821++cols1821))
    (hd : ∀ k ∈ requiredD1821, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1821, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1821 cols1821 requiredD1821 requiredS1821
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1821_eq] at model
  exact MomentData.excluded1821 ds ss model
def rows1822 : List Int := [1,2,4,7,10,12,13,16,19,22,24,25,27,28,29]
def cols1822 : List Int := [1,2,4,7,10,12,13,16,19,22,24,25,27,28,29]
def requiredD1822 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1822 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1822_eq : pairedProblem rows1822 cols1822 requiredD1822 requiredS1822 =
    MomentData.problem1822 := by rfl
theorem leaf1822 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1822++rows1822))
    (hc : (q.map Prod.snd).Perm (cols1822++cols1822))
    (hd : ∀ k ∈ requiredD1822, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1822, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1822 cols1822 requiredD1822 requiredS1822
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1822_eq] at model
  exact MomentData.excluded1822 ds ss model
def rows1823 : List Int := [1,2,4,7,10,12,13,16,19,22,24,25,27,28,29]
def cols1823 : List Int := [1,2,4,7,10,12,13,16,19,22,24,25,27,28,29]
def requiredD1823 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1823 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1823_eq : pairedProblem rows1823 cols1823 requiredD1823 requiredS1823 =
    MomentData.problem1823 := by rfl
theorem leaf1823 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1823++rows1823))
    (hc : (q.map Prod.snd).Perm (cols1823++cols1823))
    (hd : ∀ k ∈ requiredD1823, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1823, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1823 cols1823 requiredD1823 requiredS1823
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1823_eq] at model
  exact MomentData.excluded1823 ds ss model
def rows1824 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1824 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def requiredD1824 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1824 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1824_eq : pairedProblem rows1824 cols1824 requiredD1824 requiredS1824 =
    MomentData.problem1824 := by rfl
theorem leaf1824 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1824++rows1824))
    (hc : (q.map Prod.snd).Perm (cols1824++cols1824))
    (hd : ∀ k ∈ requiredD1824, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1824, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1824 cols1824 requiredD1824 requiredS1824
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1824_eq] at model
  exact MomentData.excluded1824 ds ss model
def rows1825 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1825 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def requiredD1825 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1825 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1825_eq : pairedProblem rows1825 cols1825 requiredD1825 requiredS1825 =
    MomentData.problem1825 := by rfl
theorem leaf1825 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1825++rows1825))
    (hc : (q.map Prod.snd).Perm (cols1825++cols1825))
    (hd : ∀ k ∈ requiredD1825, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1825, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1825 cols1825 requiredD1825 requiredS1825
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1825_eq] at model
  exact MomentData.excluded1825 ds ss model
def rows1826 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def cols1826 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def requiredD1826 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1826 : List Int := [9,22,23,24,25,26,27,28,29,30,31,32,33,34,47]
theorem problem1826_eq : pairedProblem rows1826 cols1826 requiredD1826 requiredS1826 =
    MomentData.problem1826 := by rfl
theorem leaf1826 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1826++rows1826))
    (hc : (q.map Prod.snd).Perm (cols1826++cols1826))
    (hd : ∀ k ∈ requiredD1826, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1826, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1826 cols1826 requiredD1826 requiredS1826
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1826_eq] at model
  exact MomentData.excluded1826 ds ss model
def rows1827 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def cols1827 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def requiredD1827 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1827 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1827_eq : pairedProblem rows1827 cols1827 requiredD1827 requiredS1827 =
    MomentData.problem1827 := by rfl
theorem leaf1827 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1827++rows1827))
    (hc : (q.map Prod.snd).Perm (cols1827++cols1827))
    (hd : ∀ k ∈ requiredD1827, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1827, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1827 cols1827 requiredD1827 requiredS1827
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1827_eq] at model
  exact MomentData.excluded1827 ds ss model
def rows1828 : List Int := [1,2,4,7,10,13,14,16,19,22,24,25,27,28,29]
def cols1828 : List Int := [1,2,4,7,10,13,14,16,19,22,24,25,27,28,29]
def requiredD1828 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1828 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1828_eq : pairedProblem rows1828 cols1828 requiredD1828 requiredS1828 =
    MomentData.problem1828 := by rfl
theorem leaf1828 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1828++rows1828))
    (hc : (q.map Prod.snd).Perm (cols1828++cols1828))
    (hd : ∀ k ∈ requiredD1828, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1828, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1828 cols1828 requiredD1828 requiredS1828
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1828_eq] at model
  exact MomentData.excluded1828 ds ss model
def rows1829 : List Int := [1,2,4,7,10,13,14,16,19,22,24,25,27,28,29]
def cols1829 : List Int := [1,2,4,7,10,13,14,16,19,22,24,25,27,28,29]
def requiredD1829 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1829 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1829_eq : pairedProblem rows1829 cols1829 requiredD1829 requiredS1829 =
    MomentData.problem1829 := by rfl
theorem leaf1829 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1829++rows1829))
    (hc : (q.map Prod.snd).Perm (cols1829++cols1829))
    (hd : ∀ k ∈ requiredD1829, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1829, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1829 cols1829 requiredD1829 requiredS1829
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1829_eq] at model
  exact MomentData.excluded1829 ds ss model
def rows1830 : List Int := [1,2,4,7,10,13,15,16,19,22,24,25,27,28,29]
def cols1830 : List Int := [1,2,4,7,10,13,15,16,19,22,24,25,27,28,29]
def requiredD1830 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1830 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1830_eq : pairedProblem rows1830 cols1830 requiredD1830 requiredS1830 =
    MomentData.problem1830 := by rfl
theorem leaf1830 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1830++rows1830))
    (hc : (q.map Prod.snd).Perm (cols1830++cols1830))
    (hd : ∀ k ∈ requiredD1830, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1830, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1830 cols1830 requiredD1830 requiredS1830
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1830_eq] at model
  exact MomentData.excluded1830 ds ss model
def rows1831 : List Int := [1,2,4,7,10,13,15,16,19,22,24,25,27,28,29]
def cols1831 : List Int := [1,2,4,7,10,13,15,16,19,22,24,25,27,28,29]
def requiredD1831 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1831 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1831_eq : pairedProblem rows1831 cols1831 requiredD1831 requiredS1831 =
    MomentData.problem1831 := by rfl
theorem leaf1831 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1831++rows1831))
    (hc : (q.map Prod.snd).Perm (cols1831++cols1831))
    (hd : ∀ k ∈ requiredD1831, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1831, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1831 cols1831 requiredD1831 requiredS1831
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1831_eq] at model
  exact MomentData.excluded1831 ds ss model
def rows1832 : List Int := [1,2,4,7,10,13,16,17,19,22,24,25,27,28,29]
def cols1832 : List Int := [1,2,4,7,10,13,16,17,19,22,24,25,27,28,29]
def requiredD1832 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1832 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1832_eq : pairedProblem rows1832 cols1832 requiredD1832 requiredS1832 =
    MomentData.problem1832 := by rfl
theorem leaf1832 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1832++rows1832))
    (hc : (q.map Prod.snd).Perm (cols1832++cols1832))
    (hd : ∀ k ∈ requiredD1832, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1832, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1832 cols1832 requiredD1832 requiredS1832
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1832_eq] at model
  exact MomentData.excluded1832 ds ss model
def rows1833 : List Int := [1,2,4,7,10,13,16,17,19,22,24,25,27,28,29]
def cols1833 : List Int := [1,2,4,7,10,13,16,17,19,22,24,25,27,28,29]
def requiredD1833 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1833 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1833_eq : pairedProblem rows1833 cols1833 requiredD1833 requiredS1833 =
    MomentData.problem1833 := by rfl
theorem leaf1833 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1833++rows1833))
    (hc : (q.map Prod.snd).Perm (cols1833++cols1833))
    (hd : ∀ k ∈ requiredD1833, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1833, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1833 cols1833 requiredD1833 requiredS1833
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1833_eq] at model
  exact MomentData.excluded1833 ds ss model
def rows1834 : List Int := [1,2,4,7,10,13,16,18,19,22,24,25,27,28,29]
def cols1834 : List Int := [1,2,4,7,10,13,16,18,19,22,24,25,27,28,29]
def requiredD1834 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1834 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1834_eq : pairedProblem rows1834 cols1834 requiredD1834 requiredS1834 =
    MomentData.problem1834 := by rfl
theorem leaf1834 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1834++rows1834))
    (hc : (q.map Prod.snd).Perm (cols1834++cols1834))
    (hd : ∀ k ∈ requiredD1834, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1834, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1834 cols1834 requiredD1834 requiredS1834
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1834_eq] at model
  exact MomentData.excluded1834 ds ss model
def rows1835 : List Int := [1,2,4,7,10,13,16,18,19,22,24,25,27,28,29]
def cols1835 : List Int := [1,2,4,7,10,13,16,18,19,22,24,25,27,28,29]
def requiredD1835 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1835 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1835_eq : pairedProblem rows1835 cols1835 requiredD1835 requiredS1835 =
    MomentData.problem1835 := by rfl
theorem leaf1835 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1835++rows1835))
    (hc : (q.map Prod.snd).Perm (cols1835++cols1835))
    (hd : ∀ k ∈ requiredD1835, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1835, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1835 cols1835 requiredD1835 requiredS1835
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1835_eq] at model
  exact MomentData.excluded1835 ds ss model
def rows1836 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,28,29]
def cols1836 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,28,29]
def requiredD1836 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1836 : List Int := [10,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1836_eq : pairedProblem rows1836 cols1836 requiredD1836 requiredS1836 =
    MomentData.problem1836 := by rfl
theorem leaf1836 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1836++rows1836))
    (hc : (q.map Prod.snd).Perm (cols1836++cols1836))
    (hd : ∀ k ∈ requiredD1836, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1836, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1836 cols1836 requiredD1836 requiredS1836
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1836_eq] at model
  exact MomentData.excluded1836 ds ss model
def rows1837 : List Int := [1,2,4,7,10,13,16,19,20,22,24,25,27,28,29]
def cols1837 : List Int := [1,2,4,7,10,13,16,19,20,22,24,25,27,28,29]
def requiredD1837 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1837 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1837_eq : pairedProblem rows1837 cols1837 requiredD1837 requiredS1837 =
    MomentData.problem1837 := by rfl
theorem leaf1837 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1837++rows1837))
    (hc : (q.map Prod.snd).Perm (cols1837++cols1837))
    (hd : ∀ k ∈ requiredD1837, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1837, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1837 cols1837 requiredD1837 requiredS1837
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1837_eq] at model
  exact MomentData.excluded1837 ds ss model
def rows1838 : List Int := [1,2,4,7,10,13,16,19,20,22,24,25,27,28,29]
def cols1838 : List Int := [1,2,4,7,10,13,16,19,20,22,24,25,27,28,29]
def requiredD1838 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1838 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1838_eq : pairedProblem rows1838 cols1838 requiredD1838 requiredS1838 =
    MomentData.problem1838 := by rfl
theorem leaf1838 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1838++rows1838))
    (hc : (q.map Prod.snd).Perm (cols1838++cols1838))
    (hd : ∀ k ∈ requiredD1838, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1838, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1838 cols1838 requiredD1838 requiredS1838
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1838_eq] at model
  exact MomentData.excluded1838 ds ss model
def rows1839 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols1839 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD1839 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1839 : List Int := [5,8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem1839_eq : pairedProblem rows1839 cols1839 requiredD1839 requiredS1839 =
    MomentData.problem1839 := by rfl
theorem leaf1839 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1839++rows1839))
    (hc : (q.map Prod.snd).Perm (cols1839++cols1839))
    (hd : ∀ k ∈ requiredD1839, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1839, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1839 cols1839 requiredD1839 requiredS1839
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1839_eq] at model
  exact MomentData.excluded1839 ds ss model
def rows1840 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols1840 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD1840 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1840 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem1840_eq : pairedProblem rows1840 cols1840 requiredD1840 requiredS1840 =
    MomentData.problem1840 := by rfl
theorem leaf1840 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1840++rows1840))
    (hc : (q.map Prod.snd).Perm (cols1840++cols1840))
    (hd : ∀ k ∈ requiredD1840, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1840, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1840 cols1840 requiredD1840 requiredS1840
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1840_eq] at model
  exact MomentData.excluded1840 ds ss model
def rows1841 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols1841 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD1841 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1841 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem1841_eq : pairedProblem rows1841 cols1841 requiredD1841 requiredS1841 =
    MomentData.problem1841 := by rfl
theorem leaf1841 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1841++rows1841))
    (hc : (q.map Prod.snd).Perm (cols1841++cols1841))
    (hd : ∀ k ∈ requiredD1841, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1841, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1841 cols1841 requiredD1841 requiredS1841
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1841_eq] at model
  exact MomentData.excluded1841 ds ss model
def rows1842 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols1842 : List Int := [1,2,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD1842 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1842 : List Int := [5,8,11,14,17,20,23,26,29,31,32,35,38,41]
theorem problem1842_eq : pairedProblem rows1842 cols1842 requiredD1842 requiredS1842 =
    MomentData.problem1842 := by rfl
theorem leaf1842 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1842++rows1842))
    (hc : (q.map Prod.snd).Perm (cols1842++cols1842))
    (hd : ∀ k ∈ requiredD1842, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1842, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1842 cols1842 requiredD1842 requiredS1842
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1842_eq] at model
  exact MomentData.excluded1842 ds ss model
def rows1843 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1843 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1843 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1843 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1843_eq : pairedProblem rows1843 cols1843 requiredD1843 requiredS1843 =
    MomentData.problem1843 := by rfl
theorem leaf1843 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1843++rows1843))
    (hc : (q.map Prod.snd).Perm (cols1843++cols1843))
    (hd : ∀ k ∈ requiredD1843, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1843, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1843 cols1843 requiredD1843 requiredS1843
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1843_eq] at model
  exact MomentData.excluded1843 ds ss model
def rows1844 : List Int := [8,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1844 : List Int := [8,9,10,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1844 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1844 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1844_eq : pairedProblem rows1844 cols1844 requiredD1844 requiredS1844 =
    MomentData.problem1844 := by rfl
theorem leaf1844 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1844++rows1844))
    (hc : (q.map Prod.snd).Perm (cols1844++cols1844))
    (hd : ∀ k ∈ requiredD1844, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1844, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1844 cols1844 requiredD1844 requiredS1844
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1844_eq] at model
  exact MomentData.excluded1844 ds ss model
def rows1845 : List Int := [1,2,4,7,10,13,16,19,22,23,24,25,27,28,29]
def cols1845 : List Int := [1,2,4,7,10,13,16,19,22,23,24,25,27,28,29]
def requiredD1845 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1845 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1845_eq : pairedProblem rows1845 cols1845 requiredD1845 requiredS1845 =
    MomentData.problem1845 := by rfl
theorem leaf1845 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1845++rows1845))
    (hc : (q.map Prod.snd).Perm (cols1845++cols1845))
    (hd : ∀ k ∈ requiredD1845, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1845, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1845 cols1845 requiredD1845 requiredS1845
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1845_eq] at model
  exact MomentData.excluded1845 ds ss model
def rows1846 : List Int := [1,2,4,7,10,13,16,19,22,23,24,25,27,28,29]
def cols1846 : List Int := [1,2,4,7,10,13,16,19,22,23,24,25,27,28,29]
def requiredD1846 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1846 : List Int := [8,11,14,17,20,21,23,26,29,31,32,35,38,41,44]
theorem problem1846_eq : pairedProblem rows1846 cols1846 requiredD1846 requiredS1846 =
    MomentData.problem1846 := by rfl
theorem leaf1846 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1846++rows1846))
    (hc : (q.map Prod.snd).Perm (cols1846++cols1846))
    (hd : ∀ k ∈ requiredD1846, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1846, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1846 cols1846 requiredD1846 requiredS1846
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1846_eq] at model
  exact MomentData.excluded1846 ds ss model
def rows1847 : List Int := [8,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1847 : List Int := [8,9,10,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1847 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1847 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1847_eq : pairedProblem rows1847 cols1847 requiredD1847 requiredS1847 =
    MomentData.problem1847 := by rfl
theorem leaf1847 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1847++rows1847))
    (hc : (q.map Prod.snd).Perm (cols1847++cols1847))
    (hd : ∀ k ∈ requiredD1847, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1847, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1847 cols1847 requiredD1847 requiredS1847
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1847_eq] at model
  exact MomentData.excluded1847 ds ss model
def rows1848 : List Int := [8,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1848 : List Int := [8,9,10,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1848 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1848 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1848_eq : pairedProblem rows1848 cols1848 requiredD1848 requiredS1848 =
    MomentData.problem1848 := by rfl
theorem leaf1848 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1848++rows1848))
    (hc : (q.map Prod.snd).Perm (cols1848++cols1848))
    (hd : ∀ k ∈ requiredD1848, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1848, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1848 cols1848 requiredD1848 requiredS1848
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1848_eq] at model
  exact MomentData.excluded1848 ds ss model
def rows1849 : List Int := [8,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1849 : List Int := [8,9,10,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1849 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1849 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1849_eq : pairedProblem rows1849 cols1849 requiredD1849 requiredS1849 =
    MomentData.problem1849 := by rfl
theorem leaf1849 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1849++rows1849))
    (hc : (q.map Prod.snd).Perm (cols1849++cols1849))
    (hd : ∀ k ∈ requiredD1849, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1849, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1849 cols1849 requiredD1849 requiredS1849
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1849_eq] at model
  exact MomentData.excluded1849 ds ss model
def rows1850 : List Int := [8,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1850 : List Int := [8,9,10,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1850 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1850 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1850_eq : pairedProblem rows1850 cols1850 requiredD1850 requiredS1850 =
    MomentData.problem1850 := by rfl
theorem leaf1850 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1850++rows1850))
    (hc : (q.map Prod.snd).Perm (cols1850++cols1850))
    (hd : ∀ k ∈ requiredD1850, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1850, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1850 cols1850 requiredD1850 requiredS1850
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1850_eq] at model
  exact MomentData.excluded1850 ds ss model
def rows1851 : List Int := [8,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1851 : List Int := [8,9,10,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1851 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1851 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1851_eq : pairedProblem rows1851 cols1851 requiredD1851 requiredS1851 =
    MomentData.problem1851 := by rfl
theorem leaf1851 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1851++rows1851))
    (hc : (q.map Prod.snd).Perm (cols1851++cols1851))
    (hd : ∀ k ∈ requiredD1851, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1851, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1851 cols1851 requiredD1851 requiredS1851
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1851_eq] at model
  exact MomentData.excluded1851 ds ss model
def rows1852 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols1852 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD1852 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS1852 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1852_eq : pairedProblem rows1852 cols1852 requiredD1852 requiredS1852 =
    MomentData.problem1852 := by rfl
theorem leaf1852 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1852++rows1852))
    (hc : (q.map Prod.snd).Perm (cols1852++cols1852))
    (hd : ∀ k ∈ requiredD1852, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1852, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1852 cols1852 requiredD1852 requiredS1852
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1852_eq] at model
  exact MomentData.excluded1852 ds ss model
def rows1853 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols1853 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD1853 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1853 : List Int := [17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1853_eq : pairedProblem rows1853 cols1853 requiredD1853 requiredS1853 =
    MomentData.problem1853 := by rfl
theorem leaf1853 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1853++rows1853))
    (hc : (q.map Prod.snd).Perm (cols1853++cols1853))
    (hd : ∀ k ∈ requiredD1853, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1853, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1853 cols1853 requiredD1853 requiredS1853
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1853_eq] at model
  exact MomentData.excluded1853 ds ss model
def rows1854 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def cols1854 : List Int := [0,2,4,6,8,10,12,15,17,19,21,23,25,27,29]
def requiredD1854 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS1854 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,42]
theorem problem1854_eq : pairedProblem rows1854 cols1854 requiredD1854 requiredS1854 =
    MomentData.problem1854 := by rfl
theorem leaf1854 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1854++rows1854))
    (hc : (q.map Prod.snd).Perm (cols1854++cols1854))
    (hd : ∀ k ∈ requiredD1854, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1854, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1854 cols1854 requiredD1854 requiredS1854
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1854_eq] at model
  exact MomentData.excluded1854 ds ss model
def rows1855 : List Int := [0,2,4,6,8,10,12,16,17,19,21,23,25,27,29]
def cols1855 : List Int := [0,2,4,6,8,10,12,16,17,19,21,23,25,27,29]
def requiredD1855 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1855 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1855_eq : pairedProblem rows1855 cols1855 requiredD1855 requiredS1855 =
    MomentData.problem1855 := by rfl
theorem leaf1855 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1855++rows1855))
    (hc : (q.map Prod.snd).Perm (cols1855++cols1855))
    (hd : ∀ k ∈ requiredD1855, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1855, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1855 cols1855 requiredD1855 requiredS1855
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1855_eq] at model
  exact MomentData.excluded1855 ds ss model
def rows1856 : List Int := [0,2,4,6,8,10,13,15,17,19,21,23,25,27,29]
def cols1856 : List Int := [0,2,4,6,8,10,13,15,17,19,21,23,25,27,29]
def requiredD1856 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS1856 : List Int := [13,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1856_eq : pairedProblem rows1856 cols1856 requiredD1856 requiredS1856 =
    MomentData.problem1856 := by rfl
theorem leaf1856 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1856++rows1856))
    (hc : (q.map Prod.snd).Perm (cols1856++cols1856))
    (hd : ∀ k ∈ requiredD1856, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1856, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1856 cols1856 requiredD1856 requiredS1856
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1856_eq] at model
  exact MomentData.excluded1856 ds ss model
def rows1857 : List Int := [1,3,4,5,7,9,11,16,18,20,22,24,26,28,29]
def cols1857 : List Int := [1,3,4,5,7,9,11,16,18,20,22,24,26,28,29]
def requiredD1857 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1857 : List Int := [14,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1857_eq : pairedProblem rows1857 cols1857 requiredD1857 requiredS1857 =
    MomentData.problem1857 := by rfl
theorem leaf1857 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1857++rows1857))
    (hc : (q.map Prod.snd).Perm (cols1857++cols1857))
    (hd : ∀ k ∈ requiredD1857, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1857, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1857 cols1857 requiredD1857 requiredS1857
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1857_eq] at model
  exact MomentData.excluded1857 ds ss model
def rows1858 : List Int := [0,2,4,6,8,10,12,17,18,19,21,23,25,27,29]
def cols1858 : List Int := [0,2,4,6,8,10,12,17,18,19,21,23,25,27,29]
def requiredD1858 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1858 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1858_eq : pairedProblem rows1858 cols1858 requiredD1858 requiredS1858 =
    MomentData.problem1858 := by rfl
theorem leaf1858 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1858++rows1858))
    (hc : (q.map Prod.snd).Perm (cols1858++cols1858))
    (hd : ∀ k ∈ requiredD1858, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1858, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1858 cols1858 requiredD1858 requiredS1858
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1858_eq] at model
  exact MomentData.excluded1858 ds ss model
def rows1859 : List Int := [0,2,4,6,8,10,12,17,19,20,21,23,25,27,29]
def cols1859 : List Int := [0,2,4,6,8,10,12,17,19,20,21,23,25,27,29]
def requiredD1859 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1859 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1859_eq : pairedProblem rows1859 cols1859 requiredD1859 requiredS1859 =
    MomentData.problem1859 := by rfl
theorem leaf1859 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1859++rows1859))
    (hc : (q.map Prod.snd).Perm (cols1859++cols1859))
    (hd : ∀ k ∈ requiredD1859, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1859, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1859 cols1859 requiredD1859 requiredS1859
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1859_eq] at model
  exact MomentData.excluded1859 ds ss model
def rows1860 : List Int := [0,2,4,6,8,10,12,17,19,21,22,23,25,27,29]
def cols1860 : List Int := [0,2,4,6,8,10,12,17,19,21,22,23,25,27,29]
def requiredD1860 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1860 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1860_eq : pairedProblem rows1860 cols1860 requiredD1860 requiredS1860 =
    MomentData.problem1860 := by rfl
theorem leaf1860 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1860++rows1860))
    (hc : (q.map Prod.snd).Perm (cols1860++cols1860))
    (hd : ∀ k ∈ requiredD1860, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1860, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1860 cols1860 requiredD1860 requiredS1860
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1860_eq] at model
  exact MomentData.excluded1860 ds ss model
def rows1861 : List Int := [0,2,4,6,8,10,12,17,19,21,22,23,25,27,29]
def cols1861 : List Int := [1,3,5,6,7,9,11,16,18,20,22,24,26,28,29]
def requiredD1861 : List Int := [-12,-11,-9,-7,-5,-3,-1,1,3,5,7,9,11,13,14]
def requiredS1861 : List Int := [15,16,18,20,22,24,26,28,30,32,34,36,38,40,41]
theorem problem1861_eq : pairedProblem rows1861 cols1861 requiredD1861 requiredS1861 =
    MomentData.problem1861 := by rfl
theorem leaf1861 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1861++rows1861))
    (hc : (q.map Prod.snd).Perm (cols1861++cols1861))
    (hd : ∀ k ∈ requiredD1861, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1861, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1861 cols1861 requiredD1861 requiredS1861
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1861_eq] at model
  exact MomentData.excluded1861 ds ss model
def rows1862 : List Int := [1,3,5,6,7,9,11,16,18,20,22,24,26,28,29]
def cols1862 : List Int := [1,3,5,6,7,9,11,16,18,20,22,24,26,28,29]
def requiredD1862 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1862 : List Int := [14,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1862_eq : pairedProblem rows1862 cols1862 requiredD1862 requiredS1862 =
    MomentData.problem1862 := by rfl
theorem leaf1862 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1862++rows1862))
    (hc : (q.map Prod.snd).Perm (cols1862++cols1862))
    (hd : ∀ k ∈ requiredD1862, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1862, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1862 cols1862 requiredD1862 requiredS1862
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1862_eq] at model
  exact MomentData.excluded1862 ds ss model
def rows1863 : List Int := [0,2,4,6,8,10,12,17,19,21,23,24,25,27,29]
def cols1863 : List Int := [0,2,4,6,8,10,12,17,19,21,23,24,25,27,29]
def requiredD1863 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1863 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1863_eq : pairedProblem rows1863 cols1863 requiredD1863 requiredS1863 =
    MomentData.problem1863 := by rfl
theorem leaf1863 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1863++rows1863))
    (hc : (q.map Prod.snd).Perm (cols1863++cols1863))
    (hd : ∀ k ∈ requiredD1863, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1863, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1863 cols1863 requiredD1863 requiredS1863
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1863_eq] at model
  exact MomentData.excluded1863 ds ss model
def rows1864 : List Int := [1,3,5,7,8,9,11,16,18,20,22,24,26,28,29]
def cols1864 : List Int := [1,3,5,7,8,9,11,16,18,20,22,24,26,28,29]
def requiredD1864 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1864 : List Int := [14,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1864_eq : pairedProblem rows1864 cols1864 requiredD1864 requiredS1864 =
    MomentData.problem1864 := by rfl
theorem leaf1864 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1864++rows1864))
    (hc : (q.map Prod.snd).Perm (cols1864++cols1864))
    (hd : ∀ k ∈ requiredD1864, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1864, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1864 cols1864 requiredD1864 requiredS1864
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1864_eq] at model
  exact MomentData.excluded1864 ds ss model
def rows1865 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,26,27,29]
def cols1865 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,26,27,29]
def requiredD1865 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1865 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41,42]
theorem problem1865_eq : pairedProblem rows1865 cols1865 requiredD1865 requiredS1865 =
    MomentData.problem1865 := by rfl
theorem leaf1865 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1865++rows1865))
    (hc : (q.map Prod.snd).Perm (cols1865++cols1865))
    (hd : ∀ k ∈ requiredD1865, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1865, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1865 cols1865 requiredD1865 requiredS1865
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1865_eq] at model
  exact MomentData.excluded1865 ds ss model
def rows1866 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1866 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1866 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1866 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1866_eq : pairedProblem rows1866 cols1866 requiredD1866 requiredS1866 =
    MomentData.problem1866 := by rfl
theorem leaf1866 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1866++rows1866))
    (hc : (q.map Prod.snd).Perm (cols1866++cols1866))
    (hd : ∀ k ∈ requiredD1866, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1866, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1866 cols1866 requiredD1866 requiredS1866
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1866_eq] at model
  exact MomentData.excluded1866 ds ss model
def rows1867 : List Int := [1,3,5,7,9,10,11,16,18,20,22,24,26,28,29]
def cols1867 : List Int := [1,3,5,7,9,10,11,16,18,20,22,24,26,28,29]
def requiredD1867 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1867 : List Int := [14,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1867_eq : pairedProblem rows1867 cols1867 requiredD1867 requiredS1867 =
    MomentData.problem1867 := by rfl
theorem leaf1867 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1867++rows1867))
    (hc : (q.map Prod.snd).Perm (cols1867++cols1867))
    (hd : ∀ k ∈ requiredD1867, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1867, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1867 cols1867 requiredD1867 requiredS1867
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1867_eq] at model
  exact MomentData.excluded1867 ds ss model
def rows1868 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1868 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1868 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1868 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1868_eq : pairedProblem rows1868 cols1868 requiredD1868 requiredS1868 =
    MomentData.problem1868 := by rfl
theorem leaf1868 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1868++rows1868))
    (hc : (q.map Prod.snd).Perm (cols1868++cols1868))
    (hd : ∀ k ∈ requiredD1868, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1868, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1868 cols1868 requiredD1868 requiredS1868
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1868_eq] at model
  exact MomentData.excluded1868 ds ss model
def rows1869 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1869 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1869 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1869 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1869_eq : pairedProblem rows1869 cols1869 requiredD1869 requiredS1869 =
    MomentData.problem1869 := by rfl
theorem leaf1869 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1869++rows1869))
    (hc : (q.map Prod.snd).Perm (cols1869++cols1869))
    (hd : ∀ k ∈ requiredD1869, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1869, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1869 cols1869 requiredD1869 requiredS1869
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1869_eq] at model
  exact MomentData.excluded1869 ds ss model
def rows1870 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def cols1870 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,28,29]
def requiredD1870 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1870 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,46]
theorem problem1870_eq : pairedProblem rows1870 cols1870 requiredD1870 requiredS1870 =
    MomentData.problem1870 := by rfl
theorem leaf1870 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1870++rows1870))
    (hc : (q.map Prod.snd).Perm (cols1870++cols1870))
    (hd : ∀ k ∈ requiredD1870, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1870, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1870 cols1870 requiredD1870 requiredS1870
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1870_eq] at model
  exact MomentData.excluded1870 ds ss model
def rows1871 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1871 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1871 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1871 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1871_eq : pairedProblem rows1871 cols1871 requiredD1871 requiredS1871 =
    MomentData.problem1871 := by rfl
theorem leaf1871 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1871++rows1871))
    (hc : (q.map Prod.snd).Perm (cols1871++cols1871))
    (hd : ∀ k ∈ requiredD1871, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1871, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1871 cols1871 requiredD1871 requiredS1871
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1871_eq] at model
  exact MomentData.excluded1871 ds ss model
def rows1872 : List Int := [1,3,5,7,9,11,12,16,18,20,22,24,26,28,29]
def cols1872 : List Int := [1,3,5,7,9,11,12,16,18,20,22,24,26,28,29]
def requiredD1872 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1872 : List Int := [14,15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1872_eq : pairedProblem rows1872 cols1872 requiredD1872 requiredS1872 =
    MomentData.problem1872 := by rfl
theorem leaf1872 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1872++rows1872))
    (hc : (q.map Prod.snd).Perm (cols1872++cols1872))
    (hd : ∀ k ∈ requiredD1872, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1872, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1872 cols1872 requiredD1872 requiredS1872
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1872_eq] at model
  exact MomentData.excluded1872 ds ss model
def rows1873 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1873 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1873 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1873 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1873_eq : pairedProblem rows1873 cols1873 requiredD1873 requiredS1873 =
    MomentData.problem1873 := by rfl
theorem leaf1873 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1873++rows1873))
    (hc : (q.map Prod.snd).Perm (cols1873++cols1873))
    (hd : ∀ k ∈ requiredD1873, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1873, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1873 cols1873 requiredD1873 requiredS1873
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1873_eq] at model
  exact MomentData.excluded1873 ds ss model
def rows1874 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols1874 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD1874 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1874 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1874_eq : pairedProblem rows1874 cols1874 requiredD1874 requiredS1874 =
    MomentData.problem1874 := by rfl
theorem leaf1874 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1874++rows1874))
    (hc : (q.map Prod.snd).Perm (cols1874++cols1874))
    (hd : ∀ k ∈ requiredD1874, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1874, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1874 cols1874 requiredD1874 requiredS1874
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1874_eq] at model
  exact MomentData.excluded1874 ds ss model
def rows1875 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols1875 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD1875 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1875 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1875_eq : pairedProblem rows1875 cols1875 requiredD1875 requiredS1875 =
    MomentData.problem1875 := by rfl
theorem leaf1875 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1875++rows1875))
    (hc : (q.map Prod.snd).Perm (cols1875++cols1875))
    (hd : ∀ k ∈ requiredD1875, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1875, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1875 cols1875 requiredD1875 requiredS1875
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1875_eq] at model
  exact MomentData.excluded1875 ds ss model
def rows1876 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols1876 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD1876 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1876 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1876_eq : pairedProblem rows1876 cols1876 requiredD1876 requiredS1876 =
    MomentData.problem1876 := by rfl
theorem leaf1876 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1876++rows1876))
    (hc : (q.map Prod.snd).Perm (cols1876++cols1876))
    (hd : ∀ k ∈ requiredD1876, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1876, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1876 cols1876 requiredD1876 requiredS1876
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1876_eq] at model
  exact MomentData.excluded1876 ds ss model
def rows1877 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def cols1877 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def requiredD1877 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1877 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1877_eq : pairedProblem rows1877 cols1877 requiredD1877 requiredS1877 =
    MomentData.problem1877 := by rfl
theorem leaf1877 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1877++rows1877))
    (hc : (q.map Prod.snd).Perm (cols1877++cols1877))
    (hd : ∀ k ∈ requiredD1877, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1877, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1877 cols1877 requiredD1877 requiredS1877
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1877_eq] at model
  exact MomentData.excluded1877 ds ss model
def rows1878 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def cols1878 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def requiredD1878 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1878 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1878_eq : pairedProblem rows1878 cols1878 requiredD1878 requiredS1878 =
    MomentData.problem1878 := by rfl
theorem leaf1878 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1878++rows1878))
    (hc : (q.map Prod.snd).Perm (cols1878++cols1878))
    (hd : ∀ k ∈ requiredD1878, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1878, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1878 cols1878 requiredD1878 requiredS1878
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1878_eq] at model
  exact MomentData.excluded1878 ds ss model
def rows1879 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def cols1879 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1879 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1879 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1879_eq : pairedProblem rows1879 cols1879 requiredD1879 requiredS1879 =
    MomentData.problem1879 := by rfl
theorem leaf1879 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1879++rows1879))
    (hc : (q.map Prod.snd).Perm (cols1879++cols1879))
    (hd : ∀ k ∈ requiredD1879, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1879, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1879 cols1879 requiredD1879 requiredS1879
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1879_eq] at model
  exact MomentData.excluded1879 ds ss model
def rows1880 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1880 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1880 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1880 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1880_eq : pairedProblem rows1880 cols1880 requiredD1880 requiredS1880 =
    MomentData.problem1880 := by rfl
theorem leaf1880 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1880++rows1880))
    (hc : (q.map Prod.snd).Perm (cols1880++cols1880))
    (hd : ∀ k ∈ requiredD1880, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1880, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1880 cols1880 requiredD1880 requiredS1880
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1880_eq] at model
  exact MomentData.excluded1880 ds ss model
def rows1881 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,28,29]
def cols1881 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,28,29]
def requiredD1881 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS1881 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem1881_eq : pairedProblem rows1881 cols1881 requiredD1881 requiredS1881 =
    MomentData.problem1881 := by rfl
theorem leaf1881 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1881++rows1881))
    (hc : (q.map Prod.snd).Perm (cols1881++cols1881))
    (hd : ∀ k ∈ requiredD1881, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1881, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1881 cols1881 requiredD1881 requiredS1881
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1881_eq] at model
  exact MomentData.excluded1881 ds ss model
def rows1882 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def cols1882 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def requiredD1882 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1882 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1882_eq : pairedProblem rows1882 cols1882 requiredD1882 requiredS1882 =
    MomentData.problem1882 := by rfl
theorem leaf1882 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1882++rows1882))
    (hc : (q.map Prod.snd).Perm (cols1882++cols1882))
    (hd : ∀ k ∈ requiredD1882, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1882, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1882 cols1882 requiredD1882 requiredS1882
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1882_eq] at model
  exact MomentData.excluded1882 ds ss model
def rows1883 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def cols1883 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def requiredD1883 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1883 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1883_eq : pairedProblem rows1883 cols1883 requiredD1883 requiredS1883 =
    MomentData.problem1883 := by rfl
theorem leaf1883 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1883++rows1883))
    (hc : (q.map Prod.snd).Perm (cols1883++cols1883))
    (hd : ∀ k ∈ requiredD1883, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1883, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1883 cols1883 requiredD1883 requiredS1883
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1883_eq] at model
  exact MomentData.excluded1883 ds ss model
def rows1884 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1884 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1884 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1884 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem1884_eq : pairedProblem rows1884 cols1884 requiredD1884 requiredS1884 =
    MomentData.problem1884 := by rfl
theorem leaf1884 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1884++rows1884))
    (hc : (q.map Prod.snd).Perm (cols1884++cols1884))
    (hd : ∀ k ∈ requiredD1884, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1884, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1884 cols1884 requiredD1884 requiredS1884
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1884_eq] at model
  exact MomentData.excluded1884 ds ss model
def rows1885 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1885 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1885 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1885 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,47]
theorem problem1885_eq : pairedProblem rows1885 cols1885 requiredD1885 requiredS1885 =
    MomentData.problem1885 := by rfl
theorem leaf1885 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1885++rows1885))
    (hc : (q.map Prod.snd).Perm (cols1885++cols1885))
    (hd : ∀ k ∈ requiredD1885, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1885, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1885 cols1885 requiredD1885 requiredS1885
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1885_eq] at model
  exact MomentData.excluded1885 ds ss model
def rows1886 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1886 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1886 : List Int := [-21,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,21]
def requiredS1886 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,47]
theorem problem1886_eq : pairedProblem rows1886 cols1886 requiredD1886 requiredS1886 =
    MomentData.problem1886 := by rfl
theorem leaf1886 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1886++rows1886))
    (hc : (q.map Prod.snd).Perm (cols1886++cols1886))
    (hd : ∀ k ∈ requiredD1886, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1886, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1886 cols1886 requiredD1886 requiredS1886
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1886_eq] at model
  exact MomentData.excluded1886 ds ss model
def rows1887 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def cols1887 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,28,29]
def requiredD1887 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1887 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1887_eq : pairedProblem rows1887 cols1887 requiredD1887 requiredS1887 =
    MomentData.problem1887 := by rfl
theorem leaf1887 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1887++rows1887))
    (hc : (q.map Prod.snd).Perm (cols1887++cols1887))
    (hd : ∀ k ∈ requiredD1887, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1887, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1887 cols1887 requiredD1887 requiredS1887
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1887_eq] at model
  exact MomentData.excluded1887 ds ss model
def rows1888 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols1888 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def requiredD1888 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1888 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1888_eq : pairedProblem rows1888 cols1888 requiredD1888 requiredS1888 =
    MomentData.problem1888 := by rfl
theorem leaf1888 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1888++rows1888))
    (hc : (q.map Prod.snd).Perm (cols1888++cols1888))
    (hd : ∀ k ∈ requiredD1888, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1888, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1888 cols1888 requiredD1888 requiredS1888
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1888_eq] at model
  exact MomentData.excluded1888 ds ss model
def rows1889 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols1889 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def requiredD1889 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1889 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1889_eq : pairedProblem rows1889 cols1889 requiredD1889 requiredS1889 =
    MomentData.problem1889 := by rfl
theorem leaf1889 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1889++rows1889))
    (hc : (q.map Prod.snd).Perm (cols1889++cols1889))
    (hd : ∀ k ∈ requiredD1889, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1889, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1889 cols1889 requiredD1889 requiredS1889
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1889_eq] at model
  exact MomentData.excluded1889 ds ss model
def rows1890 : List Int := [1,3,5,7,9,11,14,16,18,20,22,24,26,28,29]
def cols1890 : List Int := [1,3,5,7,9,11,14,16,18,20,22,24,26,28,29]
def requiredD1890 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1890 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,40]
theorem problem1890_eq : pairedProblem rows1890 cols1890 requiredD1890 requiredS1890 =
    MomentData.problem1890 := by rfl
theorem leaf1890 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1890++rows1890))
    (hc : (q.map Prod.snd).Perm (cols1890++cols1890))
    (hd : ∀ k ∈ requiredD1890, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1890, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1890 cols1890 requiredD1890 requiredS1890
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1890_eq] at model
  exact MomentData.excluded1890 ds ss model
def rows1891 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def cols1891 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def requiredD1891 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1891 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1891_eq : pairedProblem rows1891 cols1891 requiredD1891 requiredS1891 =
    MomentData.problem1891 := by rfl
theorem leaf1891 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1891++rows1891))
    (hc : (q.map Prod.snd).Perm (cols1891++cols1891))
    (hd : ∀ k ∈ requiredD1891, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1891, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1891 cols1891 requiredD1891 requiredS1891
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1891_eq] at model
  exact MomentData.excluded1891 ds ss model
def rows1892 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def cols1892 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def requiredD1892 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1892 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1892_eq : pairedProblem rows1892 cols1892 requiredD1892 requiredS1892 =
    MomentData.problem1892 := by rfl
theorem leaf1892 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1892++rows1892))
    (hc : (q.map Prod.snd).Perm (cols1892++cols1892))
    (hd : ∀ k ∈ requiredD1892, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1892, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1892 cols1892 requiredD1892 requiredS1892
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1892_eq] at model
  exact MomentData.excluded1892 ds ss model
def rows1893 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def cols1893 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def requiredD1893 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1893 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1893_eq : pairedProblem rows1893 cols1893 requiredD1893 requiredS1893 =
    MomentData.problem1893 := by rfl
theorem leaf1893 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1893++rows1893))
    (hc : (q.map Prod.snd).Perm (cols1893++cols1893))
    (hd : ∀ k ∈ requiredD1893, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1893, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1893 cols1893 requiredD1893 requiredS1893
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1893_eq] at model
  exact MomentData.excluded1893 ds ss model
def rows1894 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def cols1894 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def requiredD1894 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1894 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1894_eq : pairedProblem rows1894 cols1894 requiredD1894 requiredS1894 =
    MomentData.problem1894 := by rfl
theorem leaf1894 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1894++rows1894))
    (hc : (q.map Prod.snd).Perm (cols1894++cols1894))
    (hd : ∀ k ∈ requiredD1894, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1894, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1894 cols1894 requiredD1894 requiredS1894
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1894_eq] at model
  exact MomentData.excluded1894 ds ss model
def rows1895 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def cols1895 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def requiredD1895 : List Int := [-20,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,20]
def requiredS1895 : List Int := [9,23,24,25,26,27,28,29,30,31,32,33,34,35,49]
theorem problem1895_eq : pairedProblem rows1895 cols1895 requiredD1895 requiredS1895 =
    MomentData.problem1895 := by rfl
theorem leaf1895 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1895++rows1895))
    (hc : (q.map Prod.snd).Perm (cols1895++cols1895))
    (hd : ∀ k ∈ requiredD1895, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1895, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1895 cols1895 requiredD1895 requiredS1895
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1895_eq] at model
  exact MomentData.excluded1895 ds ss model
def rows1896 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def cols1896 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def requiredD1896 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1896 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1896_eq : pairedProblem rows1896 cols1896 requiredD1896 requiredS1896 =
    MomentData.problem1896 := by rfl
theorem leaf1896 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1896++rows1896))
    (hc : (q.map Prod.snd).Perm (cols1896++cols1896))
    (hd : ∀ k ∈ requiredD1896, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1896, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1896 cols1896 requiredD1896 requiredS1896
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1896_eq] at model
  exact MomentData.excluded1896 ds ss model
def rows1897 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,29]
def cols1897 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,29]
def requiredD1897 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1897 : List Int := [10,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem1897_eq : pairedProblem rows1897 cols1897 requiredD1897 requiredS1897 =
    MomentData.problem1897 := by rfl
theorem leaf1897 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1897++rows1897))
    (hc : (q.map Prod.snd).Perm (cols1897++cols1897))
    (hd : ∀ k ∈ requiredD1897, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1897, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1897 cols1897 requiredD1897 requiredS1897
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1897_eq] at model
  exact MomentData.excluded1897 ds ss model
def rows1898 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1898 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1898 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1898 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1898_eq : pairedProblem rows1898 cols1898 requiredD1898 requiredS1898 =
    MomentData.problem1898 := by rfl
theorem leaf1898 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1898++rows1898))
    (hc : (q.map Prod.snd).Perm (cols1898++cols1898))
    (hd : ∀ k ∈ requiredD1898, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1898, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1898 cols1898 requiredD1898 requiredS1898
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1898_eq] at model
  exact MomentData.excluded1898 ds ss model
def rows1899 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def cols1899 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,21,28,29]
def requiredD1899 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1899 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1899_eq : pairedProblem rows1899 cols1899 requiredD1899 requiredS1899 =
    MomentData.problem1899 := by rfl
theorem leaf1899 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1899++rows1899))
    (hc : (q.map Prod.snd).Perm (cols1899++cols1899))
    (hd : ∀ k ∈ requiredD1899, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1899, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1899 cols1899 requiredD1899 requiredS1899
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1899_eq] at model
  exact MomentData.excluded1899 ds ss model
def rows1900 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1900 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,22,28,29]
def requiredD1900 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1900 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1900_eq : pairedProblem rows1900 cols1900 requiredD1900 requiredS1900 =
    MomentData.problem1900 := by rfl
theorem leaf1900 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1900++rows1900))
    (hc : (q.map Prod.snd).Perm (cols1900++cols1900))
    (hd : ∀ k ∈ requiredD1900, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1900, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1900 cols1900 requiredD1900 requiredS1900
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1900_eq] at model
  exact MomentData.excluded1900 ds ss model
def rows1901 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols1901 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,23,28,29]
def requiredD1901 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1901 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1901_eq : pairedProblem rows1901 cols1901 requiredD1901 requiredS1901 =
    MomentData.problem1901 := by rfl
theorem leaf1901 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1901++rows1901))
    (hc : (q.map Prod.snd).Perm (cols1901++cols1901))
    (hd : ∀ k ∈ requiredD1901, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1901, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1901 cols1901 requiredD1901 requiredS1901
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1901_eq] at model
  exact MomentData.excluded1901 ds ss model
def rows1902 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols1902 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,24,28,29]
def requiredD1902 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1902 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1902_eq : pairedProblem rows1902 cols1902 requiredD1902 requiredS1902 =
    MomentData.problem1902 := by rfl
theorem leaf1902 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1902++rows1902))
    (hc : (q.map Prod.snd).Perm (cols1902++cols1902))
    (hd : ∀ k ∈ requiredD1902, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1902, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1902 cols1902 requiredD1902 requiredS1902
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1902_eq] at model
  exact MomentData.excluded1902 ds ss model
def rows1903 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1903 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,25,28,29]
def requiredD1903 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1903 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1903_eq : pairedProblem rows1903 cols1903 requiredD1903 requiredS1903 =
    MomentData.problem1903 := by rfl
theorem leaf1903 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1903++rows1903))
    (hc : (q.map Prod.snd).Perm (cols1903++cols1903))
    (hd : ∀ k ∈ requiredD1903, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1903, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1903 cols1903 requiredD1903 requiredS1903
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1903_eq] at model
  exact MomentData.excluded1903 ds ss model
def rows1904 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def cols1904 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,26,28,29]
def requiredD1904 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1904 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1904_eq : pairedProblem rows1904 cols1904 requiredD1904 requiredS1904 =
    MomentData.problem1904 := by rfl
theorem leaf1904 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1904++rows1904))
    (hc : (q.map Prod.snd).Perm (cols1904++cols1904))
    (hd : ∀ k ∈ requiredD1904, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1904, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1904 cols1904 requiredD1904 requiredS1904
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1904_eq] at model
  exact MomentData.excluded1904 ds ss model
def rows1905 : List Int := [1,2,3,4,5,8,11,14,17,20,23,24,26,27,29]
def cols1905 : List Int := [1,2,3,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD1905 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1905 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1905_eq : pairedProblem rows1905 cols1905 requiredD1905 requiredS1905 =
    MomentData.problem1905 := by rfl
theorem leaf1905 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1905++rows1905))
    (hc : (q.map Prod.snd).Perm (cols1905++cols1905))
    (hd : ∀ k ∈ requiredD1905, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1905, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1905 cols1905 requiredD1905 requiredS1905
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1905_eq] at model
  exact MomentData.excluded1905 ds ss model
def rows1906 : List Int := [1,2,3,4,5,8,11,14,17,20,23,24,26,27,29]
def cols1906 : List Int := [1,2,3,4,5,8,11,14,17,20,23,24,26,27,29]
def requiredD1906 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1906 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1906_eq : pairedProblem rows1906 cols1906 requiredD1906 requiredS1906 =
    MomentData.problem1906 := by rfl
theorem leaf1906 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1906++rows1906))
    (hc : (q.map Prod.snd).Perm (cols1906++cols1906))
    (hd : ∀ k ∈ requiredD1906, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1906, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1906 cols1906 requiredD1906 requiredS1906
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1906_eq] at model
  exact MomentData.excluded1906 ds ss model
def rows1907 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def cols1907 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def requiredD1907 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1907 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1907_eq : pairedProblem rows1907 cols1907 requiredD1907 requiredS1907 =
    MomentData.problem1907 := by rfl
theorem leaf1907 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1907++rows1907))
    (hc : (q.map Prod.snd).Perm (cols1907++cols1907))
    (hd : ∀ k ∈ requiredD1907, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1907, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1907 cols1907 requiredD1907 requiredS1907
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1907_eq] at model
  exact MomentData.excluded1907 ds ss model
def rows1908 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def cols1908 : List Int := [1,2,4,5,6,8,11,14,17,20,23,24,26,27,29]
def requiredD1908 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1908 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1908_eq : pairedProblem rows1908 cols1908 requiredD1908 requiredS1908 =
    MomentData.problem1908 := by rfl
theorem leaf1908 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1908++rows1908))
    (hc : (q.map Prod.snd).Perm (cols1908++cols1908))
    (hd : ∀ k ∈ requiredD1908, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1908, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1908 cols1908 requiredD1908 requiredS1908
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1908_eq] at model
  exact MomentData.excluded1908 ds ss model
def rows1909 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols1909 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD1909 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1909 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46,49]
theorem problem1909_eq : pairedProblem rows1909 cols1909 requiredD1909 requiredS1909 =
    MomentData.problem1909 := by rfl
theorem leaf1909 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1909++rows1909))
    (hc : (q.map Prod.snd).Perm (cols1909++cols1909))
    (hd : ∀ k ∈ requiredD1909, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1909, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1909 cols1909 requiredD1909 requiredS1909
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1909_eq] at model
  exact MomentData.excluded1909 ds ss model
def rows1910 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols1910 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD1910 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS1910 : List Int := [13,16,19,21,22,25,28,31,34,37,40,43,46,49]
theorem problem1910_eq : pairedProblem rows1910 cols1910 requiredD1910 requiredS1910 =
    MomentData.problem1910 := by rfl
theorem leaf1910 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1910++rows1910))
    (hc : (q.map Prod.snd).Perm (cols1910++cols1910))
    (hd : ∀ k ∈ requiredD1910, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1910, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1910 cols1910 requiredD1910 requiredS1910
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1910_eq] at model
  exact MomentData.excluded1910 ds ss model
def rows1911 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols1911 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD1911 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1911 : List Int := [10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1911_eq : pairedProblem rows1911 cols1911 requiredD1911 requiredS1911 =
    MomentData.problem1911 := by rfl
theorem leaf1911 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1911++rows1911))
    (hc : (q.map Prod.snd).Perm (cols1911++cols1911))
    (hd : ∀ k ∈ requiredD1911, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1911, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1911 cols1911 requiredD1911 requiredS1911
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1911_eq] at model
  exact MomentData.excluded1911 ds ss model
def rows1912 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def cols1912 : List Int := [1,2,4,5,7,8,11,14,17,20,23,24,26,27,29]
def requiredD1912 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1912 : List Int := [10,13,16,19,21,22,25,28,31,34,37,40,43,46]
theorem problem1912_eq : pairedProblem rows1912 cols1912 requiredD1912 requiredS1912 =
    MomentData.problem1912 := by rfl
theorem leaf1912 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1912++rows1912))
    (hc : (q.map Prod.snd).Perm (cols1912++cols1912))
    (hd : ∀ k ∈ requiredD1912, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1912, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1912 cols1912 requiredD1912 requiredS1912
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1912_eq] at model
  exact MomentData.excluded1912 ds ss model
def rows1913 : List Int := [1,2,4,5,8,9,11,14,17,20,23,24,26,27,29]
def cols1913 : List Int := [1,2,4,5,8,9,11,14,17,20,23,24,26,27,29]
def requiredD1913 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1913 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1913_eq : pairedProblem rows1913 cols1913 requiredD1913 requiredS1913 =
    MomentData.problem1913 := by rfl
theorem leaf1913 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1913++rows1913))
    (hc : (q.map Prod.snd).Perm (cols1913++cols1913))
    (hd : ∀ k ∈ requiredD1913, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1913, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1913 cols1913 requiredD1913 requiredS1913
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1913_eq] at model
  exact MomentData.excluded1913 ds ss model
def rows1914 : List Int := [1,2,4,5,8,9,11,14,17,20,23,24,26,27,29]
def cols1914 : List Int := [1,2,4,5,8,9,11,14,17,20,23,24,26,27,29]
def requiredD1914 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1914 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1914_eq : pairedProblem rows1914 cols1914 requiredD1914 requiredS1914 =
    MomentData.problem1914 := by rfl
theorem leaf1914 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1914++rows1914))
    (hc : (q.map Prod.snd).Perm (cols1914++cols1914))
    (hd : ∀ k ∈ requiredD1914, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1914, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1914 cols1914 requiredD1914 requiredS1914
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1914_eq] at model
  exact MomentData.excluded1914 ds ss model
def rows1915 : List Int := [1,2,4,5,8,10,11,14,17,20,23,24,26,27,29]
def cols1915 : List Int := [1,2,4,5,8,10,11,14,17,20,23,24,26,27,29]
def requiredD1915 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1915 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1915_eq : pairedProblem rows1915 cols1915 requiredD1915 requiredS1915 =
    MomentData.problem1915 := by rfl
theorem leaf1915 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1915++rows1915))
    (hc : (q.map Prod.snd).Perm (cols1915++cols1915))
    (hd : ∀ k ∈ requiredD1915, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1915, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1915 cols1915 requiredD1915 requiredS1915
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1915_eq] at model
  exact MomentData.excluded1915 ds ss model
def rows1916 : List Int := [1,2,4,5,8,10,11,14,17,20,23,24,26,27,29]
def cols1916 : List Int := [1,2,4,5,8,10,11,14,17,20,23,24,26,27,29]
def requiredD1916 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1916 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1916_eq : pairedProblem rows1916 cols1916 requiredD1916 requiredS1916 =
    MomentData.problem1916 := by rfl
theorem leaf1916 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1916++rows1916))
    (hc : (q.map Prod.snd).Perm (cols1916++cols1916))
    (hd : ∀ k ∈ requiredD1916, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1916, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1916 cols1916 requiredD1916 requiredS1916
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1916_eq] at model
  exact MomentData.excluded1916 ds ss model
def rows1917 : List Int := [1,2,4,5,8,11,12,14,17,20,23,24,26,27,29]
def cols1917 : List Int := [1,2,4,5,8,11,12,14,17,20,23,24,26,27,29]
def requiredD1917 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1917 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1917_eq : pairedProblem rows1917 cols1917 requiredD1917 requiredS1917 =
    MomentData.problem1917 := by rfl
theorem leaf1917 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1917++rows1917))
    (hc : (q.map Prod.snd).Perm (cols1917++cols1917))
    (hd : ∀ k ∈ requiredD1917, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1917, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1917 cols1917 requiredD1917 requiredS1917
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1917_eq] at model
  exact MomentData.excluded1917 ds ss model
def rows1918 : List Int := [1,2,4,5,8,11,12,14,17,20,23,24,26,27,29]
def cols1918 : List Int := [1,2,4,5,8,11,12,14,17,20,23,24,26,27,29]
def requiredD1918 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1918 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1918_eq : pairedProblem rows1918 cols1918 requiredD1918 requiredS1918 =
    MomentData.problem1918 := by rfl
theorem leaf1918 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1918++rows1918))
    (hc : (q.map Prod.snd).Perm (cols1918++cols1918))
    (hd : ∀ k ∈ requiredD1918, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1918, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1918 cols1918 requiredD1918 requiredS1918
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1918_eq] at model
  exact MomentData.excluded1918 ds ss model
def rows1919 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols1919 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD1919 : List Int := [-24,-20,-16,-12,-8,-4,0,4,8,12,16,20,24]
def requiredS1919 : List Int := [3,7,11,15,19,23,27,28,31,35,39,43,47,51,55]
theorem problem1919_eq : pairedProblem rows1919 cols1919 requiredD1919 requiredS1919 =
    MomentData.problem1919 := by rfl
theorem leaf1919 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1919++rows1919))
    (hc : (q.map Prod.snd).Perm (cols1919++cols1919))
    (hd : ∀ k ∈ requiredD1919, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1919, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1919 cols1919 requiredD1919 requiredS1919
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1919_eq] at model
  exact MomentData.excluded1919 ds ss model
#print axioms leaf1792
end Gardner.Kernel.MomentContexts
