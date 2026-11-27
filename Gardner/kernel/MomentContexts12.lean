import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1536 : List Int := [1,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1536 : List Int := [1,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1536 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1536 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1536_eq : pairedProblem rows1536 cols1536 requiredD1536 requiredS1536 =
    MomentData.problem1536 := by rfl
theorem leaf1536 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1536++rows1536))
    (hc : (q.map Prod.snd).Perm (cols1536++cols1536))
    (hd : ∀ k ∈ requiredD1536, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1536, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1536 cols1536 requiredD1536 requiredS1536
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1536_eq] at model
  exact MomentData.excluded1536 ds ss model
def rows1537 : List Int := [0,1,4,7,10,13,16,19,21,22,24,25,27,28,29]
def cols1537 : List Int := [0,1,4,7,10,13,16,19,21,22,24,25,27,28,29]
def requiredD1537 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1537 : List Int := [5,8,11,14,17,20,23,26,28,29,32,35,38,41,44]
theorem problem1537_eq : pairedProblem rows1537 cols1537 requiredD1537 requiredS1537 =
    MomentData.problem1537 := by rfl
theorem leaf1537 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1537++rows1537))
    (hc : (q.map Prod.snd).Perm (cols1537++cols1537))
    (hd : ∀ k ∈ requiredD1537, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1537, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1537 cols1537 requiredD1537 requiredS1537
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1537_eq] at model
  exact MomentData.excluded1537 ds ss model
def rows1538 : List Int := [2,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1538 : List Int := [2,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1538 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1538 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1538_eq : pairedProblem rows1538 cols1538 requiredD1538 requiredS1538 =
    MomentData.problem1538 := by rfl
theorem leaf1538 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1538++rows1538))
    (hc : (q.map Prod.snd).Perm (cols1538++cols1538))
    (hd : ∀ k ∈ requiredD1538, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1538, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1538 cols1538 requiredD1538 requiredS1538
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1538_eq] at model
  exact MomentData.excluded1538 ds ss model
def rows1539 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1539 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1539 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1539 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1539_eq : pairedProblem rows1539 cols1539 requiredD1539 requiredS1539 =
    MomentData.problem1539 := by rfl
theorem leaf1539 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1539++rows1539))
    (hc : (q.map Prod.snd).Perm (cols1539++cols1539))
    (hd : ∀ k ∈ requiredD1539, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1539, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1539 cols1539 requiredD1539 requiredS1539
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1539_eq] at model
  exact MomentData.excluded1539 ds ss model
def rows1540 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1540 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1540 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1540 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1540_eq : pairedProblem rows1540 cols1540 requiredD1540 requiredS1540 =
    MomentData.problem1540 := by rfl
theorem leaf1540 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1540++rows1540))
    (hc : (q.map Prod.snd).Perm (cols1540++cols1540))
    (hd : ∀ k ∈ requiredD1540, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1540, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1540 cols1540 requiredD1540 requiredS1540
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1540_eq] at model
  exact MomentData.excluded1540 ds ss model
def rows1541 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1541 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1541 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1541 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1541_eq : pairedProblem rows1541 cols1541 requiredD1541 requiredS1541 =
    MomentData.problem1541 := by rfl
theorem leaf1541 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1541++rows1541))
    (hc : (q.map Prod.snd).Perm (cols1541++cols1541))
    (hd : ∀ k ∈ requiredD1541, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1541, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1541 cols1541 requiredD1541 requiredS1541
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1541_eq] at model
  exact MomentData.excluded1541 ds ss model
def rows1542 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1542 : List Int := [0,9,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1542 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1542 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1542_eq : pairedProblem rows1542 cols1542 requiredD1542 requiredS1542 =
    MomentData.problem1542 := by rfl
theorem leaf1542 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1542++rows1542))
    (hc : (q.map Prod.snd).Perm (cols1542++cols1542))
    (hd : ∀ k ∈ requiredD1542, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1542, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1542 cols1542 requiredD1542 requiredS1542
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1542_eq] at model
  exact MomentData.excluded1542 ds ss model
def rows1543 : List Int := [3,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1543 : List Int := [3,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1543 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1543 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1543_eq : pairedProblem rows1543 cols1543 requiredD1543 requiredS1543 =
    MomentData.problem1543 := by rfl
theorem leaf1543 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1543++rows1543))
    (hc : (q.map Prod.snd).Perm (cols1543++cols1543))
    (hd : ∀ k ∈ requiredD1543, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1543, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1543 cols1543 requiredD1543 requiredS1543
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1543_eq] at model
  exact MomentData.excluded1543 ds ss model
def rows1544 : List Int := [0,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def cols1544 : List Int := [0,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def requiredD1544 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1544 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1544_eq : pairedProblem rows1544 cols1544 requiredD1544 requiredS1544 =
    MomentData.problem1544 := by rfl
theorem leaf1544 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1544++rows1544))
    (hc : (q.map Prod.snd).Perm (cols1544++cols1544))
    (hd : ∀ k ∈ requiredD1544, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1544, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1544 cols1544 requiredD1544 requiredS1544
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1544_eq] at model
  exact MomentData.excluded1544 ds ss model
def rows1545 : List Int := [0,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def cols1545 : List Int := [0,9,10,11,12,13,14,15,16,17,19,26,27,28,29]
def requiredD1545 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1545 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1545_eq : pairedProblem rows1545 cols1545 requiredD1545 requiredS1545 =
    MomentData.problem1545 := by rfl
theorem leaf1545 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1545++rows1545))
    (hc : (q.map Prod.snd).Perm (cols1545++cols1545))
    (hd : ∀ k ∈ requiredD1545, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1545, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1545 cols1545 requiredD1545 requiredS1545
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1545_eq] at model
  exact MomentData.excluded1545 ds ss model
def rows1546 : List Int := [4,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1546 : List Int := [4,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1546 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1546 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1546_eq : pairedProblem rows1546 cols1546 requiredD1546 requiredS1546 =
    MomentData.problem1546 := by rfl
theorem leaf1546 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1546++rows1546))
    (hc : (q.map Prod.snd).Perm (cols1546++cols1546))
    (hd : ∀ k ∈ requiredD1546, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1546, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1546 cols1546 requiredD1546 requiredS1546
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1546_eq] at model
  exact MomentData.excluded1546 ds ss model
def rows1547 : List Int := [0,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1547 : List Int := [0,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1547 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1547 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1547_eq : pairedProblem rows1547 cols1547 requiredD1547 requiredS1547 =
    MomentData.problem1547 := by rfl
theorem leaf1547 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1547++rows1547))
    (hc : (q.map Prod.snd).Perm (cols1547++cols1547))
    (hd : ∀ k ∈ requiredD1547, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1547, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1547 cols1547 requiredD1547 requiredS1547
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1547_eq] at model
  exact MomentData.excluded1547 ds ss model
def rows1548 : List Int := [0,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1548 : List Int := [0,9,10,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1548 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1548 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1548_eq : pairedProblem rows1548 cols1548 requiredD1548 requiredS1548 =
    MomentData.problem1548 := by rfl
theorem leaf1548 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1548++rows1548))
    (hc : (q.map Prod.snd).Perm (cols1548++cols1548))
    (hd : ∀ k ∈ requiredD1548, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1548, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1548 cols1548 requiredD1548 requiredS1548
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1548_eq] at model
  exact MomentData.excluded1548 ds ss model
def rows1549 : List Int := [0,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1549 : List Int := [0,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1549 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1549 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1549_eq : pairedProblem rows1549 cols1549 requiredD1549 requiredS1549 =
    MomentData.problem1549 := by rfl
theorem leaf1549 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1549++rows1549))
    (hc : (q.map Prod.snd).Perm (cols1549++cols1549))
    (hd : ∀ k ∈ requiredD1549, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1549, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1549 cols1549 requiredD1549 requiredS1549
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1549_eq] at model
  exact MomentData.excluded1549 ds ss model
def rows1550 : List Int := [0,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1550 : List Int := [0,9,10,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1550 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1550 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1550_eq : pairedProblem rows1550 cols1550 requiredD1550 requiredS1550 =
    MomentData.problem1550 := by rfl
theorem leaf1550 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1550++rows1550))
    (hc : (q.map Prod.snd).Perm (cols1550++cols1550))
    (hd : ∀ k ∈ requiredD1550, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1550, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1550 cols1550 requiredD1550 requiredS1550
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1550_eq] at model
  exact MomentData.excluded1550 ds ss model
def rows1551 : List Int := [5,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1551 : List Int := [5,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1551 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1551 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1551_eq : pairedProblem rows1551 cols1551 requiredD1551 requiredS1551 =
    MomentData.problem1551 := by rfl
theorem leaf1551 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1551++rows1551))
    (hc : (q.map Prod.snd).Perm (cols1551++cols1551))
    (hd : ∀ k ∈ requiredD1551, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1551, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1551 cols1551 requiredD1551 requiredS1551
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1551_eq] at model
  exact MomentData.excluded1551 ds ss model
def rows1552 : List Int := [0,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def cols1552 : List Int := [0,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1552 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1552 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1552_eq : pairedProblem rows1552 cols1552 requiredD1552 requiredS1552 =
    MomentData.problem1552 := by rfl
theorem leaf1552 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1552++rows1552))
    (hc : (q.map Prod.snd).Perm (cols1552++cols1552))
    (hd : ∀ k ∈ requiredD1552, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1552, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1552 cols1552 requiredD1552 requiredS1552
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1552_eq] at model
  exact MomentData.excluded1552 ds ss model
def rows1553 : List Int := [0,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def cols1553 : List Int := [0,9,10,11,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1553 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1553 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1553_eq : pairedProblem rows1553 cols1553 requiredD1553 requiredS1553 =
    MomentData.problem1553 := by rfl
theorem leaf1553 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1553++rows1553))
    (hc : (q.map Prod.snd).Perm (cols1553++cols1553))
    (hd : ∀ k ∈ requiredD1553, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1553, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1553 cols1553 requiredD1553 requiredS1553
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1553_eq] at model
  exact MomentData.excluded1553 ds ss model
def rows1554 : List Int := [6,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1554 : List Int := [6,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1554 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1554 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1554_eq : pairedProblem rows1554 cols1554 requiredD1554 requiredS1554 =
    MomentData.problem1554 := by rfl
theorem leaf1554 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1554++rows1554))
    (hc : (q.map Prod.snd).Perm (cols1554++cols1554))
    (hd : ∀ k ∈ requiredD1554, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1554, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1554 cols1554 requiredD1554 requiredS1554
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1554_eq] at model
  exact MomentData.excluded1554 ds ss model
def rows1555 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols1555 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def requiredD1555 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1555 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1555_eq : pairedProblem rows1555 cols1555 requiredD1555 requiredS1555 =
    MomentData.problem1555 := by rfl
theorem leaf1555 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1555++rows1555))
    (hc : (q.map Prod.snd).Perm (cols1555++cols1555))
    (hd : ∀ k ∈ requiredD1555, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1555, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1555 cols1555 requiredD1555 requiredS1555
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1555_eq] at model
  exact MomentData.excluded1555 ds ss model
def rows1556 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols1556 : List Int := [0,9,10,11,12,13,14,15,16,17,23,26,27,28,29]
def requiredD1556 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1556 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1556_eq : pairedProblem rows1556 cols1556 requiredD1556 requiredS1556 =
    MomentData.problem1556 := by rfl
theorem leaf1556 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1556++rows1556))
    (hc : (q.map Prod.snd).Perm (cols1556++cols1556))
    (hd : ∀ k ∈ requiredD1556, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1556, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1556 cols1556 requiredD1556 requiredS1556
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1556_eq] at model
  exact MomentData.excluded1556 ds ss model
def rows1557 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1557 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1557 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1557 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem1557_eq : pairedProblem rows1557 cols1557 requiredD1557 requiredS1557 =
    MomentData.problem1557 := by rfl
theorem leaf1557 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1557++rows1557))
    (hc : (q.map Prod.snd).Perm (cols1557++cols1557))
    (hd : ∀ k ∈ requiredD1557, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1557, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1557 cols1557 requiredD1557 requiredS1557
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1557_eq] at model
  exact MomentData.excluded1557 ds ss model
def rows1558 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1558 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1558 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1558 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem1558_eq : pairedProblem rows1558 cols1558 requiredD1558 requiredS1558 =
    MomentData.problem1558 := by rfl
theorem leaf1558 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1558++rows1558))
    (hc : (q.map Prod.snd).Perm (cols1558++cols1558))
    (hd : ∀ k ∈ requiredD1558, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1558, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1558 cols1558 requiredD1558 requiredS1558
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1558_eq] at model
  exact MomentData.excluded1558 ds ss model
def rows1559 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1559 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1559 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1559 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,41]
theorem problem1559_eq : pairedProblem rows1559 cols1559 requiredD1559 requiredS1559 =
    MomentData.problem1559 := by rfl
theorem leaf1559 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1559++rows1559))
    (hc : (q.map Prod.snd).Perm (cols1559++cols1559))
    (hd : ∀ k ∈ requiredD1559, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1559, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1559 cols1559 requiredD1559 requiredS1559
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1559_eq] at model
  exact MomentData.excluded1559 ds ss model
def rows1560 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1560 : List Int := [7,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1560 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1560 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1560_eq : pairedProblem rows1560 cols1560 requiredD1560 requiredS1560 =
    MomentData.problem1560 := by rfl
theorem leaf1560 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1560++rows1560))
    (hc : (q.map Prod.snd).Perm (cols1560++cols1560))
    (hd : ∀ k ∈ requiredD1560, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1560, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1560 cols1560 requiredD1560 requiredS1560
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1560_eq] at model
  exact MomentData.excluded1560 ds ss model
def rows1561 : List Int := [1,2,4,7,10,13,16,19,22,23,25,26,27,28,29]
def cols1561 : List Int := [1,2,4,7,10,13,16,19,22,23,25,26,27,28,29]
def requiredD1561 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1561 : List Int := [5,8,11,14,17,20,23,24,26,29,32,35,38,41,44]
theorem problem1561_eq : pairedProblem rows1561 cols1561 requiredD1561 requiredS1561 =
    MomentData.problem1561 := by rfl
theorem leaf1561 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1561++rows1561))
    (hc : (q.map Prod.snd).Perm (cols1561++cols1561))
    (hd : ∀ k ∈ requiredD1561, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1561, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1561 cols1561 requiredD1561 requiredS1561
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1561_eq] at model
  exact MomentData.excluded1561 ds ss model
def rows1562 : List Int := [0,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols1562 : List Int := [0,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def requiredD1562 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1562 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1562_eq : pairedProblem rows1562 cols1562 requiredD1562 requiredS1562 =
    MomentData.problem1562 := by rfl
theorem leaf1562 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1562++rows1562))
    (hc : (q.map Prod.snd).Perm (cols1562++cols1562))
    (hd : ∀ k ∈ requiredD1562, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1562, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1562 cols1562 requiredD1562 requiredS1562
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1562_eq] at model
  exact MomentData.excluded1562 ds ss model
def rows1563 : List Int := [0,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols1563 : List Int := [0,9,10,11,12,13,14,15,16,17,24,26,27,28,29]
def requiredD1563 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1563 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1563_eq : pairedProblem rows1563 cols1563 requiredD1563 requiredS1563 =
    MomentData.problem1563 := by rfl
theorem leaf1563 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1563++rows1563))
    (hc : (q.map Prod.snd).Perm (cols1563++cols1563))
    (hd : ∀ k ∈ requiredD1563, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1563, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1563 cols1563 requiredD1563 requiredS1563
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1563_eq] at model
  exact MomentData.excluded1563 ds ss model
def rows1564 : List Int := [0,10,11,12,13,14,15,16,17,18,19,26,27,28,29]
def cols1564 : List Int := [0,10,11,12,13,14,15,16,17,18,19,26,27,28,29]
def requiredD1564 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1564 : List Int := [10,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1564_eq : pairedProblem rows1564 cols1564 requiredD1564 requiredS1564 =
    MomentData.problem1564 := by rfl
theorem leaf1564 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1564++rows1564))
    (hc : (q.map Prod.snd).Perm (cols1564++cols1564))
    (hd : ∀ k ∈ requiredD1564, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1564, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1564 cols1564 requiredD1564 requiredS1564
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1564_eq] at model
  exact MomentData.excluded1564 ds ss model
def rows1565 : List Int := [0,3,6,9,12,15,18,20,21,23,24,26,27,28,29]
def cols1565 : List Int := [0,3,6,9,12,15,18,20,21,23,24,26,27,28,29]
def requiredD1565 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1565 : List Int := [3,6,9,12,15,18,21,24,26,27,30,33,36,39,42]
theorem problem1565_eq : pairedProblem rows1565 cols1565 requiredD1565 requiredS1565 =
    MomentData.problem1565 := by rfl
theorem leaf1565 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1565++rows1565))
    (hc : (q.map Prod.snd).Perm (cols1565++cols1565))
    (hd : ∀ k ∈ requiredD1565, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1565, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1565 cols1565 requiredD1565 requiredS1565
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1565_eq] at model
  exact MomentData.excluded1565 ds ss model
def rows1566 : List Int := [8,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1566 : List Int := [8,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1566 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1566 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1566_eq : pairedProblem rows1566 cols1566 requiredD1566 requiredS1566 =
    MomentData.problem1566 := by rfl
theorem leaf1566 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1566++rows1566))
    (hc : (q.map Prod.snd).Perm (cols1566++cols1566))
    (hd : ∀ k ∈ requiredD1566, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1566, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1566 cols1566 requiredD1566 requiredS1566
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1566_eq] at model
  exact MomentData.excluded1566 ds ss model
def rows1567 : List Int := [8,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def cols1567 : List Int := [8,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def requiredD1567 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1567 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1567_eq : pairedProblem rows1567 cols1567 requiredD1567 requiredS1567 =
    MomentData.problem1567 := by rfl
theorem leaf1567 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1567++rows1567))
    (hc : (q.map Prod.snd).Perm (cols1567++cols1567))
    (hd : ∀ k ∈ requiredD1567, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1567, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1567 cols1567 requiredD1567 requiredS1567
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1567_eq] at model
  exact MomentData.excluded1567 ds ss model
def rows1568 : List Int := [8,9,10,11,12,13,14,15,16,19,25,26,27,28,29]
def cols1568 : List Int := [8,9,10,11,12,13,14,15,16,19,25,26,27,28,29]
def requiredD1568 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1568 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1568_eq : pairedProblem rows1568 cols1568 requiredD1568 requiredS1568 =
    MomentData.problem1568 := by rfl
theorem leaf1568 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1568++rows1568))
    (hc : (q.map Prod.snd).Perm (cols1568++cols1568))
    (hd : ∀ k ∈ requiredD1568, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1568, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1568 cols1568 requiredD1568 requiredS1568
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1568_eq] at model
  exact MomentData.excluded1568 ds ss model
def rows1569 : List Int := [8,9,10,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1569 : List Int := [8,9,10,11,12,13,14,15,16,20,25,26,27,28,29]
def requiredD1569 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1569 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1569_eq : pairedProblem rows1569 cols1569 requiredD1569 requiredS1569 =
    MomentData.problem1569 := by rfl
theorem leaf1569 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1569++rows1569))
    (hc : (q.map Prod.snd).Perm (cols1569++cols1569))
    (hd : ∀ k ∈ requiredD1569, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1569, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1569 cols1569 requiredD1569 requiredS1569
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1569_eq] at model
  exact MomentData.excluded1569 ds ss model
def rows1570 : List Int := [8,9,10,11,12,13,14,15,16,21,25,26,27,28,29]
def cols1570 : List Int := [8,9,10,11,12,13,14,15,16,21,25,26,27,28,29]
def requiredD1570 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1570 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1570_eq : pairedProblem rows1570 cols1570 requiredD1570 requiredS1570 =
    MomentData.problem1570 := by rfl
theorem leaf1570 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1570++rows1570))
    (hc : (q.map Prod.snd).Perm (cols1570++cols1570))
    (hd : ∀ k ∈ requiredD1570, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1570, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1570 cols1570 requiredD1570 requiredS1570
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1570_eq] at model
  exact MomentData.excluded1570 ds ss model
def rows1571 : List Int := [8,9,10,11,12,13,14,15,16,22,25,26,27,28,29]
def cols1571 : List Int := [8,9,10,11,12,13,14,15,16,22,25,26,27,28,29]
def requiredD1571 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1571 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1571_eq : pairedProblem rows1571 cols1571 requiredD1571 requiredS1571 =
    MomentData.problem1571 := by rfl
theorem leaf1571 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1571++rows1571))
    (hc : (q.map Prod.snd).Perm (cols1571++cols1571))
    (hd : ∀ k ∈ requiredD1571, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1571, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1571 cols1571 requiredD1571 requiredS1571
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1571_eq] at model
  exact MomentData.excluded1571 ds ss model
def rows1572 : List Int := [8,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def cols1572 : List Int := [8,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def requiredD1572 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1572 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1572_eq : pairedProblem rows1572 cols1572 requiredD1572 requiredS1572 =
    MomentData.problem1572 := by rfl
theorem leaf1572 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1572++rows1572))
    (hc : (q.map Prod.snd).Perm (cols1572++cols1572))
    (hd : ∀ k ∈ requiredD1572, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1572, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1572 cols1572 requiredD1572 requiredS1572
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1572_eq] at model
  exact MomentData.excluded1572 ds ss model
def rows1573 : List Int := [0,1,3,4,7,10,13,15,16,19,22,25,26,28,29]
def cols1573 : List Int := [0,1,3,4,7,10,13,15,16,19,22,25,26,28,29]
def requiredD1573 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1573 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1573_eq : pairedProblem rows1573 cols1573 requiredD1573 requiredS1573 =
    MomentData.problem1573 := by rfl
theorem leaf1573 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1573++rows1573))
    (hc : (q.map Prod.snd).Perm (cols1573++cols1573))
    (hd : ∀ k ∈ requiredD1573, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1573, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1573 cols1573 requiredD1573 requiredS1573
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1573_eq] at model
  exact MomentData.excluded1573 ds ss model
def rows1574 : List Int := [0,1,3,4,7,10,13,15,16,19,22,25,26,28,29]
def cols1574 : List Int := [0,1,3,4,7,10,13,15,16,19,22,25,26,28,29]
def requiredD1574 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1574 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1574_eq : pairedProblem rows1574 cols1574 requiredD1574 requiredS1574 =
    MomentData.problem1574 := by rfl
theorem leaf1574 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1574++rows1574))
    (hc : (q.map Prod.snd).Perm (cols1574++cols1574))
    (hd : ∀ k ∈ requiredD1574, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1574, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1574 cols1574 requiredD1574 requiredS1574
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1574_eq] at model
  exact MomentData.excluded1574 ds ss model
def rows1575 : List Int := [0,1,3,4,7,10,13,16,17,19,22,25,26,28,29]
def cols1575 : List Int := [0,1,3,4,7,10,13,16,17,19,22,25,26,28,29]
def requiredD1575 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1575 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1575_eq : pairedProblem rows1575 cols1575 requiredD1575 requiredS1575 =
    MomentData.problem1575 := by rfl
theorem leaf1575 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1575++rows1575))
    (hc : (q.map Prod.snd).Perm (cols1575++cols1575))
    (hd : ∀ k ∈ requiredD1575, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1575, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1575 cols1575 requiredD1575 requiredS1575
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1575_eq] at model
  exact MomentData.excluded1575 ds ss model
def rows1576 : List Int := [0,1,3,4,7,10,13,16,17,19,22,25,26,28,29]
def cols1576 : List Int := [0,1,3,4,7,10,13,16,17,19,22,25,26,28,29]
def requiredD1576 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1576 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1576_eq : pairedProblem rows1576 cols1576 requiredD1576 requiredS1576 =
    MomentData.problem1576 := by rfl
theorem leaf1576 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1576++rows1576))
    (hc : (q.map Prod.snd).Perm (cols1576++cols1576))
    (hd : ∀ k ∈ requiredD1576, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1576, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1576 cols1576 requiredD1576 requiredS1576
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1576_eq] at model
  exact MomentData.excluded1576 ds ss model
def rows1577 : List Int := [0,1,3,5,7,9,11,17,18,20,22,24,26,28,29]
def cols1577 : List Int := [0,1,3,5,7,9,11,17,18,20,22,24,26,28,29]
def requiredD1577 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1577 : List Int := [17,18,19,21,23,25,27,29,31,33,35,37,39,40,41]
theorem problem1577_eq : pairedProblem rows1577 cols1577 requiredD1577 requiredS1577 =
    MomentData.problem1577 := by rfl
theorem leaf1577 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1577++rows1577))
    (hc : (q.map Prod.snd).Perm (cols1577++cols1577))
    (hd : ∀ k ∈ requiredD1577, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1577, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1577 cols1577 requiredD1577 requiredS1577
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1577_eq] at model
  exact MomentData.excluded1577 ds ss model
def rows1578 : List Int := [0,2,3,4,6,9,12,15,18,21,24,25,27,28,29]
def cols1578 : List Int := [0,2,3,4,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1578 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1578 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1578_eq : pairedProblem rows1578 cols1578 requiredD1578 requiredS1578 =
    MomentData.problem1578 := by rfl
theorem leaf1578 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1578++rows1578))
    (hc : (q.map Prod.snd).Perm (cols1578++cols1578))
    (hd : ∀ k ∈ requiredD1578, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1578, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1578 cols1578 requiredD1578 requiredS1578
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1578_eq] at model
  exact MomentData.excluded1578 ds ss model
def rows1579 : List Int := [0,2,3,4,6,9,12,15,18,21,24,25,27,28,29]
def cols1579 : List Int := [0,2,3,4,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1579 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1579 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1579_eq : pairedProblem rows1579 cols1579 requiredD1579 requiredS1579 =
    MomentData.problem1579 := by rfl
theorem leaf1579 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1579++rows1579))
    (hc : (q.map Prod.snd).Perm (cols1579++cols1579))
    (hd : ∀ k ∈ requiredD1579, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1579, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1579 cols1579 requiredD1579 requiredS1579
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1579_eq] at model
  exact MomentData.excluded1579 ds ss model
def rows1580 : List Int := [0,1,3,4,7,10,13,16,18,19,22,25,26,28,29]
def cols1580 : List Int := [0,1,3,4,7,10,13,16,18,19,22,25,26,28,29]
def requiredD1580 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1580 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1580_eq : pairedProblem rows1580 cols1580 requiredD1580 requiredS1580 =
    MomentData.problem1580 := by rfl
theorem leaf1580 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1580++rows1580))
    (hc : (q.map Prod.snd).Perm (cols1580++cols1580))
    (hd : ∀ k ∈ requiredD1580, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1580, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1580 cols1580 requiredD1580 requiredS1580
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1580_eq] at model
  exact MomentData.excluded1580 ds ss model
def rows1581 : List Int := [0,1,3,4,7,10,13,16,18,19,22,25,26,28,29]
def cols1581 : List Int := [0,1,3,4,7,10,13,16,18,19,22,25,26,28,29]
def requiredD1581 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1581 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1581_eq : pairedProblem rows1581 cols1581 requiredD1581 requiredS1581 =
    MomentData.problem1581 := by rfl
theorem leaf1581 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1581++rows1581))
    (hc : (q.map Prod.snd).Perm (cols1581++cols1581))
    (hd : ∀ k ∈ requiredD1581, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1581, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1581 cols1581 requiredD1581 requiredS1581
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1581_eq] at model
  exact MomentData.excluded1581 ds ss model
def rows1582 : List Int := [1,2,4,5,7,8,11,14,17,20,23,26,27,28,29]
def cols1582 : List Int := [1,2,4,5,7,8,11,14,17,20,23,26,27,28,29]
def requiredD1582 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1582 : List Int := [10,13,16,19,22,24,25,28,31,34,37,40,43,46,49]
theorem problem1582_eq : pairedProblem rows1582 cols1582 requiredD1582 requiredS1582 =
    MomentData.problem1582 := by rfl
theorem leaf1582 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1582++rows1582))
    (hc : (q.map Prod.snd).Perm (cols1582++cols1582))
    (hd : ∀ k ∈ requiredD1582, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1582, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1582 cols1582 requiredD1582 requiredS1582
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1582_eq] at model
  exact MomentData.excluded1582 ds ss model
def rows1583 : List Int := [0,1,3,4,7,10,13,16,19,20,22,25,26,28,29]
def cols1583 : List Int := [0,1,3,4,7,10,13,16,19,20,22,25,26,28,29]
def requiredD1583 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1583 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1583_eq : pairedProblem rows1583 cols1583 requiredD1583 requiredS1583 =
    MomentData.problem1583 := by rfl
theorem leaf1583 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1583++rows1583))
    (hc : (q.map Prod.snd).Perm (cols1583++cols1583))
    (hd : ∀ k ∈ requiredD1583, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1583, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1583 cols1583 requiredD1583 requiredS1583
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1583_eq] at model
  exact MomentData.excluded1583 ds ss model
def rows1584 : List Int := [0,1,3,4,7,10,13,16,19,20,22,25,26,28,29]
def cols1584 : List Int := [0,1,3,4,7,10,13,16,19,20,22,25,26,28,29]
def requiredD1584 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1584 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1584_eq : pairedProblem rows1584 cols1584 requiredD1584 requiredS1584 =
    MomentData.problem1584 := by rfl
theorem leaf1584 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1584++rows1584))
    (hc : (q.map Prod.snd).Perm (cols1584++cols1584))
    (hd : ∀ k ∈ requiredD1584, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1584, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1584 cols1584 requiredD1584 requiredS1584
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1584_eq] at model
  exact MomentData.excluded1584 ds ss model
def rows1585 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols1585 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1585 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1585 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45,48]
theorem problem1585_eq : pairedProblem rows1585 cols1585 requiredD1585 requiredS1585 =
    MomentData.problem1585 := by rfl
theorem leaf1585 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1585++rows1585))
    (hc : (q.map Prod.snd).Perm (cols1585++cols1585))
    (hd : ∀ k ∈ requiredD1585, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1585, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1585 cols1585 requiredD1585 requiredS1585
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1585_eq] at model
  exact MomentData.excluded1585 ds ss model
def rows1586 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols1586 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1586 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1586 : List Int := [12,15,18,21,23,24,27,30,33,36,39,42,45,48]
theorem problem1586_eq : pairedProblem rows1586 cols1586 requiredD1586 requiredS1586 =
    MomentData.problem1586 := by rfl
theorem leaf1586 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1586++rows1586))
    (hc : (q.map Prod.snd).Perm (cols1586++cols1586))
    (hd : ∀ k ∈ requiredD1586, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1586, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1586 cols1586 requiredD1586 requiredS1586
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1586_eq] at model
  exact MomentData.excluded1586 ds ss model
def rows1587 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols1587 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1587 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1587 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1587_eq : pairedProblem rows1587 cols1587 requiredD1587 requiredS1587 =
    MomentData.problem1587 := by rfl
theorem leaf1587 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1587++rows1587))
    (hc : (q.map Prod.snd).Perm (cols1587++cols1587))
    (hd : ∀ k ∈ requiredD1587, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1587, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1587 cols1587 requiredD1587 requiredS1587
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1587_eq] at model
  exact MomentData.excluded1587 ds ss model
def rows1588 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def cols1588 : List Int := [0,2,3,5,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1588 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1588 : List Int := [9,12,15,18,21,23,24,27,30,33,36,39,42,45]
theorem problem1588_eq : pairedProblem rows1588 cols1588 requiredD1588 requiredS1588 =
    MomentData.problem1588 := by rfl
theorem leaf1588 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1588++rows1588))
    (hc : (q.map Prod.snd).Perm (cols1588++cols1588))
    (hd : ∀ k ∈ requiredD1588, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1588, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1588 cols1588 requiredD1588 requiredS1588
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1588_eq] at model
  exact MomentData.excluded1588 ds ss model
def rows1589 : List Int := [0,2,4,5,6,8,10,17,19,21,23,25,27,28,29]
def cols1589 : List Int := [0,2,4,5,6,8,10,17,19,21,23,25,27,28,29]
def requiredD1589 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1589 : List Int := [15,16,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1589_eq : pairedProblem rows1589 cols1589 requiredD1589 requiredS1589 =
    MomentData.problem1589 := by rfl
theorem leaf1589 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1589++rows1589))
    (hc : (q.map Prod.snd).Perm (cols1589++cols1589))
    (hd : ∀ k ∈ requiredD1589, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1589, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1589 cols1589 requiredD1589 requiredS1589
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1589_eq] at model
  exact MomentData.excluded1589 ds ss model
def rows1590 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def cols1590 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def requiredD1590 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1590 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1590_eq : pairedProblem rows1590 cols1590 requiredD1590 requiredS1590 =
    MomentData.problem1590 := by rfl
theorem leaf1590 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1590++rows1590))
    (hc : (q.map Prod.snd).Perm (cols1590++cols1590))
    (hd : ∀ k ∈ requiredD1590, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1590, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1590 cols1590 requiredD1590 requiredS1590
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1590_eq] at model
  exact MomentData.excluded1590 ds ss model
def rows1591 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def cols1591 : List Int := [0,1,3,4,7,10,13,16,19,21,22,25,26,28,29]
def requiredD1591 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1591 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1591_eq : pairedProblem rows1591 cols1591 requiredD1591 requiredS1591 =
    MomentData.problem1591 := by rfl
theorem leaf1591 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1591++rows1591))
    (hc : (q.map Prod.snd).Perm (cols1591++cols1591))
    (hd : ∀ k ∈ requiredD1591, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1591, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1591 cols1591 requiredD1591 requiredS1591
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1591_eq] at model
  exact MomentData.excluded1591 ds ss model
def rows1592 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols1592 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD1592 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1592 : List Int := [8,11,14,17,20,23,26,29,32,33,35,38,41,44,47]
theorem problem1592_eq : pairedProblem rows1592 cols1592 requiredD1592 requiredS1592 =
    MomentData.problem1592 := by rfl
theorem leaf1592 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1592++rows1592))
    (hc : (q.map Prod.snd).Perm (cols1592++cols1592))
    (hd : ∀ k ∈ requiredD1592, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1592, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1592 cols1592 requiredD1592 requiredS1592
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1592_eq] at model
  exact MomentData.excluded1592 ds ss model
def rows1593 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols1593 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD1593 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1593 : List Int := [11,14,17,20,23,26,29,32,33,35,38,41,44,47]
theorem problem1593_eq : pairedProblem rows1593 cols1593 requiredD1593 requiredS1593 =
    MomentData.problem1593 := by rfl
theorem leaf1593 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1593++rows1593))
    (hc : (q.map Prod.snd).Perm (cols1593++cols1593))
    (hd : ∀ k ∈ requiredD1593, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1593, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1593 cols1593 requiredD1593 requiredS1593
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1593_eq] at model
  exact MomentData.excluded1593 ds ss model
def rows1594 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols1594 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD1594 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1594 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1594_eq : pairedProblem rows1594 cols1594 requiredD1594 requiredS1594 =
    MomentData.problem1594 := by rfl
theorem leaf1594 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1594++rows1594))
    (hc : (q.map Prod.snd).Perm (cols1594++cols1594))
    (hd : ∀ k ∈ requiredD1594, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1594, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1594 cols1594 requiredD1594 requiredS1594
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1594_eq] at model
  exact MomentData.excluded1594 ds ss model
def rows1595 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def cols1595 : List Int := [0,1,3,4,7,10,13,16,19,22,23,25,26,28,29]
def requiredD1595 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1595 : List Int := [8,11,14,17,20,23,26,29,32,33,35,38,41,44]
theorem problem1595_eq : pairedProblem rows1595 cols1595 requiredD1595 requiredS1595 =
    MomentData.problem1595 := by rfl
theorem leaf1595 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1595++rows1595))
    (hc : (q.map Prod.snd).Perm (cols1595++cols1595))
    (hd : ∀ k ∈ requiredD1595, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1595, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1595 cols1595 requiredD1595 requiredS1595
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1595_eq] at model
  exact MomentData.excluded1595 ds ss model
def rows1596 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def cols1596 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def requiredD1596 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1596 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1596_eq : pairedProblem rows1596 cols1596 requiredD1596 requiredS1596 =
    MomentData.problem1596 := by rfl
theorem leaf1596 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1596++rows1596))
    (hc : (q.map Prod.snd).Perm (cols1596++cols1596))
    (hd : ∀ k ∈ requiredD1596, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1596, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1596 cols1596 requiredD1596 requiredS1596
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1596_eq] at model
  exact MomentData.excluded1596 ds ss model
def rows1597 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def cols1597 : List Int := [0,2,3,6,7,9,12,15,18,21,24,25,27,28,29]
def requiredD1597 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1597 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1597_eq : pairedProblem rows1597 cols1597 requiredD1597 requiredS1597 =
    MomentData.problem1597 := by rfl
theorem leaf1597 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1597++rows1597))
    (hc : (q.map Prod.snd).Perm (cols1597++cols1597))
    (hd : ∀ k ∈ requiredD1597, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1597, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1597 cols1597 requiredD1597 requiredS1597
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1597_eq] at model
  exact MomentData.excluded1597 ds ss model
def rows1598 : List Int := [0,2,4,6,7,8,10,17,19,21,23,25,27,28,29]
def cols1598 : List Int := [0,2,4,6,7,8,10,17,19,21,23,25,27,28,29]
def requiredD1598 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1598 : List Int := [15,16,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1598_eq : pairedProblem rows1598 cols1598 requiredD1598 requiredS1598 =
    MomentData.problem1598 := by rfl
theorem leaf1598 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1598++rows1598))
    (hc : (q.map Prod.snd).Perm (cols1598++cols1598))
    (hd : ∀ k ∈ requiredD1598, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1598, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1598 cols1598 requiredD1598 requiredS1598
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1598_eq] at model
  exact MomentData.excluded1598 ds ss model
def rows1599 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,26,28,29]
def cols1599 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,26,28,29]
def requiredD1599 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1599 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1599_eq : pairedProblem rows1599 cols1599 requiredD1599 requiredS1599 =
    MomentData.problem1599 := by rfl
theorem leaf1599 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1599++rows1599))
    (hc : (q.map Prod.snd).Perm (cols1599++cols1599))
    (hd : ∀ k ∈ requiredD1599, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1599, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1599 cols1599 requiredD1599 requiredS1599
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1599_eq] at model
  exact MomentData.excluded1599 ds ss model
def rows1600 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,26,28,29]
def cols1600 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,26,28,29]
def requiredD1600 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1600 : List Int := [11,14,17,20,23,25,26,29,32,33,35,38,41,44,47]
theorem problem1600_eq : pairedProblem rows1600 cols1600 requiredD1600 requiredS1600 =
    MomentData.problem1600 := by rfl
theorem leaf1600 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1600++rows1600))
    (hc : (q.map Prod.snd).Perm (cols1600++cols1600))
    (hd : ∀ k ∈ requiredD1600, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1600, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1600 cols1600 requiredD1600 requiredS1600
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1600_eq] at model
  exact MomentData.excluded1600 ds ss model
def rows1601 : List Int := [0,2,3,6,8,9,12,15,18,21,24,25,27,28,29]
def cols1601 : List Int := [0,2,3,6,8,9,12,15,18,21,24,25,27,28,29]
def requiredD1601 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1601 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1601_eq : pairedProblem rows1601 cols1601 requiredD1601 requiredS1601 =
    MomentData.problem1601 := by rfl
theorem leaf1601 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1601++rows1601))
    (hc : (q.map Prod.snd).Perm (cols1601++cols1601))
    (hd : ∀ k ∈ requiredD1601, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1601, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1601 cols1601 requiredD1601 requiredS1601
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1601_eq] at model
  exact MomentData.excluded1601 ds ss model
def rows1602 : List Int := [0,2,3,6,8,9,12,15,18,21,24,25,27,28,29]
def cols1602 : List Int := [0,2,3,6,8,9,12,15,18,21,24,25,27,28,29]
def requiredD1602 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1602 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1602_eq : pairedProblem rows1602 cols1602 requiredD1602 requiredS1602 =
    MomentData.problem1602 := by rfl
theorem leaf1602 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1602++rows1602))
    (hc : (q.map Prod.snd).Perm (cols1602++cols1602))
    (hd : ∀ k ∈ requiredD1602, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1602, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1602 cols1602 requiredD1602 requiredS1602
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1602_eq] at model
  exact MomentData.excluded1602 ds ss model
def rows1603 : List Int := [0,2,4,6,8,9,10,17,19,21,23,25,27,28,29]
def cols1603 : List Int := [0,2,4,6,8,9,10,17,19,21,23,25,27,28,29]
def requiredD1603 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1603 : List Int := [15,16,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1603_eq : pairedProblem rows1603 cols1603 requiredD1603 requiredS1603 =
    MomentData.problem1603 := by rfl
theorem leaf1603 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1603++rows1603))
    (hc : (q.map Prod.snd).Perm (cols1603++cols1603))
    (hd : ∀ k ∈ requiredD1603, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1603, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1603 cols1603 requiredD1603 requiredS1603
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1603_eq] at model
  exact MomentData.excluded1603 ds ss model
def rows1604 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,27,28,29]
def cols1604 : List Int := [0,2,3,5,6,8,9,12,15,18,21,24,27,28,29]
def requiredD1604 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1604 : List Int := [12,15,18,21,24,26,27,30,33,36,39,42,45,48,51]
theorem problem1604_eq : pairedProblem rows1604 cols1604 requiredD1604 requiredS1604 =
    MomentData.problem1604 := by rfl
theorem leaf1604 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1604++rows1604))
    (hc : (q.map Prod.snd).Perm (cols1604++cols1604))
    (hd : ∀ k ∈ requiredD1604, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1604, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1604 cols1604 requiredD1604 requiredS1604
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1604_eq] at model
  exact MomentData.excluded1604 ds ss model
def rows1605 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1605 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1605 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1605 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1605_eq : pairedProblem rows1605 cols1605 requiredD1605 requiredS1605 =
    MomentData.problem1605 := by rfl
theorem leaf1605 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1605++rows1605))
    (hc : (q.map Prod.snd).Perm (cols1605++cols1605))
    (hd : ∀ k ∈ requiredD1605, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1605, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1605 cols1605 requiredD1605 requiredS1605
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1605_eq] at model
  exact MomentData.excluded1605 ds ss model
def rows1606 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1606 : List Int := [0,2,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1606 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1606 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1606_eq : pairedProblem rows1606 cols1606 requiredD1606 requiredS1606 =
    MomentData.problem1606 := by rfl
theorem leaf1606 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1606++rows1606))
    (hc : (q.map Prod.snd).Perm (cols1606++cols1606))
    (hd : ∀ k ∈ requiredD1606, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1606, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1606 cols1606 requiredD1606 requiredS1606
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1606_eq] at model
  exact MomentData.excluded1606 ds ss model
def rows1607 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols1607 : List Int := [0,7,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD1607 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1607 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,44]
theorem problem1607_eq : pairedProblem rows1607 cols1607 requiredD1607 requiredS1607 =
    MomentData.problem1607 := by rfl
theorem leaf1607 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1607++rows1607))
    (hc : (q.map Prod.snd).Perm (cols1607++cols1607))
    (hd : ∀ k ∈ requiredD1607, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1607, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1607 cols1607 requiredD1607 requiredS1607
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1607_eq] at model
  exact MomentData.excluded1607 ds ss model
def rows1608 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1608 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1608 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1608 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1608_eq : pairedProblem rows1608 cols1608 requiredD1608 requiredS1608 =
    MomentData.problem1608 := by rfl
theorem leaf1608 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1608++rows1608))
    (hc : (q.map Prod.snd).Perm (cols1608++cols1608))
    (hd : ∀ k ∈ requiredD1608, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1608, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1608 cols1608 requiredD1608 requiredS1608
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1608_eq] at model
  exact MomentData.excluded1608 ds ss model
def rows1609 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1609 : List Int := [0,3,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1609 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1609 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1609_eq : pairedProblem rows1609 cols1609 requiredD1609 requiredS1609 =
    MomentData.problem1609 := by rfl
theorem leaf1609 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1609++rows1609))
    (hc : (q.map Prod.snd).Perm (cols1609++cols1609))
    (hd : ∀ k ∈ requiredD1609, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1609, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1609 cols1609 requiredD1609 requiredS1609
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1609_eq] at model
  exact MomentData.excluded1609 ds ss model
def rows1610 : List Int := [0,2,3,6,9,10,12,15,18,21,24,25,27,28,29]
def cols1610 : List Int := [0,2,3,6,9,10,12,15,18,21,24,25,27,28,29]
def requiredD1610 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1610 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1610_eq : pairedProblem rows1610 cols1610 requiredD1610 requiredS1610 =
    MomentData.problem1610 := by rfl
theorem leaf1610 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1610++rows1610))
    (hc : (q.map Prod.snd).Perm (cols1610++cols1610))
    (hd : ∀ k ∈ requiredD1610, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1610, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1610 cols1610 requiredD1610 requiredS1610
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1610_eq] at model
  exact MomentData.excluded1610 ds ss model
def rows1611 : List Int := [0,2,3,6,9,10,12,15,18,21,24,25,27,28,29]
def cols1611 : List Int := [0,2,3,6,9,10,12,15,18,21,24,25,27,28,29]
def requiredD1611 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1611 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1611_eq : pairedProblem rows1611 cols1611 requiredD1611 requiredS1611 =
    MomentData.problem1611 := by rfl
theorem leaf1611 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1611++rows1611))
    (hc : (q.map Prod.snd).Perm (cols1611++cols1611))
    (hd : ∀ k ∈ requiredD1611, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1611, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1611 cols1611 requiredD1611 requiredS1611
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1611_eq] at model
  exact MomentData.excluded1611 ds ss model
def rows1612 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1612 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1612 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1612 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1612_eq : pairedProblem rows1612 cols1612 requiredD1612 requiredS1612 =
    MomentData.problem1612 := by rfl
theorem leaf1612 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1612++rows1612))
    (hc : (q.map Prod.snd).Perm (cols1612++cols1612))
    (hd : ∀ k ∈ requiredD1612, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1612, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1612 cols1612 requiredD1612 requiredS1612
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1612_eq] at model
  exact MomentData.excluded1612 ds ss model
def rows1613 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1613 : List Int := [0,4,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1613 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1613 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1613_eq : pairedProblem rows1613 cols1613 requiredD1613 requiredS1613 =
    MomentData.problem1613 := by rfl
theorem leaf1613 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1613++rows1613))
    (hc : (q.map Prod.snd).Perm (cols1613++cols1613))
    (hd : ∀ k ∈ requiredD1613, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1613, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1613 cols1613 requiredD1613 requiredS1613
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1613_eq] at model
  exact MomentData.excluded1613 ds ss model
def rows1614 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1614 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1614 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1614 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1614_eq : pairedProblem rows1614 cols1614 requiredD1614 requiredS1614 =
    MomentData.problem1614 := by rfl
theorem leaf1614 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1614++rows1614))
    (hc : (q.map Prod.snd).Perm (cols1614++cols1614))
    (hd : ∀ k ∈ requiredD1614, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1614, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1614 cols1614 requiredD1614 requiredS1614
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1614_eq] at model
  exact MomentData.excluded1614 ds ss model
def rows1615 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1615 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1615 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1615 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1615_eq : pairedProblem rows1615 cols1615 requiredD1615 requiredS1615 =
    MomentData.problem1615 := by rfl
theorem leaf1615 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1615++rows1615))
    (hc : (q.map Prod.snd).Perm (cols1615++cols1615))
    (hd : ∀ k ∈ requiredD1615, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1615, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1615 cols1615 requiredD1615 requiredS1615
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1615_eq] at model
  exact MomentData.excluded1615 ds ss model
def rows1616 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1616 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1616 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1616 : List Int := [11,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1616_eq : pairedProblem rows1616 cols1616 requiredD1616 requiredS1616 =
    MomentData.problem1616 := by rfl
theorem leaf1616 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1616++rows1616))
    (hc : (q.map Prod.snd).Perm (cols1616++cols1616))
    (hd : ∀ k ∈ requiredD1616, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1616, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1616 cols1616 requiredD1616 requiredS1616
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1616_eq] at model
  exact MomentData.excluded1616 ds ss model
def rows1617 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def cols1617 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,20,28,29]
def requiredD1617 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1617 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1617_eq : pairedProblem rows1617 cols1617 requiredD1617 requiredS1617 =
    MomentData.problem1617 := by rfl
theorem leaf1617 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1617++rows1617))
    (hc : (q.map Prod.snd).Perm (cols1617++cols1617))
    (hd : ∀ k ∈ requiredD1617, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1617, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1617 cols1617 requiredD1617 requiredS1617
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1617_eq] at model
  exact MomentData.excluded1617 ds ss model
def rows1618 : List Int := [0,2,3,6,9,11,12,15,18,21,24,25,27,28,29]
def cols1618 : List Int := [0,2,3,6,9,11,12,15,18,21,24,25,27,28,29]
def requiredD1618 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1618 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1618_eq : pairedProblem rows1618 cols1618 requiredD1618 requiredS1618 =
    MomentData.problem1618 := by rfl
theorem leaf1618 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1618++rows1618))
    (hc : (q.map Prod.snd).Perm (cols1618++cols1618))
    (hd : ∀ k ∈ requiredD1618, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1618, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1618 cols1618 requiredD1618 requiredS1618
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1618_eq] at model
  exact MomentData.excluded1618 ds ss model
def rows1619 : List Int := [0,2,3,6,9,11,12,15,18,21,24,25,27,28,29]
def cols1619 : List Int := [0,2,3,6,9,11,12,15,18,21,24,25,27,28,29]
def requiredD1619 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1619 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1619_eq : pairedProblem rows1619 cols1619 requiredD1619 requiredS1619 =
    MomentData.problem1619 := by rfl
theorem leaf1619 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1619++rows1619))
    (hc : (q.map Prod.snd).Perm (cols1619++cols1619))
    (hd : ∀ k ∈ requiredD1619, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1619, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1619 cols1619 requiredD1619 requiredS1619
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1619_eq] at model
  exact MomentData.excluded1619 ds ss model
def rows1620 : List Int := [0,2,4,6,8,10,11,17,19,21,23,25,27,28,29]
def cols1620 : List Int := [0,2,4,6,8,10,11,17,19,21,23,25,27,28,29]
def requiredD1620 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1620 : List Int := [15,16,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1620_eq : pairedProblem rows1620 cols1620 requiredD1620 requiredS1620 =
    MomentData.problem1620 := by rfl
theorem leaf1620 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1620++rows1620))
    (hc : (q.map Prod.snd).Perm (cols1620++cols1620))
    (hd : ∀ k ∈ requiredD1620, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1620, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1620 cols1620 requiredD1620 requiredS1620
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1620_eq] at model
  exact MomentData.excluded1620 ds ss model
def rows1621 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1621 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1621 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1621 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1621_eq : pairedProblem rows1621 cols1621 requiredD1621 requiredS1621 =
    MomentData.problem1621 := by rfl
theorem leaf1621 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1621++rows1621))
    (hc : (q.map Prod.snd).Perm (cols1621++cols1621))
    (hd : ∀ k ∈ requiredD1621, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1621, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1621 cols1621 requiredD1621 requiredS1621
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1621_eq] at model
  exact MomentData.excluded1621 ds ss model
def rows1622 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1622 : List Int := [0,5,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1622 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1622 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1622_eq : pairedProblem rows1622 cols1622 requiredD1622 requiredS1622 =
    MomentData.problem1622 := by rfl
theorem leaf1622 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1622++rows1622))
    (hc : (q.map Prod.snd).Perm (cols1622++cols1622))
    (hd : ∀ k ∈ requiredD1622, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1622, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1622 cols1622 requiredD1622 requiredS1622
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1622_eq] at model
  exact MomentData.excluded1622 ds ss model
def rows1623 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,21,28,29]
def cols1623 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,21,28,29]
def requiredD1623 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1623 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1623_eq : pairedProblem rows1623 cols1623 requiredD1623 requiredS1623 =
    MomentData.problem1623 := by rfl
theorem leaf1623 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1623++rows1623))
    (hc : (q.map Prod.snd).Perm (cols1623++cols1623))
    (hd : ∀ k ∈ requiredD1623, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1623, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1623 cols1623 requiredD1623 requiredS1623
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1623_eq] at model
  exact MomentData.excluded1623 ds ss model
def rows1624 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,21,28,29]
def cols1624 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,21,28,29]
def requiredD1624 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1624 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1624_eq : pairedProblem rows1624 cols1624 requiredD1624 requiredS1624 =
    MomentData.problem1624 := by rfl
theorem leaf1624 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1624++rows1624))
    (hc : (q.map Prod.snd).Perm (cols1624++cols1624))
    (hd : ∀ k ∈ requiredD1624, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1624, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1624 cols1624 requiredD1624 requiredS1624
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1624_eq] at model
  exact MomentData.excluded1624 ds ss model
def rows1625 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1625 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def requiredD1625 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1625 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1625_eq : pairedProblem rows1625 cols1625 requiredD1625 requiredS1625 =
    MomentData.problem1625 := by rfl
theorem leaf1625 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1625++rows1625))
    (hc : (q.map Prod.snd).Perm (cols1625++cols1625))
    (hd : ∀ k ∈ requiredD1625, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1625, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1625 cols1625 requiredD1625 requiredS1625
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1625_eq] at model
  exact MomentData.excluded1625 ds ss model
def rows1626 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1626 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def requiredD1626 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1626 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1626_eq : pairedProblem rows1626 cols1626 requiredD1626 requiredS1626 =
    MomentData.problem1626 := by rfl
theorem leaf1626 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1626++rows1626))
    (hc : (q.map Prod.snd).Perm (cols1626++cols1626))
    (hd : ∀ k ∈ requiredD1626, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1626, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1626 cols1626 requiredD1626 requiredS1626
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1626_eq] at model
  exact MomentData.excluded1626 ds ss model
def rows1627 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1627 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1627 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS1627 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem1627_eq : pairedProblem rows1627 cols1627 requiredD1627 requiredS1627 =
    MomentData.problem1627 := by rfl
theorem leaf1627 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1627++rows1627))
    (hc : (q.map Prod.snd).Perm (cols1627++cols1627))
    (hd : ∀ k ∈ requiredD1627, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1627, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1627 cols1627 requiredD1627 requiredS1627
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1627_eq] at model
  exact MomentData.excluded1627 ds ss model
def rows1628 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,22,28,29]
def cols1628 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1628 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1628 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1628_eq : pairedProblem rows1628 cols1628 requiredD1628 requiredS1628 =
    MomentData.problem1628 := by rfl
theorem leaf1628 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1628++rows1628))
    (hc : (q.map Prod.snd).Perm (cols1628++cols1628))
    (hd : ∀ k ∈ requiredD1628, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1628, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1628 cols1628 requiredD1628 requiredS1628
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1628_eq] at model
  exact MomentData.excluded1628 ds ss model
def rows1629 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1629 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1629 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1629 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1629_eq : pairedProblem rows1629 cols1629 requiredD1629 requiredS1629 =
    MomentData.problem1629 := by rfl
theorem leaf1629 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1629++rows1629))
    (hc : (q.map Prod.snd).Perm (cols1629++cols1629))
    (hd : ∀ k ∈ requiredD1629, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1629, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1629 cols1629 requiredD1629 requiredS1629
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1629_eq] at model
  exact MomentData.excluded1629 ds ss model
def rows1630 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1630 : List Int := [0,6,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1630 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1630 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1630_eq : pairedProblem rows1630 cols1630 requiredD1630 requiredS1630 =
    MomentData.problem1630 := by rfl
theorem leaf1630 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1630++rows1630))
    (hc : (q.map Prod.snd).Perm (cols1630++cols1630))
    (hd : ∀ k ∈ requiredD1630, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1630, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1630 cols1630 requiredD1630 requiredS1630
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1630_eq] at model
  exact MomentData.excluded1630 ds ss model
def rows1631 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,27,28,29]
def cols1631 : List Int := [0,2,4,6,8,10,12,17,19,21,23,25,27,28,29]
def requiredD1631 : List Int := [-13,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,13]
def requiredS1631 : List Int := [16,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem1631_eq : pairedProblem rows1631 cols1631 requiredD1631 requiredS1631 =
    MomentData.problem1631 := by rfl
theorem leaf1631 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1631++rows1631))
    (hc : (q.map Prod.snd).Perm (cols1631++cols1631))
    (hd : ∀ k ∈ requiredD1631, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1631, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1631 cols1631 requiredD1631 requiredS1631
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1631_eq] at model
  exact MomentData.excluded1631 ds ss model
def rows1632 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols1632 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,23,28,29]
def requiredD1632 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1632 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1632_eq : pairedProblem rows1632 cols1632 requiredD1632 requiredS1632 =
    MomentData.problem1632 := by rfl
theorem leaf1632 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1632++rows1632))
    (hc : (q.map Prod.snd).Perm (cols1632++cols1632))
    (hd : ∀ k ∈ requiredD1632, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1632, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1632 cols1632 requiredD1632 requiredS1632
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1632_eq] at model
  exact MomentData.excluded1632 ds ss model
def rows1633 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,23,28,29]
def cols1633 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,23,28,29]
def requiredD1633 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1633 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1633_eq : pairedProblem rows1633 cols1633 requiredD1633 requiredS1633 =
    MomentData.problem1633 := by rfl
theorem leaf1633 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1633++rows1633))
    (hc : (q.map Prod.snd).Perm (cols1633++cols1633))
    (hd : ∀ k ∈ requiredD1633, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1633, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1633 cols1633 requiredD1633 requiredS1633
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1633_eq] at model
  exact MomentData.excluded1633 ds ss model
def rows1634 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1634 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1634 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1634 : List Int := [9,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1634_eq : pairedProblem rows1634 cols1634 requiredD1634 requiredS1634 =
    MomentData.problem1634 := by rfl
theorem leaf1634 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1634++rows1634))
    (hc : (q.map Prod.snd).Perm (cols1634++cols1634))
    (hd : ∀ k ∈ requiredD1634, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1634, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1634 cols1634 requiredD1634 requiredS1634
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1634_eq] at model
  exact MomentData.excluded1634 ds ss model
def rows1635 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1635 : List Int := [0,7,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1635 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1635 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1635_eq : pairedProblem rows1635 cols1635 requiredD1635 requiredS1635 =
    MomentData.problem1635 := by rfl
theorem leaf1635 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1635++rows1635))
    (hc : (q.map Prod.snd).Perm (cols1635++cols1635))
    (hd : ∀ k ∈ requiredD1635, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1635, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1635 cols1635 requiredD1635 requiredS1635
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1635_eq] at model
  exact MomentData.excluded1635 ds ss model
def rows1636 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols1636 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def requiredD1636 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1636 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1636_eq : pairedProblem rows1636 cols1636 requiredD1636 requiredS1636 =
    MomentData.problem1636 := by rfl
theorem leaf1636 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1636++rows1636))
    (hc : (q.map Prod.snd).Perm (cols1636++cols1636))
    (hd : ∀ k ∈ requiredD1636, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1636, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1636 cols1636 requiredD1636 requiredS1636
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1636_eq] at model
  exact MomentData.excluded1636 ds ss model
def rows1637 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def cols1637 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,24,28,29]
def requiredD1637 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1637 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1637_eq : pairedProblem rows1637 cols1637 requiredD1637 requiredS1637 =
    MomentData.problem1637 := by rfl
theorem leaf1637 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1637++rows1637))
    (hc : (q.map Prod.snd).Perm (cols1637++cols1637))
    (hd : ∀ k ∈ requiredD1637, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1637, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1637 cols1637 requiredD1637 requiredS1637
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1637_eq] at model
  exact MomentData.excluded1637 ds ss model
def rows1638 : List Int := [0,2,3,6,9,12,13,15,18,21,24,25,27,28,29]
def cols1638 : List Int := [0,2,3,6,9,12,13,15,18,21,24,25,27,28,29]
def requiredD1638 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1638 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1638_eq : pairedProblem rows1638 cols1638 requiredD1638 requiredS1638 =
    MomentData.problem1638 := by rfl
theorem leaf1638 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1638++rows1638))
    (hc : (q.map Prod.snd).Perm (cols1638++cols1638))
    (hd : ∀ k ∈ requiredD1638, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1638, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1638 cols1638 requiredD1638 requiredS1638
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1638_eq] at model
  exact MomentData.excluded1638 ds ss model
def rows1639 : List Int := [0,2,3,6,9,12,13,15,18,21,24,25,27,28,29]
def cols1639 : List Int := [0,2,3,6,9,12,13,15,18,21,24,25,27,28,29]
def requiredD1639 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1639 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1639_eq : pairedProblem rows1639 cols1639 requiredD1639 requiredS1639 =
    MomentData.problem1639 := by rfl
theorem leaf1639 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1639++rows1639))
    (hc : (q.map Prod.snd).Perm (cols1639++cols1639))
    (hd : ∀ k ∈ requiredD1639, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1639, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1639 cols1639 requiredD1639 requiredS1639
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1639_eq] at model
  exact MomentData.excluded1639 ds ss model
def rows1640 : List Int := [0,2,4,6,8,10,13,17,19,21,23,25,27,28,29]
def cols1640 : List Int := [0,2,4,6,8,10,13,17,19,21,23,25,27,28,29]
def requiredD1640 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1640 : List Int := [15,16,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1640_eq : pairedProblem rows1640 cols1640 requiredD1640 requiredS1640 =
    MomentData.problem1640 := by rfl
theorem leaf1640 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1640++rows1640))
    (hc : (q.map Prod.snd).Perm (cols1640++cols1640))
    (hd : ∀ k ∈ requiredD1640, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1640, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1640 cols1640 requiredD1640 requiredS1640
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1640_eq] at model
  exact MomentData.excluded1640 ds ss model
def rows1641 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1641 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def requiredD1641 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1641 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1641_eq : pairedProblem rows1641 cols1641 requiredD1641 requiredS1641 =
    MomentData.problem1641 := by rfl
theorem leaf1641 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1641++rows1641))
    (hc : (q.map Prod.snd).Perm (cols1641++cols1641))
    (hd : ∀ k ∈ requiredD1641, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1641, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1641 cols1641 requiredD1641 requiredS1641
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1641_eq] at model
  exact MomentData.excluded1641 ds ss model
def rows1642 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1642 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def requiredD1642 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1642 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1642_eq : pairedProblem rows1642 cols1642 requiredD1642 requiredS1642 =
    MomentData.problem1642 := by rfl
theorem leaf1642 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1642++rows1642))
    (hc : (q.map Prod.snd).Perm (cols1642++cols1642))
    (hd : ∀ k ∈ requiredD1642, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1642, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1642 cols1642 requiredD1642 requiredS1642
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1642_eq] at model
  exact MomentData.excluded1642 ds ss model
def rows1643 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1643 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1643 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1643 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem1643_eq : pairedProblem rows1643 cols1643 requiredD1643 requiredS1643 =
    MomentData.problem1643 := by rfl
theorem leaf1643 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1643++rows1643))
    (hc : (q.map Prod.snd).Perm (cols1643++cols1643))
    (hd : ∀ k ∈ requiredD1643, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1643, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1643 cols1643 requiredD1643 requiredS1643
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1643_eq] at model
  exact MomentData.excluded1643 ds ss model
def rows1644 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1644 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1644 : List Int := [-17,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,19]
def requiredS1644 : List Int := [10,22,23,24,25,26,27,28,29,30,31,32,33,34,46]
theorem problem1644_eq : pairedProblem rows1644 cols1644 requiredD1644 requiredS1644 =
    MomentData.problem1644 := by rfl
theorem leaf1644 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1644++rows1644))
    (hc : (q.map Prod.snd).Perm (cols1644++cols1644))
    (hd : ∀ k ∈ requiredD1644, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1644, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1644 cols1644 requiredD1644 requiredS1644
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1644_eq] at model
  exact MomentData.excluded1644 ds ss model
def rows1645 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,25,28,29]
def cols1645 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1645 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1645 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1645_eq : pairedProblem rows1645 cols1645 requiredD1645 requiredS1645 =
    MomentData.problem1645 := by rfl
theorem leaf1645 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1645++rows1645))
    (hc : (q.map Prod.snd).Perm (cols1645++cols1645))
    (hd : ∀ k ∈ requiredD1645, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1645, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1645 cols1645 requiredD1645 requiredS1645
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1645_eq] at model
  exact MomentData.excluded1645 ds ss model
def rows1646 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1646 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1646 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1646 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1646_eq : pairedProblem rows1646 cols1646 requiredD1646 requiredS1646 =
    MomentData.problem1646 := by rfl
theorem leaf1646 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1646++rows1646))
    (hc : (q.map Prod.snd).Perm (cols1646++cols1646))
    (hd : ∀ k ∈ requiredD1646, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1646, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1646 cols1646 requiredD1646 requiredS1646
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1646_eq] at model
  exact MomentData.excluded1646 ds ss model
def rows1647 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1647 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1647 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1647 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1647_eq : pairedProblem rows1647 cols1647 requiredD1647 requiredS1647 =
    MomentData.problem1647 := by rfl
theorem leaf1647 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1647++rows1647))
    (hc : (q.map Prod.snd).Perm (cols1647++cols1647))
    (hd : ∀ k ∈ requiredD1647, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1647, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1647 cols1647 requiredD1647 requiredS1647
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1647_eq] at model
  exact MomentData.excluded1647 ds ss model
def rows1648 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1648 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1648 : List Int := [-19,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,19]
def requiredS1648 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,45]
theorem problem1648_eq : pairedProblem rows1648 cols1648 requiredD1648 requiredS1648 =
    MomentData.problem1648 := by rfl
theorem leaf1648 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1648++rows1648))
    (hc : (q.map Prod.snd).Perm (cols1648++cols1648))
    (hd : ∀ k ∈ requiredD1648, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1648, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1648 cols1648 requiredD1648 requiredS1648
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1648_eq] at model
  exact MomentData.excluded1648 ds ss model
def rows1649 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1649 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1649 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1649 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1649_eq : pairedProblem rows1649 cols1649 requiredD1649 requiredS1649 =
    MomentData.problem1649 := by rfl
theorem leaf1649 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1649++rows1649))
    (hc : (q.map Prod.snd).Perm (cols1649++cols1649))
    (hd : ∀ k ∈ requiredD1649, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1649, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1649 cols1649 requiredD1649 requiredS1649
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1649_eq] at model
  exact MomentData.excluded1649 ds ss model
def rows1650 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,26,28,29]
def cols1650 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,26,28,29]
def requiredD1650 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1650 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35,47]
theorem problem1650_eq : pairedProblem rows1650 cols1650 requiredD1650 requiredS1650 =
    MomentData.problem1650 := by rfl
theorem leaf1650 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1650++rows1650))
    (hc : (q.map Prod.snd).Perm (cols1650++cols1650))
    (hd : ∀ k ∈ requiredD1650, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1650, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1650 cols1650 requiredD1650 requiredS1650
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1650_eq] at model
  exact MomentData.excluded1650 ds ss model
def rows1651 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,26,28,29]
def cols1651 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,26,28,29]
def requiredD1651 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1651 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1651_eq : pairedProblem rows1651 cols1651 requiredD1651 requiredS1651 =
    MomentData.problem1651 := by rfl
theorem leaf1651 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1651++rows1651))
    (hc : (q.map Prod.snd).Perm (cols1651++cols1651))
    (hd : ∀ k ∈ requiredD1651, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1651, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1651 cols1651 requiredD1651 requiredS1651
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1651_eq] at model
  exact MomentData.excluded1651 ds ss model
def rows1652 : List Int := [0,2,3,6,9,12,14,15,18,21,24,25,27,28,29]
def cols1652 : List Int := [0,2,3,6,9,12,14,15,18,21,24,25,27,28,29]
def requiredD1652 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1652 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1652_eq : pairedProblem rows1652 cols1652 requiredD1652 requiredS1652 =
    MomentData.problem1652 := by rfl
theorem leaf1652 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1652++rows1652))
    (hc : (q.map Prod.snd).Perm (cols1652++cols1652))
    (hd : ∀ k ∈ requiredD1652, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1652, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1652 cols1652 requiredD1652 requiredS1652
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1652_eq] at model
  exact MomentData.excluded1652 ds ss model
def rows1653 : List Int := [0,2,3,6,9,12,14,15,18,21,24,25,27,28,29]
def cols1653 : List Int := [0,2,3,6,9,12,14,15,18,21,24,25,27,28,29]
def requiredD1653 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1653 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1653_eq : pairedProblem rows1653 cols1653 requiredD1653 requiredS1653 =
    MomentData.problem1653 := by rfl
theorem leaf1653 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1653++rows1653))
    (hc : (q.map Prod.snd).Perm (cols1653++cols1653))
    (hd : ∀ k ∈ requiredD1653, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1653, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1653 cols1653 requiredD1653 requiredS1653
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1653_eq] at model
  exact MomentData.excluded1653 ds ss model
def rows1654 : List Int := [0,2,4,6,8,10,15,17,19,21,23,25,27,28,29]
def cols1654 : List Int := [0,2,4,6,8,10,15,17,19,21,23,25,27,28,29]
def requiredD1654 : List Int := [-12,-11,-10,-8,-6,-4,-2,0,2,4,6,8,10,11,12]
def requiredS1654 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,38,39]
theorem problem1654_eq : pairedProblem rows1654 cols1654 requiredD1654 requiredS1654 =
    MomentData.problem1654 := by rfl
theorem leaf1654 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1654++rows1654))
    (hc : (q.map Prod.snd).Perm (cols1654++cols1654))
    (hd : ∀ k ∈ requiredD1654, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1654, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1654 cols1654 requiredD1654 requiredS1654
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1654_eq] at model
  exact MomentData.excluded1654 ds ss model
def rows1655 : List Int := [6,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def cols1655 : List Int := [6,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def requiredD1655 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1655 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,42]
theorem problem1655_eq : pairedProblem rows1655 cols1655 requiredD1655 requiredS1655 =
    MomentData.problem1655 := by rfl
theorem leaf1655 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1655++rows1655))
    (hc : (q.map Prod.snd).Perm (cols1655++cols1655))
    (hd : ∀ k ∈ requiredD1655, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1655, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1655 cols1655 requiredD1655 requiredS1655
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1655_eq] at model
  exact MomentData.excluded1655 ds ss model
def rows1656 : List Int := [0,2,3,6,9,12,15,16,18,21,24,25,27,28,29]
def cols1656 : List Int := [0,2,3,6,9,12,15,16,18,21,24,25,27,28,29]
def requiredD1656 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1656 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1656_eq : pairedProblem rows1656 cols1656 requiredD1656 requiredS1656 =
    MomentData.problem1656 := by rfl
theorem leaf1656 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1656++rows1656))
    (hc : (q.map Prod.snd).Perm (cols1656++cols1656))
    (hd : ∀ k ∈ requiredD1656, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1656, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1656 cols1656 requiredD1656 requiredS1656
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1656_eq] at model
  exact MomentData.excluded1656 ds ss model
def rows1657 : List Int := [0,2,3,6,9,12,15,16,18,21,24,25,27,28,29]
def cols1657 : List Int := [0,2,3,6,9,12,15,16,18,21,24,25,27,28,29]
def requiredD1657 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1657 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1657_eq : pairedProblem rows1657 cols1657 requiredD1657 requiredS1657 =
    MomentData.problem1657 := by rfl
theorem leaf1657 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1657++rows1657))
    (hc : (q.map Prod.snd).Perm (cols1657++cols1657))
    (hd : ∀ k ∈ requiredD1657, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1657, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1657 cols1657 requiredD1657 requiredS1657
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1657_eq] at model
  exact MomentData.excluded1657 ds ss model
def rows1658 : List Int := [0,2,3,6,9,12,15,17,18,21,24,25,27,28,29]
def cols1658 : List Int := [0,2,3,6,9,12,15,17,18,21,24,25,27,28,29]
def requiredD1658 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1658 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1658_eq : pairedProblem rows1658 cols1658 requiredD1658 requiredS1658 =
    MomentData.problem1658 := by rfl
theorem leaf1658 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1658++rows1658))
    (hc : (q.map Prod.snd).Perm (cols1658++cols1658))
    (hd : ∀ k ∈ requiredD1658, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1658, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1658 cols1658 requiredD1658 requiredS1658
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1658_eq] at model
  exact MomentData.excluded1658 ds ss model
def rows1659 : List Int := [0,2,3,6,9,12,15,17,18,21,24,25,27,28,29]
def cols1659 : List Int := [0,2,3,6,9,12,15,17,18,21,24,25,27,28,29]
def requiredD1659 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1659 : List Int := [9,12,15,18,21,23,24,27,30,31,33,36,39,42,45]
theorem problem1659_eq : pairedProblem rows1659 cols1659 requiredD1659 requiredS1659 =
    MomentData.problem1659 := by rfl
theorem leaf1659 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1659++rows1659))
    (hc : (q.map Prod.snd).Perm (cols1659++cols1659))
    (hd : ∀ k ∈ requiredD1659, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1659, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1659 cols1659 requiredD1659 requiredS1659
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1659_eq] at model
  exact MomentData.excluded1659 ds ss model
def rows1660 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,28,29]
def cols1660 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,21,28,29]
def requiredD1660 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1660 : List Int := [12,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem1660_eq : pairedProblem rows1660 cols1660 requiredD1660 requiredS1660 =
    MomentData.problem1660 := by rfl
theorem leaf1660 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1660++rows1660))
    (hc : (q.map Prod.snd).Perm (cols1660++cols1660))
    (hd : ∀ k ∈ requiredD1660, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1660, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1660 cols1660 requiredD1660 requiredS1660
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1660_eq] at model
  exact MomentData.excluded1660 ds ss model
def rows1661 : List Int := [1,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1661 : List Int := [1,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1661 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1661 : List Int := [4,7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1661_eq : pairedProblem rows1661 cols1661 requiredD1661 requiredS1661 =
    MomentData.problem1661 := by rfl
theorem leaf1661 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1661++rows1661))
    (hc : (q.map Prod.snd).Perm (cols1661++cols1661))
    (hd : ∀ k ∈ requiredD1661, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1661, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1661 cols1661 requiredD1661 requiredS1661
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1661_eq] at model
  exact MomentData.excluded1661 ds ss model
def rows1662 : List Int := [1,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1662 : List Int := [1,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1662 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1662 : List Int := [7,10,13,16,19,21,22,25,28,29,31,34,37,40,43]
theorem problem1662_eq : pairedProblem rows1662 cols1662 requiredD1662 requiredS1662 =
    MomentData.problem1662 := by rfl
theorem leaf1662 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1662++rows1662))
    (hc : (q.map Prod.snd).Perm (cols1662++cols1662))
    (hd : ∀ k ∈ requiredD1662, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1662, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1662 cols1662 requiredD1662 requiredS1662
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1662_eq] at model
  exact MomentData.excluded1662 ds ss model
def rows1663 : List Int := [0,2,3,6,9,12,15,18,19,21,24,25,27,28,29]
def cols1663 : List Int := [0,2,3,6,9,12,15,18,19,21,24,25,27,28,29]
def requiredD1663 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1663 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1663_eq : pairedProblem rows1663 cols1663 requiredD1663 requiredS1663 =
    MomentData.problem1663 := by rfl
theorem leaf1663 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1663++rows1663))
    (hc : (q.map Prod.snd).Perm (cols1663++cols1663))
    (hd : ∀ k ∈ requiredD1663, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1663, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1663 cols1663 requiredD1663 requiredS1663
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1663_eq] at model
  exact MomentData.excluded1663 ds ss model
#print axioms leaf1536
end Gardner.Kernel.MomentContexts
