import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1408 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols1408 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD1408 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1408 : List Int := [9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem1408_eq : pairedProblem rows1408 cols1408 requiredD1408 requiredS1408 =
    MomentData.problem1408 := by rfl
theorem leaf1408 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1408++rows1408))
    (hc : (q.map Prod.snd).Perm (cols1408++cols1408))
    (hd : ∀ k ∈ requiredD1408, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1408, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1408 cols1408 requiredD1408 requiredS1408
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1408_eq] at model
  exact MomentData.excluded1408 ds ss model
def rows1409 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols1409 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD1409 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1409 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1409_eq : pairedProblem rows1409 cols1409 requiredD1409 requiredS1409 =
    MomentData.problem1409 := by rfl
theorem leaf1409 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1409++rows1409))
    (hc : (q.map Prod.snd).Perm (cols1409++cols1409))
    (hd : ∀ k ∈ requiredD1409, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1409, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1409 cols1409 requiredD1409 requiredS1409
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1409_eq] at model
  exact MomentData.excluded1409 ds ss model
def rows1410 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols1410 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD1410 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1410 : List Int := [6,9,12,15,18,21,24,27,29,30,33,36,39,42]
theorem problem1410_eq : pairedProblem rows1410 cols1410 requiredD1410 requiredS1410 =
    MomentData.problem1410 := by rfl
theorem leaf1410 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1410++rows1410))
    (hc : (q.map Prod.snd).Perm (cols1410++cols1410))
    (hd : ∀ k ∈ requiredD1410, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1410, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1410 cols1410 requiredD1410 requiredS1410
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1410_eq] at model
  exact MomentData.excluded1410 ds ss model
def rows1411 : List Int := [0,2,5,7,8,11,14,17,20,23,25,26,27,28,29]
def cols1411 : List Int := [0,2,5,7,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1411 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1411 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1411_eq : pairedProblem rows1411 cols1411 requiredD1411 requiredS1411 =
    MomentData.problem1411 := by rfl
theorem leaf1411 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1411++rows1411))
    (hc : (q.map Prod.snd).Perm (cols1411++cols1411))
    (hd : ∀ k ∈ requiredD1411, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1411, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1411 cols1411 requiredD1411 requiredS1411
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1411_eq] at model
  exact MomentData.excluded1411 ds ss model
def rows1412 : List Int := [0,1,10,11,12,13,14,15,16,17,22,26,27,28,29]
def cols1412 : List Int := [0,1,10,11,12,13,14,15,16,17,22,26,27,28,29]
def requiredD1412 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1412 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1412_eq : pairedProblem rows1412 cols1412 requiredD1412 requiredS1412 =
    MomentData.problem1412 := by rfl
theorem leaf1412 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1412++rows1412))
    (hc : (q.map Prod.snd).Perm (cols1412++cols1412))
    (hd : ∀ k ∈ requiredD1412, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1412, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1412 cols1412 requiredD1412 requiredS1412
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1412_eq] at model
  exact MomentData.excluded1412 ds ss model
def rows1413 : List Int := [0,6,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1413 : List Int := [0,6,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1413 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1413 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1413_eq : pairedProblem rows1413 cols1413 requiredD1413 requiredS1413 =
    MomentData.problem1413 := by rfl
theorem leaf1413 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1413++rows1413))
    (hc : (q.map Prod.snd).Perm (cols1413++cols1413))
    (hd : ∀ k ∈ requiredD1413, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1413, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1413 cols1413 requiredD1413 requiredS1413
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1413_eq] at model
  exact MomentData.excluded1413 ds ss model
def rows1414 : List Int := [0,6,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1414 : List Int := [0,6,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1414 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1414 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1414_eq : pairedProblem rows1414 cols1414 requiredD1414 requiredS1414 =
    MomentData.problem1414 := by rfl
theorem leaf1414 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1414++rows1414))
    (hc : (q.map Prod.snd).Perm (cols1414++cols1414))
    (hd : ∀ k ∈ requiredD1414, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1414, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1414 cols1414 requiredD1414 requiredS1414
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1414_eq] at model
  exact MomentData.excluded1414 ds ss model
def rows1415 : List Int := [0,1,10,11,12,13,14,15,16,17,23,26,27,28,29]
def cols1415 : List Int := [0,1,10,11,12,13,14,15,16,17,23,26,27,28,29]
def requiredD1415 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1415 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1415_eq : pairedProblem rows1415 cols1415 requiredD1415 requiredS1415 =
    MomentData.problem1415 := by rfl
theorem leaf1415 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1415++rows1415))
    (hc : (q.map Prod.snd).Perm (cols1415++cols1415))
    (hd : ∀ k ∈ requiredD1415, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1415, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1415 cols1415 requiredD1415 requiredS1415
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1415_eq] at model
  exact MomentData.excluded1415 ds ss model
def rows1416 : List Int := [0,7,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1416 : List Int := [0,7,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1416 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1416 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1416_eq : pairedProblem rows1416 cols1416 requiredD1416 requiredS1416 =
    MomentData.problem1416 := by rfl
theorem leaf1416 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1416++rows1416))
    (hc : (q.map Prod.snd).Perm (cols1416++cols1416))
    (hd : ∀ k ∈ requiredD1416, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1416, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1416 cols1416 requiredD1416 requiredS1416
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1416_eq] at model
  exact MomentData.excluded1416 ds ss model
def rows1417 : List Int := [0,7,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1417 : List Int := [0,7,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1417 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1417 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1417_eq : pairedProblem rows1417 cols1417 requiredD1417 requiredS1417 =
    MomentData.problem1417 := by rfl
theorem leaf1417 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1417++rows1417))
    (hc : (q.map Prod.snd).Perm (cols1417++cols1417))
    (hd : ∀ k ∈ requiredD1417, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1417, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1417 cols1417 requiredD1417 requiredS1417
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1417_eq] at model
  exact MomentData.excluded1417 ds ss model
def rows1418 : List Int := [0,2,5,8,9,11,14,17,20,23,25,26,27,28,29]
def cols1418 : List Int := [0,2,5,8,9,11,14,17,20,23,25,26,27,28,29]
def requiredD1418 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1418 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1418_eq : pairedProblem rows1418 cols1418 requiredD1418 requiredS1418 =
    MomentData.problem1418 := by rfl
theorem leaf1418 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1418++rows1418))
    (hc : (q.map Prod.snd).Perm (cols1418++cols1418))
    (hd : ∀ k ∈ requiredD1418, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1418, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1418 cols1418 requiredD1418 requiredS1418
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1418_eq] at model
  exact MomentData.excluded1418 ds ss model
def rows1419 : List Int := [0,1,10,11,12,13,14,15,16,17,24,26,27,28,29]
def cols1419 : List Int := [0,1,10,11,12,13,14,15,16,17,24,26,27,28,29]
def requiredD1419 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1419 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1419_eq : pairedProblem rows1419 cols1419 requiredD1419 requiredS1419 =
    MomentData.problem1419 := by rfl
theorem leaf1419 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1419++rows1419))
    (hc : (q.map Prod.snd).Perm (cols1419++cols1419))
    (hd : ∀ k ∈ requiredD1419, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1419, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1419 cols1419 requiredD1419 requiredS1419
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1419_eq] at model
  exact MomentData.excluded1419 ds ss model
def rows1420 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1420 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1420 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1420 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1420_eq : pairedProblem rows1420 cols1420 requiredD1420 requiredS1420 =
    MomentData.problem1420 := by rfl
theorem leaf1420 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1420++rows1420))
    (hc : (q.map Prod.snd).Perm (cols1420++cols1420))
    (hd : ∀ k ∈ requiredD1420, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1420, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1420 cols1420 requiredD1420 requiredS1420
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1420_eq] at model
  exact MomentData.excluded1420 ds ss model
def rows1421 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1421 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1421 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1421 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1421_eq : pairedProblem rows1421 cols1421 requiredD1421 requiredS1421 =
    MomentData.problem1421 := by rfl
theorem leaf1421 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1421++rows1421))
    (hc : (q.map Prod.snd).Perm (cols1421++cols1421))
    (hd : ∀ k ∈ requiredD1421, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1421, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1421 cols1421 requiredD1421 requiredS1421
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1421_eq] at model
  exact MomentData.excluded1421 ds ss model
def rows1422 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1422 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1422 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1422 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,41]
theorem problem1422_eq : pairedProblem rows1422 cols1422 requiredD1422 requiredS1422 =
    MomentData.problem1422 := by rfl
theorem leaf1422 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1422++rows1422))
    (hc : (q.map Prod.snd).Perm (cols1422++cols1422))
    (hd : ∀ k ∈ requiredD1422, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1422, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1422 cols1422 requiredD1422 requiredS1422
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1422_eq] at model
  exact MomentData.excluded1422 ds ss model
def rows1423 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1423 : List Int := [0,8,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1423 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1423 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1423_eq : pairedProblem rows1423 cols1423 requiredD1423 requiredS1423 =
    MomentData.problem1423 := by rfl
theorem leaf1423 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1423++rows1423))
    (hc : (q.map Prod.snd).Perm (cols1423++cols1423))
    (hd : ∀ k ∈ requiredD1423, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1423, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1423 cols1423 requiredD1423 requiredS1423
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1423_eq] at model
  exact MomentData.excluded1423 ds ss model
def rows1424 : List Int := [0,2,5,8,10,11,14,17,20,23,25,26,27,28,29]
def cols1424 : List Int := [0,2,5,8,10,11,14,17,20,23,25,26,27,28,29]
def requiredD1424 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1424 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1424_eq : pairedProblem rows1424 cols1424 requiredD1424 requiredS1424 =
    MomentData.problem1424 := by rfl
theorem leaf1424 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1424++rows1424))
    (hc : (q.map Prod.snd).Perm (cols1424++cols1424))
    (hd : ∀ k ∈ requiredD1424, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1424, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1424 cols1424 requiredD1424 requiredS1424
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1424_eq] at model
  exact MomentData.excluded1424 ds ss model
def rows1425 : List Int := [0,2,5,8,11,12,14,17,20,23,25,26,27,28,29]
def cols1425 : List Int := [0,2,5,8,11,12,14,17,20,23,25,26,27,28,29]
def requiredD1425 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1425 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1425_eq : pairedProblem rows1425 cols1425 requiredD1425 requiredS1425 =
    MomentData.problem1425 := by rfl
theorem leaf1425 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1425++rows1425))
    (hc : (q.map Prod.snd).Perm (cols1425++cols1425))
    (hd : ∀ k ∈ requiredD1425, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1425, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1425 cols1425 requiredD1425 requiredS1425
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1425_eq] at model
  exact MomentData.excluded1425 ds ss model
def rows1426 : List Int := [0,2,5,8,11,13,14,17,20,23,25,26,27,28,29]
def cols1426 : List Int := [0,2,5,8,11,13,14,17,20,23,25,26,27,28,29]
def requiredD1426 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1426 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1426_eq : pairedProblem rows1426 cols1426 requiredD1426 requiredS1426 =
    MomentData.problem1426 := by rfl
theorem leaf1426 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1426++rows1426))
    (hc : (q.map Prod.snd).Perm (cols1426++cols1426))
    (hd : ∀ k ∈ requiredD1426, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1426, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1426 cols1426 requiredD1426 requiredS1426
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1426_eq] at model
  exact MomentData.excluded1426 ds ss model
def rows1427 : List Int := [0,2,5,8,11,14,15,17,20,23,25,26,27,28,29]
def cols1427 : List Int := [0,2,5,8,11,14,15,17,20,23,25,26,27,28,29]
def requiredD1427 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1427 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1427_eq : pairedProblem rows1427 cols1427 requiredD1427 requiredS1427 =
    MomentData.problem1427 := by rfl
theorem leaf1427 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1427++rows1427))
    (hc : (q.map Prod.snd).Perm (cols1427++cols1427))
    (hd : ∀ k ∈ requiredD1427, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1427, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1427 cols1427 requiredD1427 requiredS1427
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1427_eq] at model
  exact MomentData.excluded1427 ds ss model
def rows1428 : List Int := [0,2,5,8,11,14,16,17,20,23,25,26,27,28,29]
def cols1428 : List Int := [0,2,5,8,11,14,16,17,20,23,25,26,27,28,29]
def requiredD1428 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1428 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1428_eq : pairedProblem rows1428 cols1428 requiredD1428 requiredS1428 =
    MomentData.problem1428 := by rfl
theorem leaf1428 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1428++rows1428))
    (hc : (q.map Prod.snd).Perm (cols1428++cols1428))
    (hd : ∀ k ∈ requiredD1428, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1428, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1428 cols1428 requiredD1428 requiredS1428
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1428_eq] at model
  exact MomentData.excluded1428 ds ss model
def rows1429 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1429 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1429 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1429 : List Int := [5,8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem1429_eq : pairedProblem rows1429 cols1429 requiredD1429 requiredS1429 =
    MomentData.problem1429 := by rfl
theorem leaf1429 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1429++rows1429))
    (hc : (q.map Prod.snd).Perm (cols1429++cols1429))
    (hd : ∀ k ∈ requiredD1429, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1429, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1429 cols1429 requiredD1429 requiredS1429
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1429_eq] at model
  exact MomentData.excluded1429 ds ss model
def rows1430 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1430 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1430 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1430 : List Int := [8,11,14,17,20,21,23,26,29,32,35,38,41,44]
theorem problem1430_eq : pairedProblem rows1430 cols1430 requiredD1430 requiredS1430 =
    MomentData.problem1430 := by rfl
theorem leaf1430 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1430++rows1430))
    (hc : (q.map Prod.snd).Perm (cols1430++cols1430))
    (hd : ∀ k ∈ requiredD1430, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1430, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1430 cols1430 requiredD1430 requiredS1430
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1430_eq] at model
  exact MomentData.excluded1430 ds ss model
def rows1431 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1431 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1431 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1431 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44]
theorem problem1431_eq : pairedProblem rows1431 cols1431 requiredD1431 requiredS1431 =
    MomentData.problem1431 := by rfl
theorem leaf1431 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1431++rows1431))
    (hc : (q.map Prod.snd).Perm (cols1431++cols1431))
    (hd : ∀ k ∈ requiredD1431, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1431, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1431 cols1431 requiredD1431 requiredS1431
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1431_eq] at model
  exact MomentData.excluded1431 ds ss model
def rows1432 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1432 : List Int := [1,2,4,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1432 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1432 : List Int := [5,8,11,14,17,20,21,23,26,29,32,35,38,41]
theorem problem1432_eq : pairedProblem rows1432 cols1432 requiredD1432 requiredS1432 =
    MomentData.problem1432 := by rfl
theorem leaf1432 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1432++rows1432))
    (hc : (q.map Prod.snd).Perm (cols1432++cols1432))
    (hd : ∀ k ∈ requiredD1432, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1432, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1432 cols1432 requiredD1432 requiredS1432
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1432_eq] at model
  exact MomentData.excluded1432 ds ss model
def rows1433 : List Int := [1,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1433 : List Int := [1,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1433 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1433 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1433_eq : pairedProblem rows1433 cols1433 requiredD1433 requiredS1433 =
    MomentData.problem1433 := by rfl
theorem leaf1433 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1433++rows1433))
    (hc : (q.map Prod.snd).Perm (cols1433++cols1433))
    (hd : ∀ k ∈ requiredD1433, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1433, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1433 cols1433 requiredD1433 requiredS1433
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1433_eq] at model
  exact MomentData.excluded1433 ds ss model
def rows1434 : List Int := [0,2,5,8,11,14,17,18,20,23,25,26,27,28,29]
def cols1434 : List Int := [0,2,5,8,11,14,17,18,20,23,25,26,27,28,29]
def requiredD1434 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1434 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1434_eq : pairedProblem rows1434 cols1434 requiredD1434 requiredS1434 =
    MomentData.problem1434 := by rfl
theorem leaf1434 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1434++rows1434))
    (hc : (q.map Prod.snd).Perm (cols1434++cols1434))
    (hd : ∀ k ∈ requiredD1434, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1434, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1434 cols1434 requiredD1434 requiredS1434
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1434_eq] at model
  exact MomentData.excluded1434 ds ss model
def rows1435 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1435 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1435 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1435 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1435_eq : pairedProblem rows1435 cols1435 requiredD1435 requiredS1435 =
    MomentData.problem1435 := by rfl
theorem leaf1435 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1435++rows1435))
    (hc : (q.map Prod.snd).Perm (cols1435++cols1435))
    (hd : ∀ k ∈ requiredD1435, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1435, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1435 cols1435 requiredD1435 requiredS1435
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1435_eq] at model
  exact MomentData.excluded1435 ds ss model
def rows1436 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1436 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1436 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1436 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1436_eq : pairedProblem rows1436 cols1436 requiredD1436 requiredS1436 =
    MomentData.problem1436 := by rfl
theorem leaf1436 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1436++rows1436))
    (hc : (q.map Prod.snd).Perm (cols1436++cols1436))
    (hd : ∀ k ∈ requiredD1436, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1436, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1436 cols1436 requiredD1436 requiredS1436
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1436_eq] at model
  exact MomentData.excluded1436 ds ss model
def rows1437 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1437 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1437 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1437 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1437_eq : pairedProblem rows1437 cols1437 requiredD1437 requiredS1437 =
    MomentData.problem1437 := by rfl
theorem leaf1437 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1437++rows1437))
    (hc : (q.map Prod.snd).Perm (cols1437++cols1437))
    (hd : ∀ k ∈ requiredD1437, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1437, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1437 cols1437 requiredD1437 requiredS1437
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1437_eq] at model
  exact MomentData.excluded1437 ds ss model
def rows1438 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def cols1438 : List Int := [0,9,10,11,12,13,14,15,16,17,25,26,27,28,29]
def requiredD1438 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1438 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1438_eq : pairedProblem rows1438 cols1438 requiredD1438 requiredS1438 =
    MomentData.problem1438 := by rfl
theorem leaf1438 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1438++rows1438))
    (hc : (q.map Prod.snd).Perm (cols1438++cols1438))
    (hd : ∀ k ∈ requiredD1438, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1438, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1438 cols1438 requiredD1438 requiredS1438
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1438_eq] at model
  exact MomentData.excluded1438 ds ss model
def rows1439 : List Int := [2,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1439 : List Int := [2,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1439 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1439 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1439_eq : pairedProblem rows1439 cols1439 requiredD1439 requiredS1439 =
    MomentData.problem1439 := by rfl
theorem leaf1439 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1439++rows1439))
    (hc : (q.map Prod.snd).Perm (cols1439++cols1439))
    (hd : ∀ k ∈ requiredD1439, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1439, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1439 cols1439 requiredD1439 requiredS1439
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1439_eq] at model
  exact MomentData.excluded1439 ds ss model
def rows1440 : List Int := [0,2,5,8,11,14,17,19,20,23,25,26,27,28,29]
def cols1440 : List Int := [0,2,5,8,11,14,17,19,20,23,25,26,27,28,29]
def requiredD1440 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1440 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1440_eq : pairedProblem rows1440 cols1440 requiredD1440 requiredS1440 =
    MomentData.problem1440 := by rfl
theorem leaf1440 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1440++rows1440))
    (hc : (q.map Prod.snd).Perm (cols1440++cols1440))
    (hd : ∀ k ∈ requiredD1440, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1440, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1440 cols1440 requiredD1440 requiredS1440
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1440_eq] at model
  exact MomentData.excluded1440 ds ss model
def rows1441 : List Int := [0,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def cols1441 : List Int := [0,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def requiredD1441 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1441 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1441_eq : pairedProblem rows1441 cols1441 requiredD1441 requiredS1441 =
    MomentData.problem1441 := by rfl
theorem leaf1441 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1441++rows1441))
    (hc : (q.map Prod.snd).Perm (cols1441++cols1441))
    (hd : ∀ k ∈ requiredD1441, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1441, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1441 cols1441 requiredD1441 requiredS1441
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1441_eq] at model
  exact MomentData.excluded1441 ds ss model
def rows1442 : List Int := [0,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def cols1442 : List Int := [0,9,10,11,12,13,14,15,16,18,25,26,27,28,29]
def requiredD1442 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1442 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1442_eq : pairedProblem rows1442 cols1442 requiredD1442 requiredS1442 =
    MomentData.problem1442 := by rfl
theorem leaf1442 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1442++rows1442))
    (hc : (q.map Prod.snd).Perm (cols1442++cols1442))
    (hd : ∀ k ∈ requiredD1442, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1442, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1442 cols1442 requiredD1442 requiredS1442
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1442_eq] at model
  exact MomentData.excluded1442 ds ss model
def rows1443 : List Int := [3,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1443 : List Int := [3,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1443 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1443 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1443_eq : pairedProblem rows1443 cols1443 requiredD1443 requiredS1443 =
    MomentData.problem1443 := by rfl
theorem leaf1443 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1443++rows1443))
    (hc : (q.map Prod.snd).Perm (cols1443++cols1443))
    (hd : ∀ k ∈ requiredD1443, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1443, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1443 cols1443 requiredD1443 requiredS1443
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1443_eq] at model
  exact MomentData.excluded1443 ds ss model
def rows1444 : List Int := [0,9,10,11,12,13,14,15,16,19,25,26,27,28,29]
def cols1444 : List Int := [0,9,10,11,12,13,14,15,16,19,25,26,27,28,29]
def requiredD1444 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1444 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1444_eq : pairedProblem rows1444 cols1444 requiredD1444 requiredS1444 =
    MomentData.problem1444 := by rfl
theorem leaf1444 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1444++rows1444))
    (hc : (q.map Prod.snd).Perm (cols1444++cols1444))
    (hd : ∀ k ∈ requiredD1444, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1444, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1444 cols1444 requiredD1444 requiredS1444
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1444_eq] at model
  exact MomentData.excluded1444 ds ss model
def rows1445 : List Int := [0,2,5,8,11,14,17,20,21,23,25,26,27,28,29]
def cols1445 : List Int := [0,2,5,8,11,14,17,20,21,23,25,26,27,28,29]
def requiredD1445 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1445 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1445_eq : pairedProblem rows1445 cols1445 requiredD1445 requiredS1445 =
    MomentData.problem1445 := by rfl
theorem leaf1445 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1445++rows1445))
    (hc : (q.map Prod.snd).Perm (cols1445++cols1445))
    (hd : ∀ k ∈ requiredD1445, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1445, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1445 cols1445 requiredD1445 requiredS1445
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1445_eq] at model
  exact MomentData.excluded1445 ds ss model
def rows1446 : List Int := [0,9,10,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1446 : List Int := [0,9,10,11,12,13,14,15,16,20,25,26,27,28,29]
def requiredD1446 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1446 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1446_eq : pairedProblem rows1446 cols1446 requiredD1446 requiredS1446 =
    MomentData.problem1446 := by rfl
theorem leaf1446 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1446++rows1446))
    (hc : (q.map Prod.snd).Perm (cols1446++cols1446))
    (hd : ∀ k ∈ requiredD1446, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1446, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1446 cols1446 requiredD1446 requiredS1446
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1446_eq] at model
  exact MomentData.excluded1446 ds ss model
def rows1447 : List Int := [0,9,10,11,12,13,14,15,16,20,25,26,27,28,29]
def cols1447 : List Int := [4,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1447 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1447 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1447_eq : pairedProblem rows1447 cols1447 requiredD1447 requiredS1447 =
    MomentData.problem1447 := by rfl
theorem leaf1447 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1447++rows1447))
    (hc : (q.map Prod.snd).Perm (cols1447++cols1447))
    (hd : ∀ k ∈ requiredD1447, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1447, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1447 cols1447 requiredD1447 requiredS1447
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1447_eq] at model
  exact MomentData.excluded1447 ds ss model
def rows1448 : List Int := [4,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1448 : List Int := [4,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1448 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1448 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1448_eq : pairedProblem rows1448 cols1448 requiredD1448 requiredS1448 =
    MomentData.problem1448 := by rfl
theorem leaf1448 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1448++rows1448))
    (hc : (q.map Prod.snd).Perm (cols1448++cols1448))
    (hd : ∀ k ∈ requiredD1448, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1448, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1448 cols1448 requiredD1448 requiredS1448
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1448_eq] at model
  exact MomentData.excluded1448 ds ss model
def rows1449 : List Int := [1,4,5,7,10,13,16,19,22,24,25,26,27,28,29]
def cols1449 : List Int := [1,4,5,7,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1449 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1449 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1449_eq : pairedProblem rows1449 cols1449 requiredD1449 requiredS1449 =
    MomentData.problem1449 := by rfl
theorem leaf1449 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1449++rows1449))
    (hc : (q.map Prod.snd).Perm (cols1449++cols1449))
    (hd : ∀ k ∈ requiredD1449, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1449, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1449 cols1449 requiredD1449 requiredS1449
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1449_eq] at model
  exact MomentData.excluded1449 ds ss model
def rows1450 : List Int := [0,2,5,8,11,14,17,20,22,23,25,26,27,28,29]
def cols1450 : List Int := [0,2,5,8,11,14,17,20,22,23,25,26,27,28,29]
def requiredD1450 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1450 : List Int := [7,10,13,16,19,22,25,27,28,31,34,37,40,43]
theorem problem1450_eq : pairedProblem rows1450 cols1450 requiredD1450 requiredS1450 =
    MomentData.problem1450 := by rfl
theorem leaf1450 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1450++rows1450))
    (hc : (q.map Prod.snd).Perm (cols1450++cols1450))
    (hd : ∀ k ∈ requiredD1450, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1450, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1450 cols1450 requiredD1450 requiredS1450
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1450_eq] at model
  exact MomentData.excluded1450 ds ss model
def rows1451 : List Int := [0,9,10,11,12,13,14,15,16,21,25,26,27,28,29]
def cols1451 : List Int := [0,9,10,11,12,13,14,15,16,21,25,26,27,28,29]
def requiredD1451 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1451 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1451_eq : pairedProblem rows1451 cols1451 requiredD1451 requiredS1451 =
    MomentData.problem1451 := by rfl
theorem leaf1451 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1451++rows1451))
    (hc : (q.map Prod.snd).Perm (cols1451++cols1451))
    (hd : ∀ k ∈ requiredD1451, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1451, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1451 cols1451 requiredD1451 requiredS1451
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1451_eq] at model
  exact MomentData.excluded1451 ds ss model
def rows1452 : List Int := [5,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1452 : List Int := [5,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1452 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1452 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1452_eq : pairedProblem rows1452 cols1452 requiredD1452 requiredS1452 =
    MomentData.problem1452 := by rfl
theorem leaf1452 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1452++rows1452))
    (hc : (q.map Prod.snd).Perm (cols1452++cols1452))
    (hd : ∀ k ∈ requiredD1452, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1452, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1452 cols1452 requiredD1452 requiredS1452
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1452_eq] at model
  exact MomentData.excluded1452 ds ss model
def rows1453 : List Int := [0,9,10,11,12,13,14,15,16,22,25,26,27,28,29]
def cols1453 : List Int := [0,9,10,11,12,13,14,15,16,22,25,26,27,28,29]
def requiredD1453 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1453 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1453_eq : pairedProblem rows1453 cols1453 requiredD1453 requiredS1453 =
    MomentData.problem1453 := by rfl
theorem leaf1453 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1453++rows1453))
    (hc : (q.map Prod.snd).Perm (cols1453++cols1453))
    (hd : ∀ k ∈ requiredD1453, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1453, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1453 cols1453 requiredD1453 requiredS1453
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1453_eq] at model
  exact MomentData.excluded1453 ds ss model
def rows1454 : List Int := [6,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1454 : List Int := [6,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1454 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1454 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1454_eq : pairedProblem rows1454 cols1454 requiredD1454 requiredS1454 =
    MomentData.problem1454 := by rfl
theorem leaf1454 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1454++rows1454))
    (hc : (q.map Prod.snd).Perm (cols1454++cols1454))
    (hd : ∀ k ∈ requiredD1454, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1454, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1454 cols1454 requiredD1454 requiredS1454
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1454_eq] at model
  exact MomentData.excluded1454 ds ss model
def rows1455 : List Int := [0,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def cols1455 : List Int := [0,9,10,11,12,13,14,15,16,23,25,26,27,28,29]
def requiredD1455 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1455 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1455_eq : pairedProblem rows1455 cols1455 requiredD1455 requiredS1455 =
    MomentData.problem1455 := by rfl
theorem leaf1455 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1455++rows1455))
    (hc : (q.map Prod.snd).Perm (cols1455++cols1455))
    (hd : ∀ k ∈ requiredD1455, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1455, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1455 cols1455 requiredD1455 requiredS1455
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1455_eq] at model
  exact MomentData.excluded1455 ds ss model
def rows1456 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1456 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1456 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1456 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem1456_eq : pairedProblem rows1456 cols1456 requiredD1456 requiredS1456 =
    MomentData.problem1456 := by rfl
theorem leaf1456 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1456++rows1456))
    (hc : (q.map Prod.snd).Perm (cols1456++cols1456))
    (hd : ∀ k ∈ requiredD1456, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1456, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1456 cols1456 requiredD1456 requiredS1456
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1456_eq] at model
  exact MomentData.excluded1456 ds ss model
def rows1457 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1457 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1457 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1457 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem1457_eq : pairedProblem rows1457 cols1457 requiredD1457 requiredS1457 =
    MomentData.problem1457 := by rfl
theorem leaf1457 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1457++rows1457))
    (hc : (q.map Prod.snd).Perm (cols1457++cols1457))
    (hd : ∀ k ∈ requiredD1457, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1457, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1457 cols1457 requiredD1457 requiredS1457
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1457_eq] at model
  exact MomentData.excluded1457 ds ss model
def rows1458 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1458 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1458 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1458 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,39]
theorem problem1458_eq : pairedProblem rows1458 cols1458 requiredD1458 requiredS1458 =
    MomentData.problem1458 := by rfl
theorem leaf1458 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1458++rows1458))
    (hc : (q.map Prod.snd).Perm (cols1458++cols1458))
    (hd : ∀ k ∈ requiredD1458, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1458, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1458 cols1458 requiredD1458 requiredS1458
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1458_eq] at model
  exact MomentData.excluded1458 ds ss model
def rows1459 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1459 : List Int := [7,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1459 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1459 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29]
theorem problem1459_eq : pairedProblem rows1459 cols1459 requiredD1459 requiredS1459 =
    MomentData.problem1459 := by rfl
theorem leaf1459 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1459++rows1459))
    (hc : (q.map Prod.snd).Perm (cols1459++cols1459))
    (hd : ∀ k ∈ requiredD1459, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1459, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1459 cols1459 requiredD1459 requiredS1459
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1459_eq] at model
  exact MomentData.excluded1459 ds ss model
def rows1460 : List Int := [1,4,7,8,10,13,16,19,22,24,25,26,27,28,29]
def cols1460 : List Int := [1,4,7,8,10,13,16,19,22,24,25,26,27,28,29]
def requiredD1460 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1460 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1460_eq : pairedProblem rows1460 cols1460 requiredD1460 requiredS1460 =
    MomentData.problem1460 := by rfl
theorem leaf1460 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1460++rows1460))
    (hc : (q.map Prod.snd).Perm (cols1460++cols1460))
    (hd : ∀ k ∈ requiredD1460, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1460, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1460 cols1460 requiredD1460 requiredS1460
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1460_eq] at model
  exact MomentData.excluded1460 ds ss model
def rows1461 : List Int := [1,4,7,10,11,13,16,19,22,24,25,26,27,28,29]
def cols1461 : List Int := [1,4,7,10,11,13,16,19,22,24,25,26,27,28,29]
def requiredD1461 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1461 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1461_eq : pairedProblem rows1461 cols1461 requiredD1461 requiredS1461 =
    MomentData.problem1461 := by rfl
theorem leaf1461 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1461++rows1461))
    (hc : (q.map Prod.snd).Perm (cols1461++cols1461))
    (hd : ∀ k ∈ requiredD1461, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1461, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1461 cols1461 requiredD1461 requiredS1461
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1461_eq] at model
  exact MomentData.excluded1461 ds ss model
def rows1462 : List Int := [1,4,7,10,13,14,16,19,22,24,25,26,27,28,29]
def cols1462 : List Int := [1,4,7,10,13,14,16,19,22,24,25,26,27,28,29]
def requiredD1462 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1462 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1462_eq : pairedProblem rows1462 cols1462 requiredD1462 requiredS1462 =
    MomentData.problem1462 := by rfl
theorem leaf1462 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1462++rows1462))
    (hc : (q.map Prod.snd).Perm (cols1462++cols1462))
    (hd : ∀ k ∈ requiredD1462, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1462, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1462 cols1462 requiredD1462 requiredS1462
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1462_eq] at model
  exact MomentData.excluded1462 ds ss model
def rows1463 : List Int := [8,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def cols1463 : List Int := [8,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def requiredD1463 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1463 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem1463_eq : pairedProblem rows1463 cols1463 requiredD1463 requiredS1463 =
    MomentData.problem1463 := by rfl
theorem leaf1463 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1463++rows1463))
    (hc : (q.map Prod.snd).Perm (cols1463++cols1463))
    (hd : ∀ k ∈ requiredD1463, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1463, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1463 cols1463 requiredD1463 requiredS1463
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1463_eq] at model
  exact MomentData.excluded1463 ds ss model
def rows1464 : List Int := [1,4,7,10,13,16,17,19,22,24,25,26,27,28,29]
def cols1464 : List Int := [1,4,7,10,13,16,17,19,22,24,25,26,27,28,29]
def requiredD1464 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1464 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1464_eq : pairedProblem rows1464 cols1464 requiredD1464 requiredS1464 =
    MomentData.problem1464 := by rfl
theorem leaf1464 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1464++rows1464))
    (hc : (q.map Prod.snd).Perm (cols1464++cols1464))
    (hd : ∀ k ∈ requiredD1464, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1464, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1464 cols1464 requiredD1464 requiredS1464
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1464_eq] at model
  exact MomentData.excluded1464 ds ss model
def rows1465 : List Int := [1,4,7,10,13,16,19,20,22,24,25,26,27,28,29]
def cols1465 : List Int := [1,4,7,10,13,16,19,20,22,24,25,26,27,28,29]
def requiredD1465 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1465 : List Int := [5,8,11,14,17,20,21,23,25,26,29,32,35,38,41]
theorem problem1465_eq : pairedProblem rows1465 cols1465 requiredD1465 requiredS1465 =
    MomentData.problem1465 := by rfl
theorem leaf1465 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1465++rows1465))
    (hc : (q.map Prod.snd).Perm (cols1465++cols1465))
    (hd : ∀ k ∈ requiredD1465, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1465, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1465 cols1465 requiredD1465 requiredS1465
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1465_eq] at model
  exact MomentData.excluded1465 ds ss model
def rows1466 : List Int := [1,4,7,10,13,16,19,21,22,24,25,26,27,28,29]
def cols1466 : List Int := [1,4,7,10,13,16,19,21,22,24,25,26,27,28,29]
def requiredD1466 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1466 : List Int := [5,8,11,14,17,20,23,25,26,29,32,35,38,41]
theorem problem1466_eq : pairedProblem rows1466 cols1466 requiredD1466 requiredS1466 =
    MomentData.problem1466 := by rfl
theorem leaf1466 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1466++rows1466))
    (hc : (q.map Prod.snd).Perm (cols1466++cols1466))
    (hd : ∀ k ∈ requiredD1466, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1466, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1466 cols1466 requiredD1466 requiredS1466
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1466_eq] at model
  exact MomentData.excluded1466 ds ss model
def rows1467 : List Int := [0,2,3,5,6,8,11,14,17,20,23,26,27,28,29]
def cols1467 : List Int := [0,2,3,5,6,8,11,14,17,20,23,26,27,28,29]
def requiredD1467 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1467 : List Int := [10,13,16,19,22,25,26,28,31,34,37,40,43,46,49]
theorem problem1467_eq : pairedProblem rows1467 cols1467 requiredD1467 requiredS1467 =
    MomentData.problem1467 := by rfl
theorem leaf1467 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1467++rows1467))
    (hc : (q.map Prod.snd).Perm (cols1467++cols1467))
    (hd : ∀ k ∈ requiredD1467, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1467, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1467 cols1467 requiredD1467 requiredS1467
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1467_eq] at model
  exact MomentData.excluded1467 ds ss model
def rows1468 : List Int := [0,1,3,4,6,9,12,15,18,21,24,25,27,28,29]
def cols1468 : List Int := [0,1,3,4,6,9,12,15,18,21,24,25,27,28,29]
def requiredD1468 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1468 : List Int := [9,12,15,18,21,24,27,28,30,33,36,39,42,45,48]
theorem problem1468_eq : pairedProblem rows1468 cols1468 requiredD1468 requiredS1468 =
    MomentData.problem1468 := by rfl
theorem leaf1468 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1468++rows1468))
    (hc : (q.map Prod.snd).Perm (cols1468++cols1468))
    (hd : ∀ k ∈ requiredD1468, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1468, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1468 cols1468 requiredD1468 requiredS1468
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1468_eq] at model
  exact MomentData.excluded1468 ds ss model
def rows1469 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def cols1469 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1469 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1469 : List Int := [9,12,15,18,21,24,26,27,30,33,36,39,42,45,48]
theorem problem1469_eq : pairedProblem rows1469 cols1469 requiredD1469 requiredS1469 =
    MomentData.problem1469 := by rfl
theorem leaf1469 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1469++rows1469))
    (hc : (q.map Prod.snd).Perm (cols1469++cols1469))
    (hd : ∀ k ∈ requiredD1469, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1469, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1469 cols1469 requiredD1469 requiredS1469
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1469_eq] at model
  exact MomentData.excluded1469 ds ss model
def rows1470 : List Int := [0,2,3,5,6,9,12,15,18,21,24,26,27,28,29]
def cols1470 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def requiredD1470 : List Int := [-22,-19,-16,-13,-10,-7,-4,-1,2,5,8,11,14,17,20]
def requiredS1470 : List Int := [10,13,16,19,22,25,27,28,31,34,37,40,43,46,49]
theorem problem1470_eq : pairedProblem rows1470 cols1470 requiredD1470 requiredS1470 =
    MomentData.problem1470 := by rfl
theorem leaf1470 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1470++rows1470))
    (hc : (q.map Prod.snd).Perm (cols1470++cols1470))
    (hd : ∀ k ∈ requiredD1470, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1470, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1470 cols1470 requiredD1470 requiredS1470
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1470_eq] at model
  exact MomentData.excluded1470 ds ss model
def rows1471 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def cols1471 : List Int := [0,1,3,4,6,7,10,13,16,19,22,25,27,28,29]
def requiredD1471 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1471 : List Int := [11,14,17,20,23,26,28,29,32,35,38,41,44,47,50]
theorem problem1471_eq : pairedProblem rows1471 cols1471 requiredD1471 requiredS1471 =
    MomentData.problem1471 := by rfl
theorem leaf1471 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1471++rows1471))
    (hc : (q.map Prod.snd).Perm (cols1471++cols1471))
    (hd : ∀ k ∈ requiredD1471, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1471, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1471 cols1471 requiredD1471 requiredS1471
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1471_eq] at model
  exact MomentData.excluded1471 ds ss model
def rows1472 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1472 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1472 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1472 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1472_eq : pairedProblem rows1472 cols1472 requiredD1472 requiredS1472 =
    MomentData.problem1472 := by rfl
theorem leaf1472 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1472++rows1472))
    (hc : (q.map Prod.snd).Perm (cols1472++cols1472))
    (hd : ∀ k ∈ requiredD1472, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1472, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1472 cols1472 requiredD1472 requiredS1472
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1472_eq] at model
  exact MomentData.excluded1472 ds ss model
def rows1473 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1473 : List Int := [0,1,4,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1473 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1473 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1473_eq : pairedProblem rows1473 cols1473 requiredD1473 requiredS1473 =
    MomentData.problem1473 := by rfl
theorem leaf1473 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1473++rows1473))
    (hc : (q.map Prod.snd).Perm (cols1473++cols1473))
    (hd : ∀ k ∈ requiredD1473, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1473, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1473 cols1473 requiredD1473 requiredS1473
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1473_eq] at model
  exact MomentData.excluded1473 ds ss model
def rows1474 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1474 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1474 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1474 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1474_eq : pairedProblem rows1474 cols1474 requiredD1474 requiredS1474 =
    MomentData.problem1474 := by rfl
theorem leaf1474 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1474++rows1474))
    (hc : (q.map Prod.snd).Perm (cols1474++cols1474))
    (hd : ∀ k ∈ requiredD1474, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1474, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1474 cols1474 requiredD1474 requiredS1474
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1474_eq] at model
  exact MomentData.excluded1474 ds ss model
def rows1475 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1475 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1475 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1475 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1475_eq : pairedProblem rows1475 cols1475 requiredD1475 requiredS1475 =
    MomentData.problem1475 := by rfl
theorem leaf1475 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1475++rows1475))
    (hc : (q.map Prod.snd).Perm (cols1475++cols1475))
    (hd : ∀ k ∈ requiredD1475, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1475, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1475 cols1475 requiredD1475 requiredS1475
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1475_eq] at model
  exact MomentData.excluded1475 ds ss model
def rows1476 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1476 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1476 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1476 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1476_eq : pairedProblem rows1476 cols1476 requiredD1476 requiredS1476 =
    MomentData.problem1476 := by rfl
theorem leaf1476 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1476++rows1476))
    (hc : (q.map Prod.snd).Perm (cols1476++cols1476))
    (hd : ∀ k ∈ requiredD1476, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1476, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1476 cols1476 requiredD1476 requiredS1476
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1476_eq] at model
  exact MomentData.excluded1476 ds ss model
def rows1477 : List Int := [0,1,5,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1477 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1477 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1477 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1477_eq : pairedProblem rows1477 cols1477 requiredD1477 requiredS1477 =
    MomentData.problem1477 := by rfl
theorem leaf1477 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1477++rows1477))
    (hc : (q.map Prod.snd).Perm (cols1477++cols1477))
    (hd : ∀ k ∈ requiredD1477, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1477, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1477 cols1477 requiredD1477 requiredS1477
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1477_eq] at model
  exact MomentData.excluded1477 ds ss model
def rows1478 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1478 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1478 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1478 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1478_eq : pairedProblem rows1478 cols1478 requiredD1478 requiredS1478 =
    MomentData.problem1478 := by rfl
theorem leaf1478 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1478++rows1478))
    (hc : (q.map Prod.snd).Perm (cols1478++cols1478))
    (hd : ∀ k ∈ requiredD1478, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1478, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1478 cols1478 requiredD1478 requiredS1478
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1478_eq] at model
  exact MomentData.excluded1478 ds ss model
def rows1479 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1479 : List Int := [0,1,3,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1479 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1479 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1479_eq : pairedProblem rows1479 cols1479 requiredD1479 requiredS1479 =
    MomentData.problem1479 := by rfl
theorem leaf1479 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1479++rows1479))
    (hc : (q.map Prod.snd).Perm (cols1479++cols1479))
    (hd : ∀ k ∈ requiredD1479, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1479, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1479 cols1479 requiredD1479 requiredS1479
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1479_eq] at model
  exact MomentData.excluded1479 ds ss model
def rows1480 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1480 : List Int := [0,1,3,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1480 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1480 : List Int := [8,11,14,17,20,23,26,28,29,32,35,38,41,44,47]
theorem problem1480_eq : pairedProblem rows1480 cols1480 requiredD1480 requiredS1480 =
    MomentData.problem1480 := by rfl
theorem leaf1480 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1480++rows1480))
    (hc : (q.map Prod.snd).Perm (cols1480++cols1480))
    (hd : ∀ k ∈ requiredD1480, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1480, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1480 cols1480 requiredD1480 requiredS1480
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1480_eq] at model
  exact MomentData.excluded1480 ds ss model
def rows1481 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1481 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1481 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1481 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1481_eq : pairedProblem rows1481 cols1481 requiredD1481 requiredS1481 =
    MomentData.problem1481 := by rfl
theorem leaf1481 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1481++rows1481))
    (hc : (q.map Prod.snd).Perm (cols1481++cols1481))
    (hd : ∀ k ∈ requiredD1481, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1481, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1481 cols1481 requiredD1481 requiredS1481
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1481_eq] at model
  exact MomentData.excluded1481 ds ss model
def rows1482 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1482 : List Int := [0,1,6,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1482 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1482 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1482_eq : pairedProblem rows1482 cols1482 requiredD1482 requiredS1482 =
    MomentData.problem1482 := by rfl
theorem leaf1482 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1482++rows1482))
    (hc : (q.map Prod.snd).Perm (cols1482++cols1482))
    (hd : ∀ k ∈ requiredD1482, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1482, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1482 cols1482 requiredD1482 requiredS1482
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1482_eq] at model
  exact MomentData.excluded1482 ds ss model
def rows1483 : List Int := [0,1,7,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1483 : List Int := [0,1,7,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1483 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1483 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1483_eq : pairedProblem rows1483 cols1483 requiredD1483 requiredS1483 =
    MomentData.problem1483 := by rfl
theorem leaf1483 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1483++rows1483))
    (hc : (q.map Prod.snd).Perm (cols1483++cols1483))
    (hd : ∀ k ∈ requiredD1483, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1483, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1483 cols1483 requiredD1483 requiredS1483
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1483_eq] at model
  exact MomentData.excluded1483 ds ss model
def rows1484 : List Int := [0,1,7,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1484 : List Int := [0,1,7,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1484 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1484 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1484_eq : pairedProblem rows1484 cols1484 requiredD1484 requiredS1484 =
    MomentData.problem1484 := by rfl
theorem leaf1484 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1484++rows1484))
    (hc : (q.map Prod.snd).Perm (cols1484++cols1484))
    (hd : ∀ k ∈ requiredD1484, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1484, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1484 cols1484 requiredD1484 requiredS1484
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1484_eq] at model
  exact MomentData.excluded1484 ds ss model
def rows1485 : List Int := [0,1,8,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1485 : List Int := [0,1,8,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1485 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1485 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1485_eq : pairedProblem rows1485 cols1485 requiredD1485 requiredS1485 =
    MomentData.problem1485 := by rfl
theorem leaf1485 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1485++rows1485))
    (hc : (q.map Prod.snd).Perm (cols1485++cols1485))
    (hd : ∀ k ∈ requiredD1485, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1485, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1485 cols1485 requiredD1485 requiredS1485
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1485_eq] at model
  exact MomentData.excluded1485 ds ss model
def rows1486 : List Int := [0,1,8,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1486 : List Int := [0,1,8,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1486 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1486 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1486_eq : pairedProblem rows1486 cols1486 requiredD1486 requiredS1486 =
    MomentData.problem1486 := by rfl
theorem leaf1486 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1486++rows1486))
    (hc : (q.map Prod.snd).Perm (cols1486++cols1486))
    (hd : ∀ k ∈ requiredD1486, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1486, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1486 cols1486 requiredD1486 requiredS1486
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1486_eq] at model
  exact MomentData.excluded1486 ds ss model
def rows1487 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1487 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1487 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1487 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1487_eq : pairedProblem rows1487 cols1487 requiredD1487 requiredS1487 =
    MomentData.problem1487 := by rfl
theorem leaf1487 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1487++rows1487))
    (hc : (q.map Prod.snd).Perm (cols1487++cols1487))
    (hd : ∀ k ∈ requiredD1487, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1487, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1487 cols1487 requiredD1487 requiredS1487
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1487_eq] at model
  exact MomentData.excluded1487 ds ss model
def rows1488 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1488 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1488 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1488 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1488_eq : pairedProblem rows1488 cols1488 requiredD1488 requiredS1488 =
    MomentData.problem1488 := by rfl
theorem leaf1488 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1488++rows1488))
    (hc : (q.map Prod.snd).Perm (cols1488++cols1488))
    (hd : ∀ k ∈ requiredD1488, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1488, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1488 cols1488 requiredD1488 requiredS1488
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1488_eq] at model
  exact MomentData.excluded1488 ds ss model
def rows1489 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1489 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1489 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1489 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,45]
theorem problem1489_eq : pairedProblem rows1489 cols1489 requiredD1489 requiredS1489 =
    MomentData.problem1489 := by rfl
theorem leaf1489 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1489++rows1489))
    (hc : (q.map Prod.snd).Perm (cols1489++cols1489))
    (hd : ∀ k ∈ requiredD1489, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1489, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1489 cols1489 requiredD1489 requiredS1489
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1489_eq] at model
  exact MomentData.excluded1489 ds ss model
def rows1490 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def cols1490 : List Int := [0,1,9,10,11,12,13,14,15,16,17,18,27,28,29]
def requiredD1490 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1490 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1490_eq : pairedProblem rows1490 cols1490 requiredD1490 requiredS1490 =
    MomentData.problem1490 := by rfl
theorem leaf1490 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1490++rows1490))
    (hc : (q.map Prod.snd).Perm (cols1490++cols1490))
    (hd : ∀ k ∈ requiredD1490, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1490, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1490 cols1490 requiredD1490 requiredS1490
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1490_eq] at model
  exact MomentData.excluded1490 ds ss model
def rows1491 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def cols1491 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def requiredD1491 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1491 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,42]
theorem problem1491_eq : pairedProblem rows1491 cols1491 requiredD1491 requiredS1491 =
    MomentData.problem1491 := by rfl
theorem leaf1491 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1491++rows1491))
    (hc : (q.map Prod.snd).Perm (cols1491++cols1491))
    (hd : ∀ k ∈ requiredD1491, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1491, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1491 cols1491 requiredD1491 requiredS1491
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1491_eq] at model
  exact MomentData.excluded1491 ds ss model
def rows1492 : List Int := [0,7,8,9,10,11,12,13,14,15,16,26,27,28,29]
def cols1492 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD1492 : List Int := [-8,-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1492 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1492_eq : pairedProblem rows1492 cols1492 requiredD1492 requiredS1492 =
    MomentData.problem1492 := by rfl
theorem leaf1492 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1492++rows1492))
    (hc : (q.map Prod.snd).Perm (cols1492++cols1492))
    (hd : ∀ k ∈ requiredD1492, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1492, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1492 cols1492 requiredD1492 requiredS1492
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1492_eq] at model
  exact MomentData.excluded1492 ds ss model
def rows1493 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def cols1493 : List Int := [0,1,8,9,10,11,12,13,14,15,16,17,27,28,29]
def requiredD1493 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1493 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,44]
theorem problem1493_eq : pairedProblem rows1493 cols1493 requiredD1493 requiredS1493 =
    MomentData.problem1493 := by rfl
theorem leaf1493 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1493++rows1493))
    (hc : (q.map Prod.snd).Perm (cols1493++cols1493))
    (hd : ∀ k ∈ requiredD1493, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1493, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1493 cols1493 requiredD1493 requiredS1493
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1493_eq] at model
  exact MomentData.excluded1493 ds ss model
def rows1494 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,27,28,29]
def cols1494 : List Int := [0,1,3,4,6,7,9,12,15,18,21,24,27,28,29]
def requiredD1494 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1494 : List Int := [12,15,18,21,24,27,28,30,33,36,39,42,45,48,51]
theorem problem1494_eq : pairedProblem rows1494 cols1494 requiredD1494 requiredS1494 =
    MomentData.problem1494 := by rfl
theorem leaf1494 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1494++rows1494))
    (hc : (q.map Prod.snd).Perm (cols1494++cols1494))
    (hd : ∀ k ∈ requiredD1494, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1494, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1494 cols1494 requiredD1494 requiredS1494
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1494_eq] at model
  exact MomentData.excluded1494 ds ss model
def rows1495 : List Int := [0,2,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1495 : List Int := [0,2,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1495 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1495 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1495_eq : pairedProblem rows1495 cols1495 requiredD1495 requiredS1495 =
    MomentData.problem1495 := by rfl
theorem leaf1495 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1495++rows1495))
    (hc : (q.map Prod.snd).Perm (cols1495++cols1495))
    (hd : ∀ k ∈ requiredD1495, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1495, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1495 cols1495 requiredD1495 requiredS1495
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1495_eq] at model
  exact MomentData.excluded1495 ds ss model
def rows1496 : List Int := [0,2,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1496 : List Int := [0,2,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1496 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1496 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1496_eq : pairedProblem rows1496 cols1496 requiredD1496 requiredS1496 =
    MomentData.problem1496 := by rfl
theorem leaf1496 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1496++rows1496))
    (hc : (q.map Prod.snd).Perm (cols1496++cols1496))
    (hd : ∀ k ∈ requiredD1496, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1496, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1496 cols1496 requiredD1496 requiredS1496
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1496_eq] at model
  exact MomentData.excluded1496 ds ss model
def rows1497 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1497 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1497 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1497 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1497_eq : pairedProblem rows1497 cols1497 requiredD1497 requiredS1497 =
    MomentData.problem1497 := by rfl
theorem leaf1497 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1497++rows1497))
    (hc : (q.map Prod.snd).Perm (cols1497++cols1497))
    (hd : ∀ k ∈ requiredD1497, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1497, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1497 cols1497 requiredD1497 requiredS1497
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1497_eq] at model
  exact MomentData.excluded1497 ds ss model
def rows1498 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1498 : List Int := [0,3,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1498 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1498 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1498_eq : pairedProblem rows1498 cols1498 requiredD1498 requiredS1498 =
    MomentData.problem1498 := by rfl
theorem leaf1498 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1498++rows1498))
    (hc : (q.map Prod.snd).Perm (cols1498++cols1498))
    (hd : ∀ k ∈ requiredD1498, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1498, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1498 cols1498 requiredD1498 requiredS1498
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1498_eq] at model
  exact MomentData.excluded1498 ds ss model
def rows1499 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1499 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1499 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1499 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1499_eq : pairedProblem rows1499 cols1499 requiredD1499 requiredS1499 =
    MomentData.problem1499 := by rfl
theorem leaf1499 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1499++rows1499))
    (hc : (q.map Prod.snd).Perm (cols1499++cols1499))
    (hd : ∀ k ∈ requiredD1499, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1499, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1499 cols1499 requiredD1499 requiredS1499
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1499_eq] at model
  exact MomentData.excluded1499 ds ss model
def rows1500 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1500 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1500 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1500 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1500_eq : pairedProblem rows1500 cols1500 requiredD1500 requiredS1500 =
    MomentData.problem1500 := by rfl
theorem leaf1500 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1500++rows1500))
    (hc : (q.map Prod.snd).Perm (cols1500++cols1500))
    (hd : ∀ k ∈ requiredD1500, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1500, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1500 cols1500 requiredD1500 requiredS1500
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1500_eq] at model
  exact MomentData.excluded1500 ds ss model
def rows1501 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1501 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1501 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1501 : List Int := [11,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1501_eq : pairedProblem rows1501 cols1501 requiredD1501 requiredS1501 =
    MomentData.problem1501 := by rfl
theorem leaf1501 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1501++rows1501))
    (hc : (q.map Prod.snd).Perm (cols1501++cols1501))
    (hd : ∀ k ∈ requiredD1501, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1501, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1501 cols1501 requiredD1501 requiredS1501
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1501_eq] at model
  exact MomentData.excluded1501 ds ss model
def rows1502 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1502 : List Int := [0,1,10,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1502 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1502 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1502_eq : pairedProblem rows1502 cols1502 requiredD1502 requiredS1502 =
    MomentData.problem1502 := by rfl
theorem leaf1502 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1502++rows1502))
    (hc : (q.map Prod.snd).Perm (cols1502++cols1502))
    (hd : ∀ k ∈ requiredD1502, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1502, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1502 cols1502 requiredD1502 requiredS1502
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1502_eq] at model
  exact MomentData.excluded1502 ds ss model
def rows1503 : List Int := [1,2,4,5,7,10,13,16,19,22,25,26,27,28,29]
def cols1503 : List Int := [1,2,4,5,7,10,13,16,19,22,25,26,27,28,29]
def requiredD1503 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1503 : List Int := [8,11,14,17,20,23,24,26,29,32,35,38,41,44,47]
theorem problem1503_eq : pairedProblem rows1503 cols1503 requiredD1503 requiredS1503 =
    MomentData.problem1503 := by rfl
theorem leaf1503 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1503++rows1503))
    (hc : (q.map Prod.snd).Perm (cols1503++cols1503))
    (hd : ∀ k ∈ requiredD1503, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1503, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1503 cols1503 requiredD1503 requiredS1503
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1503_eq] at model
  exact MomentData.excluded1503 ds ss model
def rows1504 : List Int := [0,4,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1504 : List Int := [0,4,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1504 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1504 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1504_eq : pairedProblem rows1504 cols1504 requiredD1504 requiredS1504 =
    MomentData.problem1504 := by rfl
theorem leaf1504 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1504++rows1504))
    (hc : (q.map Prod.snd).Perm (cols1504++cols1504))
    (hd : ∀ k ∈ requiredD1504, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1504, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1504 cols1504 requiredD1504 requiredS1504
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1504_eq] at model
  exact MomentData.excluded1504 ds ss model
def rows1505 : List Int := [0,4,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1505 : List Int := [0,4,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1505 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1505 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1505_eq : pairedProblem rows1505 cols1505 requiredD1505 requiredS1505 =
    MomentData.problem1505 := by rfl
theorem leaf1505 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1505++rows1505))
    (hc : (q.map Prod.snd).Perm (cols1505++cols1505))
    (hd : ∀ k ∈ requiredD1505, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1505, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1505 cols1505 requiredD1505 requiredS1505
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1505_eq] at model
  exact MomentData.excluded1505 ds ss model
def rows1506 : List Int := [0,1,10,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1506 : List Int := [0,1,10,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1506 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1506 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1506_eq : pairedProblem rows1506 cols1506 requiredD1506 requiredS1506 =
    MomentData.problem1506 := by rfl
theorem leaf1506 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1506++rows1506))
    (hc : (q.map Prod.snd).Perm (cols1506++cols1506))
    (hd : ∀ k ∈ requiredD1506, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1506, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1506 cols1506 requiredD1506 requiredS1506
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1506_eq] at model
  exact MomentData.excluded1506 ds ss model
def rows1507 : List Int := [0,1,10,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1507 : List Int := [0,1,10,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1507 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1507 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1507_eq : pairedProblem rows1507 cols1507 requiredD1507 requiredS1507 =
    MomentData.problem1507 := by rfl
theorem leaf1507 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1507++rows1507))
    (hc : (q.map Prod.snd).Perm (cols1507++cols1507))
    (hd : ∀ k ∈ requiredD1507, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1507, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1507 cols1507 requiredD1507 requiredS1507
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1507_eq] at model
  exact MomentData.excluded1507 ds ss model
def rows1508 : List Int := [0,5,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1508 : List Int := [0,5,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1508 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1508 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1508_eq : pairedProblem rows1508 cols1508 requiredD1508 requiredS1508 =
    MomentData.problem1508 := by rfl
theorem leaf1508 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1508++rows1508))
    (hc : (q.map Prod.snd).Perm (cols1508++cols1508))
    (hd : ∀ k ∈ requiredD1508, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1508, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1508 cols1508 requiredD1508 requiredS1508
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1508_eq] at model
  exact MomentData.excluded1508 ds ss model
def rows1509 : List Int := [0,5,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1509 : List Int := [0,5,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1509 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1509 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1509_eq : pairedProblem rows1509 cols1509 requiredD1509 requiredS1509 =
    MomentData.problem1509 := by rfl
theorem leaf1509 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1509++rows1509))
    (hc : (q.map Prod.snd).Perm (cols1509++cols1509))
    (hd : ∀ k ∈ requiredD1509, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1509, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1509 cols1509 requiredD1509 requiredS1509
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1509_eq] at model
  exact MomentData.excluded1509 ds ss model
def rows1510 : List Int := [0,1,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1510 : List Int := [0,1,10,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1510 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1510 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1510_eq : pairedProblem rows1510 cols1510 requiredD1510 requiredS1510 =
    MomentData.problem1510 := by rfl
theorem leaf1510 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1510++rows1510))
    (hc : (q.map Prod.snd).Perm (cols1510++cols1510))
    (hd : ∀ k ∈ requiredD1510, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1510, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1510 cols1510 requiredD1510 requiredS1510
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1510_eq] at model
  exact MomentData.excluded1510 ds ss model
def rows1511 : List Int := [0,1,10,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1511 : List Int := [0,1,10,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1511 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1511 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1511_eq : pairedProblem rows1511 cols1511 requiredD1511 requiredS1511 =
    MomentData.problem1511 := by rfl
theorem leaf1511 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1511++rows1511))
    (hc : (q.map Prod.snd).Perm (cols1511++cols1511))
    (hd : ∀ k ∈ requiredD1511, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1511, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1511 cols1511 requiredD1511 requiredS1511
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1511_eq] at model
  exact MomentData.excluded1511 ds ss model
def rows1512 : List Int := [0,1,10,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1512 : List Int := [0,1,10,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1512 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1512 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1512_eq : pairedProblem rows1512 cols1512 requiredD1512 requiredS1512 =
    MomentData.problem1512 := by rfl
theorem leaf1512 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1512++rows1512))
    (hc : (q.map Prod.snd).Perm (cols1512++cols1512))
    (hd : ∀ k ∈ requiredD1512, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1512, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1512 cols1512 requiredD1512 requiredS1512
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1512_eq] at model
  exact MomentData.excluded1512 ds ss model
def rows1513 : List Int := [0,1,10,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1513 : List Int := [0,1,10,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1513 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1513 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1513_eq : pairedProblem rows1513 cols1513 requiredD1513 requiredS1513 =
    MomentData.problem1513 := by rfl
theorem leaf1513 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1513++rows1513))
    (hc : (q.map Prod.snd).Perm (cols1513++cols1513))
    (hd : ∀ k ∈ requiredD1513, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1513, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1513 cols1513 requiredD1513 requiredS1513
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1513_eq] at model
  exact MomentData.excluded1513 ds ss model
def rows1514 : List Int := [0,6,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1514 : List Int := [0,6,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1514 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1514 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1514_eq : pairedProblem rows1514 cols1514 requiredD1514 requiredS1514 =
    MomentData.problem1514 := by rfl
theorem leaf1514 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1514++rows1514))
    (hc : (q.map Prod.snd).Perm (cols1514++cols1514))
    (hd : ∀ k ∈ requiredD1514, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1514, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1514 cols1514 requiredD1514 requiredS1514
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1514_eq] at model
  exact MomentData.excluded1514 ds ss model
def rows1515 : List Int := [0,6,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1515 : List Int := [0,6,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1515 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1515 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1515_eq : pairedProblem rows1515 cols1515 requiredD1515 requiredS1515 =
    MomentData.problem1515 := by rfl
theorem leaf1515 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1515++rows1515))
    (hc : (q.map Prod.snd).Perm (cols1515++cols1515))
    (hd : ∀ k ∈ requiredD1515, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1515, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1515 cols1515 requiredD1515 requiredS1515
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1515_eq] at model
  exact MomentData.excluded1515 ds ss model
def rows1516 : List Int := [0,1,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1516 : List Int := [0,1,10,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1516 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1516 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1516_eq : pairedProblem rows1516 cols1516 requiredD1516 requiredS1516 =
    MomentData.problem1516 := by rfl
theorem leaf1516 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1516++rows1516))
    (hc : (q.map Prod.snd).Perm (cols1516++cols1516))
    (hd : ∀ k ∈ requiredD1516, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1516, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1516 cols1516 requiredD1516 requiredS1516
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1516_eq] at model
  exact MomentData.excluded1516 ds ss model
def rows1517 : List Int := [0,1,10,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1517 : List Int := [0,1,10,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1517 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1517 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1517_eq : pairedProblem rows1517 cols1517 requiredD1517 requiredS1517 =
    MomentData.problem1517 := by rfl
theorem leaf1517 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1517++rows1517))
    (hc : (q.map Prod.snd).Perm (cols1517++cols1517))
    (hd : ∀ k ∈ requiredD1517, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1517, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1517 cols1517 requiredD1517 requiredS1517
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1517_eq] at model
  exact MomentData.excluded1517 ds ss model
def rows1518 : List Int := [0,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def cols1518 : List Int := [0,2,3,5,8,11,14,17,20,23,24,26,27,28,29]
def requiredD1518 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1518 : List Int := [7,10,13,16,19,22,25,26,28,31,34,37,40,43,46]
theorem problem1518_eq : pairedProblem rows1518 cols1518 requiredD1518 requiredS1518 =
    MomentData.problem1518 := by rfl
theorem leaf1518 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1518++rows1518))
    (hc : (q.map Prod.snd).Perm (cols1518++cols1518))
    (hd : ∀ k ∈ requiredD1518, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1518, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1518 cols1518 requiredD1518 requiredS1518
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1518_eq] at model
  exact MomentData.excluded1518 ds ss model
def rows1519 : List Int := [0,7,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1519 : List Int := [0,7,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1519 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1519 : List Int := [9,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1519_eq : pairedProblem rows1519 cols1519 requiredD1519 requiredS1519 =
    MomentData.problem1519 := by rfl
theorem leaf1519 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1519++rows1519))
    (hc : (q.map Prod.snd).Perm (cols1519++cols1519))
    (hd : ∀ k ∈ requiredD1519, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1519, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1519 cols1519 requiredD1519 requiredS1519
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1519_eq] at model
  exact MomentData.excluded1519 ds ss model
def rows1520 : List Int := [0,7,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1520 : List Int := [0,7,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1520 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1520 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1520_eq : pairedProblem rows1520 cols1520 requiredD1520 requiredS1520 =
    MomentData.problem1520 := by rfl
theorem leaf1520 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1520++rows1520))
    (hc : (q.map Prod.snd).Perm (cols1520++cols1520))
    (hd : ∀ k ∈ requiredD1520, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1520, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1520 cols1520 requiredD1520 requiredS1520
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1520_eq] at model
  exact MomentData.excluded1520 ds ss model
def rows1521 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1521 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1521 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1521 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1521_eq : pairedProblem rows1521 cols1521 requiredD1521 requiredS1521 =
    MomentData.problem1521 := by rfl
theorem leaf1521 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1521++rows1521))
    (hc : (q.map Prod.snd).Perm (cols1521++cols1521))
    (hd : ∀ k ∈ requiredD1521, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1521, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1521 cols1521 requiredD1521 requiredS1521
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1521_eq] at model
  exact MomentData.excluded1521 ds ss model
def rows1522 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1522 : List Int := [0,1,10,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1522 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1522 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1522_eq : pairedProblem rows1522 cols1522 requiredD1522 requiredS1522 =
    MomentData.problem1522 := by rfl
theorem leaf1522 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1522++rows1522))
    (hc : (q.map Prod.snd).Perm (cols1522++cols1522))
    (hd : ∀ k ∈ requiredD1522, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1522, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1522 cols1522 requiredD1522 requiredS1522
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1522_eq] at model
  exact MomentData.excluded1522 ds ss model
def rows1523 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1523 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1523 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1523 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1523_eq : pairedProblem rows1523 cols1523 requiredD1523 requiredS1523 =
    MomentData.problem1523 := by rfl
theorem leaf1523 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1523++rows1523))
    (hc : (q.map Prod.snd).Perm (cols1523++cols1523))
    (hd : ∀ k ∈ requiredD1523, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1523, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1523 cols1523 requiredD1523 requiredS1523
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1523_eq] at model
  exact MomentData.excluded1523 ds ss model
def rows1524 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1524 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1524 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1524 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1524_eq : pairedProblem rows1524 cols1524 requiredD1524 requiredS1524 =
    MomentData.problem1524 := by rfl
theorem leaf1524 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1524++rows1524))
    (hc : (q.map Prod.snd).Perm (cols1524++cols1524))
    (hd : ∀ k ∈ requiredD1524, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1524, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1524 cols1524 requiredD1524 requiredS1524
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1524_eq] at model
  exact MomentData.excluded1524 ds ss model
def rows1525 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1525 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1525 : List Int := [-18,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,18]
def requiredS1525 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,43]
theorem problem1525_eq : pairedProblem rows1525 cols1525 requiredD1525 requiredS1525 =
    MomentData.problem1525 := by rfl
theorem leaf1525 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1525++rows1525))
    (hc : (q.map Prod.snd).Perm (cols1525++cols1525))
    (hd : ∀ k ∈ requiredD1525, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1525, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1525 cols1525 requiredD1525 requiredS1525
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1525_eq] at model
  exact MomentData.excluded1525 ds ss model
def rows1526 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1526 : List Int := [0,8,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1526 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1526 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1526_eq : pairedProblem rows1526 cols1526 requiredD1526 requiredS1526 =
    MomentData.problem1526 := by rfl
theorem leaf1526 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1526++rows1526))
    (hc : (q.map Prod.snd).Perm (cols1526++cols1526))
    (hd : ∀ k ∈ requiredD1526, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1526, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1526 cols1526 requiredD1526 requiredS1526
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1526_eq] at model
  exact MomentData.excluded1526 ds ss model
def rows1527 : List Int := [0,1,10,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1527 : List Int := [0,1,10,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1527 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1527 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34,45]
theorem problem1527_eq : pairedProblem rows1527 cols1527 requiredD1527 requiredS1527 =
    MomentData.problem1527 := by rfl
theorem leaf1527 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1527++rows1527))
    (hc : (q.map Prod.snd).Perm (cols1527++cols1527))
    (hd : ∀ k ∈ requiredD1527, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1527, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1527 cols1527 requiredD1527 requiredS1527
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1527_eq] at model
  exact MomentData.excluded1527 ds ss model
def rows1528 : List Int := [0,1,10,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1528 : List Int := [0,1,10,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1528 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1528 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1528_eq : pairedProblem rows1528 cols1528 requiredD1528 requiredS1528 =
    MomentData.problem1528 := by rfl
theorem leaf1528 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1528++rows1528))
    (hc : (q.map Prod.snd).Perm (cols1528++cols1528))
    (hd : ∀ k ∈ requiredD1528, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1528, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1528 cols1528 requiredD1528 requiredS1528
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1528_eq] at model
  exact MomentData.excluded1528 ds ss model
def rows1529 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1529 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def requiredD1529 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1529 : List Int := [6,9,12,15,18,21,24,27,28,30,33,36,39,42,45]
theorem problem1529_eq : pairedProblem rows1529 cols1529 requiredD1529 requiredS1529 =
    MomentData.problem1529 := by rfl
theorem leaf1529 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1529++rows1529))
    (hc : (q.map Prod.snd).Perm (cols1529++cols1529))
    (hd : ∀ k ∈ requiredD1529, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1529, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1529 cols1529 requiredD1529 requiredS1529
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1529_eq] at model
  exact MomentData.excluded1529 ds ss model
def rows1530 : List Int := [0,1,3,6,9,12,15,18,21,22,24,25,27,28,29]
def cols1530 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1530 : List Int := [-20,-17,-14,-11,-8,-5,-2,1,2,4,7,10,13,16,19]
def requiredS1530 : List Int := [5,8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1530_eq : pairedProblem rows1530 cols1530 requiredD1530 requiredS1530 =
    MomentData.problem1530 := by rfl
theorem leaf1530 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1530++rows1530))
    (hc : (q.map Prod.snd).Perm (cols1530++cols1530))
    (hd : ∀ k ∈ requiredD1530, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1530, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1530 cols1530 requiredD1530 requiredS1530
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1530_eq] at model
  exact MomentData.excluded1530 ds ss model
def rows1531 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1531 : List Int := [1,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1531 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1531 : List Int := [7,10,13,16,19,22,24,25,28,31,34,37,40,43,46]
theorem problem1531_eq : pairedProblem rows1531 cols1531 requiredD1531 requiredS1531 =
    MomentData.problem1531 := by rfl
theorem leaf1531 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1531++rows1531))
    (hc : (q.map Prod.snd).Perm (cols1531++cols1531))
    (hd : ∀ k ∈ requiredD1531, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1531, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1531 cols1531 requiredD1531 requiredS1531
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1531_eq] at model
  exact MomentData.excluded1531 ds ss model
def rows1532 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols1532 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def requiredD1532 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1532 : List Int := [12,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1532_eq : pairedProblem rows1532 cols1532 requiredD1532 requiredS1532 =
    MomentData.problem1532 := by rfl
theorem leaf1532 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1532++rows1532))
    (hc : (q.map Prod.snd).Perm (cols1532++cols1532))
    (hd : ∀ k ∈ requiredD1532, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1532, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1532 cols1532 requiredD1532 requiredS1532
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1532_eq] at model
  exact MomentData.excluded1532 ds ss model
def rows1533 : List Int := [0,1,11,12,13,14,15,16,17,18,19,20,27,28,29]
def cols1533 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def requiredD1533 : List Int := [-14,-3,-2,-1,0,1,2,3,4,5,6,7,8,9,10]
def requiredS1533 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1533_eq : pairedProblem rows1533 cols1533 requiredD1533 requiredS1533 =
    MomentData.problem1533 := by rfl
theorem leaf1533 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1533++rows1533))
    (hc : (q.map Prod.snd).Perm (cols1533++cols1533))
    (hd : ∀ k ∈ requiredD1533, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1533, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1533 cols1533 requiredD1533 requiredS1533
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1533_eq] at model
  exact MomentData.excluded1533 ds ss model
def rows1534 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def cols1534 : List Int := [6,7,8,9,10,11,12,13,14,15,25,26,27,28,29]
def requiredD1534 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1534 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,40]
theorem problem1534_eq : pairedProblem rows1534 cols1534 requiredD1534 requiredS1534 =
    MomentData.problem1534 := by rfl
theorem leaf1534 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1534++rows1534))
    (hc : (q.map Prod.snd).Perm (cols1534++cols1534))
    (hd : ∀ k ∈ requiredD1534, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1534, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1534 cols1534 requiredD1534 requiredS1534
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1534_eq] at model
  exact MomentData.excluded1534 ds ss model
def rows1535 : List Int := [0,2,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols1535 : List Int := [0,2,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD1535 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1535 : List Int := [6,9,12,15,18,21,24,26,27,30,33,36,39,42,45]
theorem problem1535_eq : pairedProblem rows1535 cols1535 requiredD1535 requiredS1535 =
    MomentData.problem1535 := by rfl
theorem leaf1535 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1535++rows1535))
    (hc : (q.map Prod.snd).Perm (cols1535++cols1535))
    (hd : ∀ k ∈ requiredD1535, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1535, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1535 cols1535 requiredD1535 requiredS1535
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1535_eq] at model
  exact MomentData.excluded1535 ds ss model
#print axioms leaf1408
end Gardner.Kernel.MomentContexts
