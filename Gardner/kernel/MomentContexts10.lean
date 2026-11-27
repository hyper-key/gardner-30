import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1280 : List Int := [0,6,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1280 : List Int := [0,6,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1280 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1280 : List Int := [9,18,19,20,21,22,23,24,25,26,27,28,29,30,39]
theorem problem1280_eq : pairedProblem rows1280 cols1280 requiredD1280 requiredS1280 =
    MomentData.problem1280 := by rfl
theorem leaf1280 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1280++rows1280))
    (hc : (q.map Prod.snd).Perm (cols1280++cols1280))
    (hd : ∀ k ∈ requiredD1280, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1280, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1280 cols1280 requiredD1280 requiredS1280
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1280_eq] at model
  exact MomentData.excluded1280 ds ss model
def rows1281 : List Int := [0,3,6,7,9,12,15,18,21,24,25,26,27,28,29]
def cols1281 : List Int := [0,3,6,7,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1281 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1281 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1281_eq : pairedProblem rows1281 cols1281 requiredD1281 requiredS1281 =
    MomentData.problem1281 := by rfl
theorem leaf1281 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1281++rows1281))
    (hc : (q.map Prod.snd).Perm (cols1281++cols1281))
    (hd : ∀ k ∈ requiredD1281, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1281, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1281 cols1281 requiredD1281 requiredS1281
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1281_eq] at model
  exact MomentData.excluded1281 ds ss model
def rows1282 : List Int := [0,3,6,8,9,12,15,18,21,24,25,26,27,28,29]
def cols1282 : List Int := [0,3,6,8,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1282 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1282 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1282_eq : pairedProblem rows1282 cols1282 requiredD1282 requiredS1282 =
    MomentData.problem1282 := by rfl
theorem leaf1282 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1282++rows1282))
    (hc : (q.map Prod.snd).Perm (cols1282++cols1282))
    (hd : ∀ k ∈ requiredD1282, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1282, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1282 cols1282 requiredD1282 requiredS1282
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1282_eq] at model
  exact MomentData.excluded1282 ds ss model
def rows1283 : List Int := [0,3,6,8,9,12,15,18,21,24,25,26,27,28,29]
def cols1283 : List Int := [0,3,6,8,9,12,15,18,21,24,25,26,27,28,29]
def requiredD1283 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1283 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1283_eq : pairedProblem rows1283 cols1283 requiredD1283 requiredS1283 =
    MomentData.problem1283 := by rfl
theorem leaf1283 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1283++rows1283))
    (hc : (q.map Prod.snd).Perm (cols1283++cols1283))
    (hd : ∀ k ∈ requiredD1283, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1283, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1283 cols1283 requiredD1283 requiredS1283
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1283_eq] at model
  exact MomentData.excluded1283 ds ss model
def rows1284 : List Int := [0,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def cols1284 : List Int := [0,8,9,10,11,12,13,14,15,24,25,26,27,28,29]
def requiredD1284 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1284 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,39]
theorem problem1284_eq : pairedProblem rows1284 cols1284 requiredD1284 requiredS1284 =
    MomentData.problem1284 := by rfl
theorem leaf1284 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1284++rows1284))
    (hc : (q.map Prod.snd).Perm (cols1284++cols1284))
    (hd : ∀ k ∈ requiredD1284, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1284, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1284 cols1284 requiredD1284 requiredS1284
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1284_eq] at model
  exact MomentData.excluded1284 ds ss model
def rows1285 : List Int := [0,3,6,9,10,12,15,18,21,24,25,26,27,28,29]
def cols1285 : List Int := [0,3,6,9,10,12,15,18,21,24,25,26,27,28,29]
def requiredD1285 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1285 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1285_eq : pairedProblem rows1285 cols1285 requiredD1285 requiredS1285 =
    MomentData.problem1285 := by rfl
theorem leaf1285 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1285++rows1285))
    (hc : (q.map Prod.snd).Perm (cols1285++cols1285))
    (hd : ∀ k ∈ requiredD1285, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1285, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1285 cols1285 requiredD1285 requiredS1285
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1285_eq] at model
  exact MomentData.excluded1285 ds ss model
def rows1286 : List Int := [0,3,6,9,11,12,15,18,21,24,25,26,27,28,29]
def cols1286 : List Int := [0,3,6,9,11,12,15,18,21,24,25,26,27,28,29]
def requiredD1286 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1286 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1286_eq : pairedProblem rows1286 cols1286 requiredD1286 requiredS1286 =
    MomentData.problem1286 := by rfl
theorem leaf1286 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1286++rows1286))
    (hc : (q.map Prod.snd).Perm (cols1286++cols1286))
    (hd : ∀ k ∈ requiredD1286, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1286, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1286 cols1286 requiredD1286 requiredS1286
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1286_eq] at model
  exact MomentData.excluded1286 ds ss model
def rows1287 : List Int := [0,3,6,9,11,12,15,18,21,24,25,26,27,28,29]
def cols1287 : List Int := [0,3,6,9,11,12,15,18,21,24,25,26,27,28,29]
def requiredD1287 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1287 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1287_eq : pairedProblem rows1287 cols1287 requiredD1287 requiredS1287 =
    MomentData.problem1287 := by rfl
theorem leaf1287 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1287++rows1287))
    (hc : (q.map Prod.snd).Perm (cols1287++cols1287))
    (hd : ∀ k ∈ requiredD1287, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1287, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1287 cols1287 requiredD1287 requiredS1287
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1287_eq] at model
  exact MomentData.excluded1287 ds ss model
def rows1288 : List Int := [0,3,6,9,12,13,15,18,21,24,25,26,27,28,29]
def cols1288 : List Int := [0,3,6,9,12,13,15,18,21,24,25,26,27,28,29]
def requiredD1288 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1288 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1288_eq : pairedProblem rows1288 cols1288 requiredD1288 requiredS1288 =
    MomentData.problem1288 := by rfl
theorem leaf1288 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1288++rows1288))
    (hc : (q.map Prod.snd).Perm (cols1288++cols1288))
    (hd : ∀ k ∈ requiredD1288, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1288, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1288 cols1288 requiredD1288 requiredS1288
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1288_eq] at model
  exact MomentData.excluded1288 ds ss model
def rows1289 : List Int := [0,3,6,9,12,14,15,18,21,24,25,26,27,28,29]
def cols1289 : List Int := [0,3,6,9,12,14,15,18,21,24,25,26,27,28,29]
def requiredD1289 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1289 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1289_eq : pairedProblem rows1289 cols1289 requiredD1289 requiredS1289 =
    MomentData.problem1289 := by rfl
theorem leaf1289 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1289++rows1289))
    (hc : (q.map Prod.snd).Perm (cols1289++cols1289))
    (hd : ∀ k ∈ requiredD1289, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1289, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1289 cols1289 requiredD1289 requiredS1289
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1289_eq] at model
  exact MomentData.excluded1289 ds ss model
def rows1290 : List Int := [0,3,6,9,12,14,15,18,21,24,25,26,27,28,29]
def cols1290 : List Int := [0,3,6,9,12,14,15,18,21,24,25,26,27,28,29]
def requiredD1290 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1290 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1290_eq : pairedProblem rows1290 cols1290 requiredD1290 requiredS1290 =
    MomentData.problem1290 := by rfl
theorem leaf1290 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1290++rows1290))
    (hc : (q.map Prod.snd).Perm (cols1290++cols1290))
    (hd : ∀ k ∈ requiredD1290, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1290, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1290 cols1290 requiredD1290 requiredS1290
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1290_eq] at model
  exact MomentData.excluded1290 ds ss model
def rows1291 : List Int := [0,3,6,9,12,15,16,18,21,24,25,26,27,28,29]
def cols1291 : List Int := [0,3,6,9,12,15,16,18,21,24,25,26,27,28,29]
def requiredD1291 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1291 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1291_eq : pairedProblem rows1291 cols1291 requiredD1291 requiredS1291 =
    MomentData.problem1291 := by rfl
theorem leaf1291 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1291++rows1291))
    (hc : (q.map Prod.snd).Perm (cols1291++cols1291))
    (hd : ∀ k ∈ requiredD1291, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1291, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1291 cols1291 requiredD1291 requiredS1291
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1291_eq] at model
  exact MomentData.excluded1291 ds ss model
def rows1292 : List Int := [0,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def cols1292 : List Int := [0,9,10,11,12,13,14,15,16,24,25,26,27,28,29]
def requiredD1292 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1292 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1292_eq : pairedProblem rows1292 cols1292 requiredD1292 requiredS1292 =
    MomentData.problem1292 := by rfl
theorem leaf1292 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1292++rows1292))
    (hc : (q.map Prod.snd).Perm (cols1292++cols1292))
    (hd : ∀ k ∈ requiredD1292, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1292, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1292 cols1292 requiredD1292 requiredS1292
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1292_eq] at model
  exact MomentData.excluded1292 ds ss model
def rows1293 : List Int := [1,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def cols1293 : List Int := [1,2,5,8,11,14,17,20,23,24,25,26,27,28,29]
def requiredD1293 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1293 : List Int := [7,10,13,16,19,21,22,25,28,31,34,37,40,43]
theorem problem1293_eq : pairedProblem rows1293 cols1293 requiredD1293 requiredS1293 =
    MomentData.problem1293 := by rfl
theorem leaf1293 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1293++rows1293))
    (hc : (q.map Prod.snd).Perm (cols1293++cols1293))
    (hd : ∀ k ∈ requiredD1293, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1293, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1293 cols1293 requiredD1293 requiredS1293
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1293_eq] at model
  exact MomentData.excluded1293 ds ss model
def rows1294 : List Int := [0,3,6,9,12,15,17,18,21,24,25,26,27,28,29]
def cols1294 : List Int := [0,3,6,9,12,15,17,18,21,24,25,26,27,28,29]
def requiredD1294 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1294 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1294_eq : pairedProblem rows1294 cols1294 requiredD1294 requiredS1294 =
    MomentData.problem1294 := by rfl
theorem leaf1294 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1294++rows1294))
    (hc : (q.map Prod.snd).Perm (cols1294++cols1294))
    (hd : ∀ k ∈ requiredD1294, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1294, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1294 cols1294 requiredD1294 requiredS1294
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1294_eq] at model
  exact MomentData.excluded1294 ds ss model
def rows1295 : List Int := [0,3,6,9,12,15,17,18,21,24,25,26,27,28,29]
def cols1295 : List Int := [0,3,6,9,12,15,17,18,21,24,25,26,27,28,29]
def requiredD1295 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1295 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1295_eq : pairedProblem rows1295 cols1295 requiredD1295 requiredS1295 =
    MomentData.problem1295 := by rfl
theorem leaf1295 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1295++rows1295))
    (hc : (q.map Prod.snd).Perm (cols1295++cols1295))
    (hd : ∀ k ∈ requiredD1295, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1295, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1295 cols1295 requiredD1295 requiredS1295
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1295_eq] at model
  exact MomentData.excluded1295 ds ss model
def rows1296 : List Int := [0,9,10,11,12,13,14,15,18,24,25,26,27,28,29]
def cols1296 : List Int := [0,9,10,11,12,13,14,15,18,24,25,26,27,28,29]
def requiredD1296 : List Int := [-15,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,15]
def requiredS1296 : List Int := [9,18,19,20,21,22,23,24,25,26,27,28,29,30,39]
theorem problem1296_eq : pairedProblem rows1296 cols1296 requiredD1296 requiredS1296 =
    MomentData.problem1296 := by rfl
theorem leaf1296 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1296++rows1296))
    (hc : (q.map Prod.snd).Perm (cols1296++cols1296))
    (hd : ∀ k ∈ requiredD1296, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1296, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1296 cols1296 requiredD1296 requiredS1296
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1296_eq] at model
  exact MomentData.excluded1296 ds ss model
def rows1297 : List Int := [0,3,6,9,12,15,18,19,21,24,25,26,27,28,29]
def cols1297 : List Int := [0,3,6,9,12,15,18,19,21,24,25,26,27,28,29]
def requiredD1297 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1297 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1297_eq : pairedProblem rows1297 cols1297 requiredD1297 requiredS1297 =
    MomentData.problem1297 := by rfl
theorem leaf1297 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1297++rows1297))
    (hc : (q.map Prod.snd).Perm (cols1297++cols1297))
    (hd : ∀ k ∈ requiredD1297, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1297, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1297 cols1297 requiredD1297 requiredS1297
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1297_eq] at model
  exact MomentData.excluded1297 ds ss model
def rows1298 : List Int := [0,3,6,9,12,15,18,20,21,24,25,26,27,28,29]
def cols1298 : List Int := [0,3,6,9,12,15,18,20,21,24,25,26,27,28,29]
def requiredD1298 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1298 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42,45]
theorem problem1298_eq : pairedProblem rows1298 cols1298 requiredD1298 requiredS1298 =
    MomentData.problem1298 := by rfl
theorem leaf1298 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1298++rows1298))
    (hc : (q.map Prod.snd).Perm (cols1298++cols1298))
    (hd : ∀ k ∈ requiredD1298, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1298, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1298 cols1298 requiredD1298 requiredS1298
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1298_eq] at model
  exact MomentData.excluded1298 ds ss model
def rows1299 : List Int := [0,3,6,9,12,15,18,20,21,24,25,26,27,28,29]
def cols1299 : List Int := [0,3,6,9,12,15,18,20,21,24,25,26,27,28,29]
def requiredD1299 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1299 : List Int := [6,9,12,15,18,21,23,24,25,27,30,33,36,39,42]
theorem problem1299_eq : pairedProblem rows1299 cols1299 requiredD1299 requiredS1299 =
    MomentData.problem1299 := by rfl
theorem leaf1299 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1299++rows1299))
    (hc : (q.map Prod.snd).Perm (cols1299++cols1299))
    (hd : ∀ k ∈ requiredD1299, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1299, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1299 cols1299 requiredD1299 requiredS1299
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1299_eq] at model
  exact MomentData.excluded1299 ds ss model
def rows1300 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols1300 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD1300 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1300 : List Int := [3,6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem1300_eq : pairedProblem rows1300 cols1300 requiredD1300 requiredS1300 =
    MomentData.problem1300 := by rfl
theorem leaf1300 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1300++rows1300))
    (hc : (q.map Prod.snd).Perm (cols1300++cols1300))
    (hd : ∀ k ∈ requiredD1300, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1300, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1300 cols1300 requiredD1300 requiredS1300
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1300_eq] at model
  exact MomentData.excluded1300 ds ss model
def rows1301 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols1301 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD1301 : List Int := [-18,-15,-12,-9,-6,-3,-1,0,1,3,6,9,12,15,18]
def requiredS1301 : List Int := [6,9,12,15,18,21,24,25,27,30,33,36,39,42]
theorem problem1301_eq : pairedProblem rows1301 cols1301 requiredD1301 requiredS1301 =
    MomentData.problem1301 := by rfl
theorem leaf1301 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1301++rows1301))
    (hc : (q.map Prod.snd).Perm (cols1301++cols1301))
    (hd : ∀ k ∈ requiredD1301, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1301, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1301 cols1301 requiredD1301 requiredS1301
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1301_eq] at model
  exact MomentData.excluded1301 ds ss model
def rows1302 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols1302 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD1302 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1302 : List Int := [3,6,9,12,15,18,21,24,27,30,33,36,39,42]
theorem problem1302_eq : pairedProblem rows1302 cols1302 requiredD1302 requiredS1302 =
    MomentData.problem1302 := by rfl
theorem leaf1302 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1302++rows1302))
    (hc : (q.map Prod.snd).Perm (cols1302++cols1302))
    (hd : ∀ k ∈ requiredD1302, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1302, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1302 cols1302 requiredD1302 requiredS1302
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1302_eq] at model
  exact MomentData.excluded1302 ds ss model
def rows1303 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def cols1303 : List Int := [0,3,6,9,12,15,18,21,22,24,25,26,27,28,29]
def requiredD1303 : List Int := [-18,-15,-12,-9,-6,-4,-3,0,3,4,6,9,12,15,18]
def requiredS1303 : List Int := [3,6,9,12,15,18,21,24,25,27,30,33,36,39]
theorem problem1303_eq : pairedProblem rows1303 cols1303 requiredD1303 requiredS1303 =
    MomentData.problem1303 := by rfl
theorem leaf1303 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1303++rows1303))
    (hc : (q.map Prod.snd).Perm (cols1303++cols1303))
    (hd : ∀ k ∈ requiredD1303, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1303, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1303 cols1303 requiredD1303 requiredS1303
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1303_eq] at model
  exact MomentData.excluded1303 ds ss model
def rows1304 : List Int := [7,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def cols1304 : List Int := [7,8,9,10,11,12,13,14,23,24,25,26,27,28,29]
def requiredD1304 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1304 : List Int := [15,16,17,18,19,20,21,22,23,24,25,26,27,37]
theorem problem1304_eq : pairedProblem rows1304 cols1304 requiredD1304 requiredS1304 =
    MomentData.problem1304 := by rfl
theorem leaf1304 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1304++rows1304))
    (hc : (q.map Prod.snd).Perm (cols1304++cols1304))
    (hd : ∀ k ∈ requiredD1304, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1304, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1304 cols1304 requiredD1304 requiredS1304
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1304_eq] at model
  exact MomentData.excluded1304 ds ss model
def rows1305 : List Int := [0,1,2,4,6,8,10,16,19,21,23,25,27,28,29]
def cols1305 : List Int := [0,1,2,4,6,8,10,16,19,21,23,25,27,28,29]
def requiredD1305 : List Int := [-12,-10,-9,-8,-6,-4,-2,0,2,4,6,8,9,10,12]
def requiredS1305 : List Int := [17,19,20,21,23,25,27,29,31,33,35,37,38,39,41]
theorem problem1305_eq : pairedProblem rows1305 cols1305 requiredD1305 requiredS1305 =
    MomentData.problem1305 := by rfl
theorem leaf1305 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1305++rows1305))
    (hc : (q.map Prod.snd).Perm (cols1305++cols1305))
    (hd : ∀ k ∈ requiredD1305, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1305, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1305 cols1305 requiredD1305 requiredS1305
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1305_eq] at model
  exact MomentData.excluded1305 ds ss model
def rows1306 : List Int := [0,1,2,4,7,10,13,15,16,19,22,25,27,28,29]
def cols1306 : List Int := [0,1,2,4,7,10,13,15,16,19,22,25,27,28,29]
def requiredD1306 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1306 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1306_eq : pairedProblem rows1306 cols1306 requiredD1306 requiredS1306 =
    MomentData.problem1306 := by rfl
theorem leaf1306 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1306++rows1306))
    (hc : (q.map Prod.snd).Perm (cols1306++cols1306))
    (hd : ∀ k ∈ requiredD1306, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1306, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1306 cols1306 requiredD1306 requiredS1306
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1306_eq] at model
  exact MomentData.excluded1306 ds ss model
def rows1307 : List Int := [0,1,2,4,7,10,13,15,16,19,22,25,27,28,29]
def cols1307 : List Int := [0,1,2,4,7,10,13,15,16,19,22,25,27,28,29]
def requiredD1307 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1307 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1307_eq : pairedProblem rows1307 cols1307 requiredD1307 requiredS1307 =
    MomentData.problem1307 := by rfl
theorem leaf1307 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1307++rows1307))
    (hc : (q.map Prod.snd).Perm (cols1307++cols1307))
    (hd : ∀ k ∈ requiredD1307, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1307, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1307 cols1307 requiredD1307 requiredS1307
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1307_eq] at model
  exact MomentData.excluded1307 ds ss model
def rows1308 : List Int := [0,1,2,4,7,10,13,16,17,19,22,25,27,28,29]
def cols1308 : List Int := [0,1,2,4,7,10,13,16,17,19,22,25,27,28,29]
def requiredD1308 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1308 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1308_eq : pairedProblem rows1308 cols1308 requiredD1308 requiredS1308 =
    MomentData.problem1308 := by rfl
theorem leaf1308 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1308++rows1308))
    (hc : (q.map Prod.snd).Perm (cols1308++cols1308))
    (hd : ∀ k ∈ requiredD1308, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1308, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1308 cols1308 requiredD1308 requiredS1308
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1308_eq] at model
  exact MomentData.excluded1308 ds ss model
def rows1309 : List Int := [0,1,2,4,7,10,13,16,17,19,22,25,27,28,29]
def cols1309 : List Int := [0,1,2,4,7,10,13,16,17,19,22,25,27,28,29]
def requiredD1309 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1309 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1309_eq : pairedProblem rows1309 cols1309 requiredD1309 requiredS1309 =
    MomentData.problem1309 := by rfl
theorem leaf1309 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1309++rows1309))
    (hc : (q.map Prod.snd).Perm (cols1309++cols1309))
    (hd : ∀ k ∈ requiredD1309, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1309, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1309 cols1309 requiredD1309 requiredS1309
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1309_eq] at model
  exact MomentData.excluded1309 ds ss model
def rows1310 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols1310 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1310 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1310 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45,48]
theorem problem1310_eq : pairedProblem rows1310 cols1310 requiredD1310 requiredS1310 =
    MomentData.problem1310 := by rfl
theorem leaf1310 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1310++rows1310))
    (hc : (q.map Prod.snd).Perm (cols1310++cols1310))
    (hd : ∀ k ∈ requiredD1310, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1310, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1310 cols1310 requiredD1310 requiredS1310
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1310_eq] at model
  exact MomentData.excluded1310 ds ss model
def rows1311 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols1311 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1311 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1311 : List Int := [12,15,18,21,24,25,27,30,33,36,39,42,45,48]
theorem problem1311_eq : pairedProblem rows1311 cols1311 requiredD1311 requiredS1311 =
    MomentData.problem1311 := by rfl
theorem leaf1311 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1311++rows1311))
    (hc : (q.map Prod.snd).Perm (cols1311++cols1311))
    (hd : ∀ k ∈ requiredD1311, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1311, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1311 cols1311 requiredD1311 requiredS1311
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1311_eq] at model
  exact MomentData.excluded1311 ds ss model
def rows1312 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols1312 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1312 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1312 : List Int := [9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1312_eq : pairedProblem rows1312 cols1312 requiredD1312 requiredS1312 =
    MomentData.problem1312 := by rfl
theorem leaf1312 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1312++rows1312))
    (hc : (q.map Prod.snd).Perm (cols1312++cols1312))
    (hd : ∀ k ∈ requiredD1312, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1312, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1312 cols1312 requiredD1312 requiredS1312
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1312_eq] at model
  exact MomentData.excluded1312 ds ss model
def rows1313 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def cols1313 : List Int := [0,1,3,4,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1313 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1313 : List Int := [9,12,15,18,21,24,25,27,30,33,36,39,42,45]
theorem problem1313_eq : pairedProblem rows1313 cols1313 requiredD1313 requiredS1313 =
    MomentData.problem1313 := by rfl
theorem leaf1313 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1313++rows1313))
    (hc : (q.map Prod.snd).Perm (cols1313++cols1313))
    (hd : ∀ k ∈ requiredD1313, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1313, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1313 cols1313 requiredD1313 requiredS1313
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1313_eq] at model
  exact MomentData.excluded1313 ds ss model
def rows1314 : List Int := [0,1,2,4,7,10,13,16,18,19,22,25,27,28,29]
def cols1314 : List Int := [0,1,2,4,7,10,13,16,18,19,22,25,27,28,29]
def requiredD1314 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1314 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1314_eq : pairedProblem rows1314 cols1314 requiredD1314 requiredS1314 =
    MomentData.problem1314 := by rfl
theorem leaf1314 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1314++rows1314))
    (hc : (q.map Prod.snd).Perm (cols1314++cols1314))
    (hd : ∀ k ∈ requiredD1314, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1314, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1314 cols1314 requiredD1314 requiredS1314
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1314_eq] at model
  exact MomentData.excluded1314 ds ss model
def rows1315 : List Int := [0,1,2,4,7,10,13,16,18,19,22,25,27,28,29]
def cols1315 : List Int := [0,1,2,4,7,10,13,16,18,19,22,25,27,28,29]
def requiredD1315 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1315 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1315_eq : pairedProblem rows1315 cols1315 requiredD1315 requiredS1315 =
    MomentData.problem1315 := by rfl
theorem leaf1315 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1315++rows1315))
    (hc : (q.map Prod.snd).Perm (cols1315++cols1315))
    (hd : ∀ k ∈ requiredD1315, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1315, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1315 cols1315 requiredD1315 requiredS1315
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1315_eq] at model
  exact MomentData.excluded1315 ds ss model
def rows1316 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def cols1316 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def requiredD1316 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1316 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1316_eq : pairedProblem rows1316 cols1316 requiredD1316 requiredS1316 =
    MomentData.problem1316 := by rfl
theorem leaf1316 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1316++rows1316))
    (hc : (q.map Prod.snd).Perm (cols1316++cols1316))
    (hd : ∀ k ∈ requiredD1316, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1316, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1316 cols1316 requiredD1316 requiredS1316
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1316_eq] at model
  exact MomentData.excluded1316 ds ss model
def rows1317 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def cols1317 : List Int := [0,1,2,4,7,10,13,16,19,20,22,25,27,28,29]
def requiredD1317 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1317 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1317_eq : pairedProblem rows1317 cols1317 requiredD1317 requiredS1317 =
    MomentData.problem1317 := by rfl
theorem leaf1317 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1317++rows1317))
    (hc : (q.map Prod.snd).Perm (cols1317++cols1317))
    (hd : ∀ k ∈ requiredD1317, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1317, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1317 cols1317 requiredD1317 requiredS1317
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1317_eq] at model
  exact MomentData.excluded1317 ds ss model
def rows1318 : List Int := [0,1,3,5,6,9,12,15,18,21,24,26,27,28,29]
def cols1318 : List Int := [0,1,3,5,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1318 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1318 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1318_eq : pairedProblem rows1318 cols1318 requiredD1318 requiredS1318 =
    MomentData.problem1318 := by rfl
theorem leaf1318 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1318++rows1318))
    (hc : (q.map Prod.snd).Perm (cols1318++cols1318))
    (hd : ∀ k ∈ requiredD1318, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1318, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1318 cols1318 requiredD1318 requiredS1318
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1318_eq] at model
  exact MomentData.excluded1318 ds ss model
def rows1319 : List Int := [0,1,3,5,6,9,12,15,18,21,24,26,27,28,29]
def cols1319 : List Int := [0,1,3,5,6,9,12,15,18,21,24,26,27,28,29]
def requiredD1319 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1319 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1319_eq : pairedProblem rows1319 cols1319 requiredD1319 requiredS1319 =
    MomentData.problem1319 := by rfl
theorem leaf1319 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1319++rows1319))
    (hc : (q.map Prod.snd).Perm (cols1319++cols1319))
    (hd : ∀ k ∈ requiredD1319, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1319, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1319 cols1319 requiredD1319 requiredS1319
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1319_eq] at model
  exact MomentData.excluded1319 ds ss model
def rows1320 : List Int := [0,1,2,4,7,10,13,16,19,21,22,25,27,28,29]
def cols1320 : List Int := [0,1,2,4,7,10,13,16,19,21,22,25,27,28,29]
def requiredD1320 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1320 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1320_eq : pairedProblem rows1320 cols1320 requiredD1320 requiredS1320 =
    MomentData.problem1320 := by rfl
theorem leaf1320 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1320++rows1320))
    (hc : (q.map Prod.snd).Perm (cols1320++cols1320))
    (hd : ∀ k ∈ requiredD1320, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1320, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1320 cols1320 requiredD1320 requiredS1320
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1320_eq] at model
  exact MomentData.excluded1320 ds ss model
def rows1321 : List Int := [0,1,2,4,7,10,13,16,19,21,22,25,27,28,29]
def cols1321 : List Int := [0,1,2,4,7,10,13,16,19,21,22,25,27,28,29]
def requiredD1321 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1321 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1321_eq : pairedProblem rows1321 cols1321 requiredD1321 requiredS1321 =
    MomentData.problem1321 := by rfl
theorem leaf1321 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1321++rows1321))
    (hc : (q.map Prod.snd).Perm (cols1321++cols1321))
    (hd : ∀ k ∈ requiredD1321, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1321, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1321 cols1321 requiredD1321 requiredS1321
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1321_eq] at model
  exact MomentData.excluded1321 ds ss model
def rows1322 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,27,28,29]
def cols1322 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,27,28,29]
def requiredD1322 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1322 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1322_eq : pairedProblem rows1322 cols1322 requiredD1322 requiredS1322 =
    MomentData.problem1322 := by rfl
theorem leaf1322 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1322++rows1322))
    (hc : (q.map Prod.snd).Perm (cols1322++cols1322))
    (hd : ∀ k ∈ requiredD1322, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1322, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1322 cols1322 requiredD1322 requiredS1322
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1322_eq] at model
  exact MomentData.excluded1322 ds ss model
def rows1323 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,27,28,29]
def cols1323 : List Int := [0,1,2,4,7,10,13,16,19,22,23,25,27,28,29]
def requiredD1323 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1323 : List Int := [11,14,17,20,23,26,27,29,31,32,35,38,41,44,47]
theorem problem1323_eq : pairedProblem rows1323 cols1323 requiredD1323 requiredS1323 =
    MomentData.problem1323 := by rfl
theorem leaf1323 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1323++rows1323))
    (hc : (q.map Prod.snd).Perm (cols1323++cols1323))
    (hd : ∀ k ∈ requiredD1323, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1323, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1323 cols1323 requiredD1323 requiredS1323
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1323_eq] at model
  exact MomentData.excluded1323 ds ss model
def rows1324 : List Int := [0,1,3,6,7,9,12,15,18,21,24,26,27,28,29]
def cols1324 : List Int := [0,1,3,6,7,9,12,15,18,21,24,26,27,28,29]
def requiredD1324 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1324 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1324_eq : pairedProblem rows1324 cols1324 requiredD1324 requiredS1324 =
    MomentData.problem1324 := by rfl
theorem leaf1324 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1324++rows1324))
    (hc : (q.map Prod.snd).Perm (cols1324++cols1324))
    (hd : ∀ k ∈ requiredD1324, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1324, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1324 cols1324 requiredD1324 requiredS1324
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1324_eq] at model
  exact MomentData.excluded1324 ds ss model
def rows1325 : List Int := [0,1,3,6,7,9,12,15,18,21,24,26,27,28,29]
def cols1325 : List Int := [0,1,3,6,7,9,12,15,18,21,24,26,27,28,29]
def requiredD1325 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1325 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1325_eq : pairedProblem rows1325 cols1325 requiredD1325 requiredS1325 =
    MomentData.problem1325 := by rfl
theorem leaf1325 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1325++rows1325))
    (hc : (q.map Prod.snd).Perm (cols1325++cols1325))
    (hd : ∀ k ∈ requiredD1325, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1325, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1325 cols1325 requiredD1325 requiredS1325
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1325_eq] at model
  exact MomentData.excluded1325 ds ss model
def rows1326 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1326 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1326 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1326 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44,47]
theorem problem1326_eq : pairedProblem rows1326 cols1326 requiredD1326 requiredS1326 =
    MomentData.problem1326 := by rfl
theorem leaf1326 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1326++rows1326))
    (hc : (q.map Prod.snd).Perm (cols1326++cols1326))
    (hd : ∀ k ∈ requiredD1326, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1326, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1326 cols1326 requiredD1326 requiredS1326
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1326_eq] at model
  exact MomentData.excluded1326 ds ss model
def rows1327 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1327 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1327 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1327 : List Int := [11,14,17,20,23,26,29,31,32,35,38,41,44,47]
theorem problem1327_eq : pairedProblem rows1327 cols1327 requiredD1327 requiredS1327 =
    MomentData.problem1327 := by rfl
theorem leaf1327 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1327++rows1327))
    (hc : (q.map Prod.snd).Perm (cols1327++cols1327))
    (hd : ∀ k ∈ requiredD1327, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1327, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1327 cols1327 requiredD1327 requiredS1327
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1327_eq] at model
  exact MomentData.excluded1327 ds ss model
def rows1328 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1328 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1328 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1328 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem1328_eq : pairedProblem rows1328 cols1328 requiredD1328 requiredS1328 =
    MomentData.problem1328 := by rfl
theorem leaf1328 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1328++rows1328))
    (hc : (q.map Prod.snd).Perm (cols1328++cols1328))
    (hd : ∀ k ∈ requiredD1328, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1328, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1328 cols1328 requiredD1328 requiredS1328
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1328_eq] at model
  exact MomentData.excluded1328 ds ss model
def rows1329 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def cols1329 : List Int := [0,1,2,4,7,10,13,16,19,22,24,25,27,28,29]
def requiredD1329 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1329 : List Int := [8,11,14,17,20,23,26,29,31,32,35,38,41,44]
theorem problem1329_eq : pairedProblem rows1329 cols1329 requiredD1329 requiredS1329 =
    MomentData.problem1329 := by rfl
theorem leaf1329 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1329++rows1329))
    (hc : (q.map Prod.snd).Perm (cols1329++cols1329))
    (hd : ∀ k ∈ requiredD1329, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1329, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1329 cols1329 requiredD1329 requiredS1329
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1329_eq] at model
  exact MomentData.excluded1329 ds ss model
def rows1330 : List Int := [0,1,3,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1330 : List Int := [0,1,3,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1330 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1330 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1330_eq : pairedProblem rows1330 cols1330 requiredD1330 requiredS1330 =
    MomentData.problem1330 := by rfl
theorem leaf1330 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1330++rows1330))
    (hc : (q.map Prod.snd).Perm (cols1330++cols1330))
    (hd : ∀ k ∈ requiredD1330, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1330, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1330 cols1330 requiredD1330 requiredS1330
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1330_eq] at model
  exact MomentData.excluded1330 ds ss model
def rows1331 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def cols1331 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def requiredD1331 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1331 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1331_eq : pairedProblem rows1331 cols1331 requiredD1331 requiredS1331 =
    MomentData.problem1331 := by rfl
theorem leaf1331 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1331++rows1331))
    (hc : (q.map Prod.snd).Perm (cols1331++cols1331))
    (hd : ∀ k ∈ requiredD1331, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1331, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1331 cols1331 requiredD1331 requiredS1331
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1331_eq] at model
  exact MomentData.excluded1331 ds ss model
def rows1332 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def cols1332 : List Int := [0,1,3,6,8,9,12,15,18,21,24,26,27,28,29]
def requiredD1332 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1332 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1332_eq : pairedProblem rows1332 cols1332 requiredD1332 requiredS1332 =
    MomentData.problem1332 := by rfl
theorem leaf1332 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1332++rows1332))
    (hc : (q.map Prod.snd).Perm (cols1332++cols1332))
    (hd : ∀ k ∈ requiredD1332, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1332, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1332 cols1332 requiredD1332 requiredS1332
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1332_eq] at model
  exact MomentData.excluded1332 ds ss model
def rows1333 : List Int := [0,1,4,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1333 : List Int := [0,1,4,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1333 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1333 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1333_eq : pairedProblem rows1333 cols1333 requiredD1333 requiredS1333 =
    MomentData.problem1333 := by rfl
theorem leaf1333 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1333++rows1333))
    (hc : (q.map Prod.snd).Perm (cols1333++cols1333))
    (hd : ∀ k ∈ requiredD1333, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1333, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1333 cols1333 requiredD1333 requiredS1333
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1333_eq] at model
  exact MomentData.excluded1333 ds ss model
def rows1334 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1334 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1334 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1334 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1334_eq : pairedProblem rows1334 cols1334 requiredD1334 requiredS1334 =
    MomentData.problem1334 := by rfl
theorem leaf1334 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1334++rows1334))
    (hc : (q.map Prod.snd).Perm (cols1334++cols1334))
    (hd : ∀ k ∈ requiredD1334, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1334, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1334 cols1334 requiredD1334 requiredS1334
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1334_eq] at model
  exact MomentData.excluded1334 ds ss model
def rows1335 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1335 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1335 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1335 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1335_eq : pairedProblem rows1335 cols1335 requiredD1335 requiredS1335 =
    MomentData.problem1335 := by rfl
theorem leaf1335 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1335++rows1335))
    (hc : (q.map Prod.snd).Perm (cols1335++cols1335))
    (hd : ∀ k ∈ requiredD1335, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1335, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1335 cols1335 requiredD1335 requiredS1335
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1335_eq] at model
  exact MomentData.excluded1335 ds ss model
def rows1336 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1336 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1336 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1336 : List Int := [13,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1336_eq : pairedProblem rows1336 cols1336 requiredD1336 requiredS1336 =
    MomentData.problem1336 := by rfl
theorem leaf1336 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1336++rows1336))
    (hc : (q.map Prod.snd).Perm (cols1336++cols1336))
    (hd : ∀ k ∈ requiredD1336, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1336, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1336 cols1336 requiredD1336 requiredS1336
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1336_eq] at model
  exact MomentData.excluded1336 ds ss model
def rows1337 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def cols1337 : List Int := [0,1,2,11,12,13,14,15,16,17,18,19,27,28,29]
def requiredD1337 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1337 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1337_eq : pairedProblem rows1337 cols1337 requiredD1337 requiredS1337 =
    MomentData.problem1337 := by rfl
theorem leaf1337 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1337++rows1337))
    (hc : (q.map Prod.snd).Perm (cols1337++cols1337))
    (hd : ∀ k ∈ requiredD1337, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1337, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1337 cols1337 requiredD1337 requiredS1337
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1337_eq] at model
  exact MomentData.excluded1337 ds ss model
def rows1338 : List Int := [0,1,2,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1338 : List Int := [0,1,2,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1338 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1338 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1338_eq : pairedProblem rows1338 cols1338 requiredD1338 requiredS1338 =
    MomentData.problem1338 := by rfl
theorem leaf1338 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1338++rows1338))
    (hc : (q.map Prod.snd).Perm (cols1338++cols1338))
    (hd : ∀ k ∈ requiredD1338, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1338, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1338 cols1338 requiredD1338 requiredS1338
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1338_eq] at model
  exact MomentData.excluded1338 ds ss model
def rows1339 : List Int := [0,1,2,11,12,13,14,15,16,17,18,20,27,28,29]
def cols1339 : List Int := [0,1,2,11,12,13,14,15,16,17,18,20,27,28,29]
def requiredD1339 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1339 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1339_eq : pairedProblem rows1339 cols1339 requiredD1339 requiredS1339 =
    MomentData.problem1339 := by rfl
theorem leaf1339 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1339++rows1339))
    (hc : (q.map Prod.snd).Perm (cols1339++cols1339))
    (hd : ∀ k ∈ requiredD1339, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1339, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1339 cols1339 requiredD1339 requiredS1339
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1339_eq] at model
  exact MomentData.excluded1339 ds ss model
def rows1340 : List Int := [0,1,5,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1340 : List Int := [0,1,5,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1340 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1340 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1340_eq : pairedProblem rows1340 cols1340 requiredD1340 requiredS1340 =
    MomentData.problem1340 := by rfl
theorem leaf1340 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1340++rows1340))
    (hc : (q.map Prod.snd).Perm (cols1340++cols1340))
    (hd : ∀ k ∈ requiredD1340, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1340, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1340 cols1340 requiredD1340 requiredS1340
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1340_eq] at model
  exact MomentData.excluded1340 ds ss model
def rows1341 : List Int := [0,1,5,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1341 : List Int := [0,1,5,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1341 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1341 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1341_eq : pairedProblem rows1341 cols1341 requiredD1341 requiredS1341 =
    MomentData.problem1341 := by rfl
theorem leaf1341 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1341++rows1341))
    (hc : (q.map Prod.snd).Perm (cols1341++cols1341))
    (hd : ∀ k ∈ requiredD1341, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1341, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1341 cols1341 requiredD1341 requiredS1341
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1341_eq] at model
  exact MomentData.excluded1341 ds ss model
def rows1342 : List Int := [0,1,2,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1342 : List Int := [0,1,2,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1342 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1342 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1342_eq : pairedProblem rows1342 cols1342 requiredD1342 requiredS1342 =
    MomentData.problem1342 := by rfl
theorem leaf1342 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1342++rows1342))
    (hc : (q.map Prod.snd).Perm (cols1342++cols1342))
    (hd : ∀ k ∈ requiredD1342, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1342, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1342 cols1342 requiredD1342 requiredS1342
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1342_eq] at model
  exact MomentData.excluded1342 ds ss model
def rows1343 : List Int := [0,1,2,11,12,13,14,15,16,17,18,21,27,28,29]
def cols1343 : List Int := [0,1,2,11,12,13,14,15,16,17,18,21,27,28,29]
def requiredD1343 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1343 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1343_eq : pairedProblem rows1343 cols1343 requiredD1343 requiredS1343 =
    MomentData.problem1343 := by rfl
theorem leaf1343 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1343++rows1343))
    (hc : (q.map Prod.snd).Perm (cols1343++cols1343))
    (hd : ∀ k ∈ requiredD1343, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1343, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1343 cols1343 requiredD1343 requiredS1343
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1343_eq] at model
  exact MomentData.excluded1343 ds ss model
def rows1344 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1344 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1344 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1344 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1344_eq : pairedProblem rows1344 cols1344 requiredD1344 requiredS1344 =
    MomentData.problem1344 := by rfl
theorem leaf1344 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1344++rows1344))
    (hc : (q.map Prod.snd).Perm (cols1344++cols1344))
    (hd : ∀ k ∈ requiredD1344, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1344, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1344 cols1344 requiredD1344 requiredS1344
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1344_eq] at model
  exact MomentData.excluded1344 ds ss model
def rows1345 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1345 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def requiredD1345 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1345 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem1345_eq : pairedProblem rows1345 cols1345 requiredD1345 requiredS1345 =
    MomentData.problem1345 := by rfl
theorem leaf1345 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1345++rows1345))
    (hc : (q.map Prod.snd).Perm (cols1345++cols1345))
    (hd : ∀ k ∈ requiredD1345, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1345, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1345 cols1345 requiredD1345 requiredS1345
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1345_eq] at model
  exact MomentData.excluded1345 ds ss model
def rows1346 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1346 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1346 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS1346 : List Int := [12,22,23,24,25,26,27,28,29,30,31,32,33,34,44]
theorem problem1346_eq : pairedProblem rows1346 cols1346 requiredD1346 requiredS1346 =
    MomentData.problem1346 := by rfl
theorem leaf1346 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1346++rows1346))
    (hc : (q.map Prod.snd).Perm (cols1346++cols1346))
    (hd : ∀ k ∈ requiredD1346, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1346, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1346 cols1346 requiredD1346 requiredS1346
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1346_eq] at model
  exact MomentData.excluded1346 ds ss model
def rows1347 : List Int := [0,1,2,11,12,13,14,15,16,17,18,22,27,28,29]
def cols1347 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1347 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1347 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1347_eq : pairedProblem rows1347 cols1347 requiredD1347 requiredS1347 =
    MomentData.problem1347 := by rfl
theorem leaf1347 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1347++rows1347))
    (hc : (q.map Prod.snd).Perm (cols1347++cols1347))
    (hd : ∀ k ∈ requiredD1347, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1347, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1347 cols1347 requiredD1347 requiredS1347
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1347_eq] at model
  exact MomentData.excluded1347 ds ss model
def rows1348 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1348 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1348 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1348 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1348_eq : pairedProblem rows1348 cols1348 requiredD1348 requiredS1348 =
    MomentData.problem1348 := by rfl
theorem leaf1348 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1348++rows1348))
    (hc : (q.map Prod.snd).Perm (cols1348++cols1348))
    (hd : ∀ k ∈ requiredD1348, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1348, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1348 cols1348 requiredD1348 requiredS1348
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1348_eq] at model
  exact MomentData.excluded1348 ds ss model
def rows1349 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1349 : List Int := [0,1,6,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1349 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1349 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1349_eq : pairedProblem rows1349 cols1349 requiredD1349 requiredS1349 =
    MomentData.problem1349 := by rfl
theorem leaf1349 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1349++rows1349))
    (hc : (q.map Prod.snd).Perm (cols1349++cols1349))
    (hd : ∀ k ∈ requiredD1349, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1349, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1349 cols1349 requiredD1349 requiredS1349
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1349_eq] at model
  exact MomentData.excluded1349 ds ss model
def rows1350 : List Int := [0,1,3,6,9,10,12,15,18,21,24,26,27,28,29]
def cols1350 : List Int := [0,1,3,6,9,10,12,15,18,21,24,26,27,28,29]
def requiredD1350 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1350 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1350_eq : pairedProblem rows1350 cols1350 requiredD1350 requiredS1350 =
    MomentData.problem1350 := by rfl
theorem leaf1350 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1350++rows1350))
    (hc : (q.map Prod.snd).Perm (cols1350++cols1350))
    (hd : ∀ k ∈ requiredD1350, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1350, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1350 cols1350 requiredD1350 requiredS1350
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1350_eq] at model
  exact MomentData.excluded1350 ds ss model
def rows1351 : List Int := [0,1,3,6,9,10,12,15,18,21,24,26,27,28,29]
def cols1351 : List Int := [0,1,3,6,9,10,12,15,18,21,24,26,27,28,29]
def requiredD1351 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1351 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1351_eq : pairedProblem rows1351 cols1351 requiredD1351 requiredS1351 =
    MomentData.problem1351 := by rfl
theorem leaf1351 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1351++rows1351))
    (hc : (q.map Prod.snd).Perm (cols1351++cols1351))
    (hd : ∀ k ∈ requiredD1351, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1351, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1351 cols1351 requiredD1351 requiredS1351
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1351_eq] at model
  exact MomentData.excluded1351 ds ss model
def rows1352 : List Int := [0,1,2,11,12,13,14,15,16,17,18,23,27,28,29]
def cols1352 : List Int := [0,1,2,11,12,13,14,15,16,17,18,23,27,28,29]
def requiredD1352 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1352 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1352_eq : pairedProblem rows1352 cols1352 requiredD1352 requiredS1352 =
    MomentData.problem1352 := by rfl
theorem leaf1352 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1352++rows1352))
    (hc : (q.map Prod.snd).Perm (cols1352++cols1352))
    (hd : ∀ k ∈ requiredD1352, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1352, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1352 cols1352 requiredD1352 requiredS1352
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1352_eq] at model
  exact MomentData.excluded1352 ds ss model
def rows1353 : List Int := [0,1,7,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1353 : List Int := [0,1,7,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1353 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1353 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1353_eq : pairedProblem rows1353 cols1353 requiredD1353 requiredS1353 =
    MomentData.problem1353 := by rfl
theorem leaf1353 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1353++rows1353))
    (hc : (q.map Prod.snd).Perm (cols1353++cols1353))
    (hd : ∀ k ∈ requiredD1353, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1353, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1353 cols1353 requiredD1353 requiredS1353
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1353_eq] at model
  exact MomentData.excluded1353 ds ss model
def rows1354 : List Int := [0,1,7,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1354 : List Int := [0,1,7,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1354 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1354 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1354_eq : pairedProblem rows1354 cols1354 requiredD1354 requiredS1354 =
    MomentData.problem1354 := by rfl
theorem leaf1354 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1354++rows1354))
    (hc : (q.map Prod.snd).Perm (cols1354++cols1354))
    (hd : ∀ k ∈ requiredD1354, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1354, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1354 cols1354 requiredD1354 requiredS1354
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1354_eq] at model
  exact MomentData.excluded1354 ds ss model
def rows1355 : List Int := [0,1,2,11,12,13,14,15,16,17,18,24,27,28,29]
def cols1355 : List Int := [0,1,2,11,12,13,14,15,16,17,18,24,27,28,29]
def requiredD1355 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1355 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1355_eq : pairedProblem rows1355 cols1355 requiredD1355 requiredS1355 =
    MomentData.problem1355 := by rfl
theorem leaf1355 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1355++rows1355))
    (hc : (q.map Prod.snd).Perm (cols1355++cols1355))
    (hd : ∀ k ∈ requiredD1355, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1355, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1355 cols1355 requiredD1355 requiredS1355
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1355_eq] at model
  exact MomentData.excluded1355 ds ss model
def rows1356 : List Int := [0,1,3,6,9,11,12,15,18,21,24,26,27,28,29]
def cols1356 : List Int := [0,1,3,6,9,11,12,15,18,21,24,26,27,28,29]
def requiredD1356 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1356 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1356_eq : pairedProblem rows1356 cols1356 requiredD1356 requiredS1356 =
    MomentData.problem1356 := by rfl
theorem leaf1356 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1356++rows1356))
    (hc : (q.map Prod.snd).Perm (cols1356++cols1356))
    (hd : ∀ k ∈ requiredD1356, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1356, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1356 cols1356 requiredD1356 requiredS1356
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1356_eq] at model
  exact MomentData.excluded1356 ds ss model
def rows1357 : List Int := [0,1,3,6,9,11,12,15,18,21,24,26,27,28,29]
def cols1357 : List Int := [0,1,3,6,9,11,12,15,18,21,24,26,27,28,29]
def requiredD1357 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1357 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1357_eq : pairedProblem rows1357 cols1357 requiredD1357 requiredS1357 =
    MomentData.problem1357 := by rfl
theorem leaf1357 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1357++rows1357))
    (hc : (q.map Prod.snd).Perm (cols1357++cols1357))
    (hd : ∀ k ∈ requiredD1357, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1357, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1357 cols1357 requiredD1357 requiredS1357
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1357_eq] at model
  exact MomentData.excluded1357 ds ss model
def rows1358 : List Int := [0,1,3,5,7,9,12,18,20,22,24,26,27,28,29]
def cols1358 : List Int := [0,1,3,5,7,9,12,18,20,22,24,26,27,28,29]
def requiredD1358 : List Int := [-12,-10,-9,-8,-6,-4,-2,0,2,4,6,8,9,10,12]
def requiredS1358 : List Int := [15,17,18,19,21,23,25,27,29,31,33,35,36,37,39]
theorem problem1358_eq : pairedProblem rows1358 cols1358 requiredD1358 requiredS1358 =
    MomentData.problem1358 := by rfl
theorem leaf1358 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1358++rows1358))
    (hc : (q.map Prod.snd).Perm (cols1358++cols1358))
    (hd : ∀ k ∈ requiredD1358, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1358, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1358 cols1358 requiredD1358 requiredS1358
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1358_eq] at model
  exact MomentData.excluded1358 ds ss model
def rows1359 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1359 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def requiredD1359 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1359 : List Int := [13,23,24,25,26,27,28,29,30,31,32,33,34,35,45]
theorem problem1359_eq : pairedProblem rows1359 cols1359 requiredD1359 requiredS1359 =
    MomentData.problem1359 := by rfl
theorem leaf1359 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1359++rows1359))
    (hc : (q.map Prod.snd).Perm (cols1359++cols1359))
    (hd : ∀ k ∈ requiredD1359, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1359, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1359 cols1359 requiredD1359 requiredS1359
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1359_eq] at model
  exact MomentData.excluded1359 ds ss model
def rows1360 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1360 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1360 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS1360 : List Int := [12,22,23,24,25,26,27,28,29,30,31,32,33,34,44]
theorem problem1360_eq : pairedProblem rows1360 cols1360 requiredD1360 requiredS1360 =
    MomentData.problem1360 := by rfl
theorem leaf1360 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1360++rows1360))
    (hc : (q.map Prod.snd).Perm (cols1360++cols1360))
    (hd : ∀ k ∈ requiredD1360, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1360, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1360 cols1360 requiredD1360 requiredS1360
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1360_eq] at model
  exact MomentData.excluded1360 ds ss model
def rows1361 : List Int := [0,1,2,11,12,13,14,15,16,17,18,25,27,28,29]
def cols1361 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1361 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1361 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1361_eq : pairedProblem rows1361 cols1361 requiredD1361 requiredS1361 =
    MomentData.problem1361 := by rfl
theorem leaf1361 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1361++rows1361))
    (hc : (q.map Prod.snd).Perm (cols1361++cols1361))
    (hd : ∀ k ∈ requiredD1361, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1361, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1361 cols1361 requiredD1361 requiredS1361
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1361_eq] at model
  exact MomentData.excluded1361 ds ss model
def rows1362 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1362 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1362 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1362 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1362_eq : pairedProblem rows1362 cols1362 requiredD1362 requiredS1362 =
    MomentData.problem1362 := by rfl
theorem leaf1362 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1362++rows1362))
    (hc : (q.map Prod.snd).Perm (cols1362++cols1362))
    (hd : ∀ k ∈ requiredD1362, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1362, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1362 cols1362 requiredD1362 requiredS1362
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1362_eq] at model
  exact MomentData.excluded1362 ds ss model
def rows1363 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1363 : List Int := [0,1,8,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1363 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1363 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1363_eq : pairedProblem rows1363 cols1363 requiredD1363 requiredS1363 =
    MomentData.problem1363 := by rfl
theorem leaf1363 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1363++rows1363))
    (hc : (q.map Prod.snd).Perm (cols1363++cols1363))
    (hd : ∀ k ∈ requiredD1363, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1363, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1363 cols1363 requiredD1363 requiredS1363
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1363_eq] at model
  exact MomentData.excluded1363 ds ss model
def rows1364 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1364 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1364 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1364 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1364_eq : pairedProblem rows1364 cols1364 requiredD1364 requiredS1364 =
    MomentData.problem1364 := by rfl
theorem leaf1364 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1364++rows1364))
    (hc : (q.map Prod.snd).Perm (cols1364++cols1364))
    (hd : ∀ k ∈ requiredD1364, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1364, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1364 cols1364 requiredD1364 requiredS1364
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1364_eq] at model
  exact MomentData.excluded1364 ds ss model
def rows1365 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1365 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1365 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1365 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1365_eq : pairedProblem rows1365 cols1365 requiredD1365 requiredS1365 =
    MomentData.problem1365 := by rfl
theorem leaf1365 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1365++rows1365))
    (hc : (q.map Prod.snd).Perm (cols1365++cols1365))
    (hd : ∀ k ∈ requiredD1365, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1365, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1365 cols1365 requiredD1365 requiredS1365
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1365_eq] at model
  exact MomentData.excluded1365 ds ss model
def rows1366 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1366 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1366 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1366 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,43]
theorem problem1366_eq : pairedProblem rows1366 cols1366 requiredD1366 requiredS1366 =
    MomentData.problem1366 := by rfl
theorem leaf1366 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1366++rows1366))
    (hc : (q.map Prod.snd).Perm (cols1366++cols1366))
    (hd : ∀ k ∈ requiredD1366, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1366, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1366 cols1366 requiredD1366 requiredS1366
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1366_eq] at model
  exact MomentData.excluded1366 ds ss model
def rows1367 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def cols1367 : List Int := [0,1,9,10,11,12,13,14,15,16,17,26,27,28,29]
def requiredD1367 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1367 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1367_eq : pairedProblem rows1367 cols1367 requiredD1367 requiredS1367 =
    MomentData.problem1367 := by rfl
theorem leaf1367 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1367++rows1367))
    (hc : (q.map Prod.snd).Perm (cols1367++cols1367))
    (hd : ∀ k ∈ requiredD1367, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1367, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1367 cols1367 requiredD1367 requiredS1367
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1367_eq] at model
  exact MomentData.excluded1367 ds ss model
def rows1368 : List Int := [0,1,3,6,9,12,13,15,18,21,24,26,27,28,29]
def cols1368 : List Int := [0,1,3,6,9,12,13,15,18,21,24,26,27,28,29]
def requiredD1368 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1368 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1368_eq : pairedProblem rows1368 cols1368 requiredD1368 requiredS1368 =
    MomentData.problem1368 := by rfl
theorem leaf1368 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1368++rows1368))
    (hc : (q.map Prod.snd).Perm (cols1368++cols1368))
    (hd : ∀ k ∈ requiredD1368, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1368, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1368 cols1368 requiredD1368 requiredS1368
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1368_eq] at model
  exact MomentData.excluded1368 ds ss model
def rows1369 : List Int := [0,1,3,6,9,12,13,15,18,21,24,26,27,28,29]
def cols1369 : List Int := [0,1,3,6,9,12,13,15,18,21,24,26,27,28,29]
def requiredD1369 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1369 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1369_eq : pairedProblem rows1369 cols1369 requiredD1369 requiredS1369 =
    MomentData.problem1369 := by rfl
theorem leaf1369 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1369++rows1369))
    (hc : (q.map Prod.snd).Perm (cols1369++cols1369))
    (hd : ∀ k ∈ requiredD1369, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1369, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1369 cols1369 requiredD1369 requiredS1369
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1369_eq] at model
  exact MomentData.excluded1369 ds ss model
def rows1370 : List Int := [0,1,3,6,9,12,14,15,18,21,24,26,27,28,29]
def cols1370 : List Int := [0,1,3,6,9,12,14,15,18,21,24,26,27,28,29]
def requiredD1370 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1370 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1370_eq : pairedProblem rows1370 cols1370 requiredD1370 requiredS1370 =
    MomentData.problem1370 := by rfl
theorem leaf1370 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1370++rows1370))
    (hc : (q.map Prod.snd).Perm (cols1370++cols1370))
    (hd : ∀ k ∈ requiredD1370, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1370, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1370 cols1370 requiredD1370 requiredS1370
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1370_eq] at model
  exact MomentData.excluded1370 ds ss model
def rows1371 : List Int := [0,1,3,6,9,12,14,15,18,21,24,26,27,28,29]
def cols1371 : List Int := [0,1,3,6,9,12,14,15,18,21,24,26,27,28,29]
def requiredD1371 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1371 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1371_eq : pairedProblem rows1371 cols1371 requiredD1371 requiredS1371 =
    MomentData.problem1371 := by rfl
theorem leaf1371 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1371++rows1371))
    (hc : (q.map Prod.snd).Perm (cols1371++cols1371))
    (hd : ∀ k ∈ requiredD1371, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1371, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1371 cols1371 requiredD1371 requiredS1371
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1371_eq] at model
  exact MomentData.excluded1371 ds ss model
def rows1372 : List Int := [0,1,3,6,9,12,15,16,18,21,24,26,27,28,29]
def cols1372 : List Int := [0,1,3,6,9,12,15,16,18,21,24,26,27,28,29]
def requiredD1372 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1372 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1372_eq : pairedProblem rows1372 cols1372 requiredD1372 requiredS1372 =
    MomentData.problem1372 := by rfl
theorem leaf1372 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1372++rows1372))
    (hc : (q.map Prod.snd).Perm (cols1372++cols1372))
    (hd : ∀ k ∈ requiredD1372, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1372, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1372 cols1372 requiredD1372 requiredS1372
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1372_eq] at model
  exact MomentData.excluded1372 ds ss model
def rows1373 : List Int := [0,1,3,6,9,12,15,16,18,21,24,26,27,28,29]
def cols1373 : List Int := [0,1,3,6,9,12,15,16,18,21,24,26,27,28,29]
def requiredD1373 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1373 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1373_eq : pairedProblem rows1373 cols1373 requiredD1373 requiredS1373 =
    MomentData.problem1373 := by rfl
theorem leaf1373 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1373++rows1373))
    (hc : (q.map Prod.snd).Perm (cols1373++cols1373))
    (hd : ∀ k ∈ requiredD1373, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1373, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1373 cols1373 requiredD1373 requiredS1373
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1373_eq] at model
  exact MomentData.excluded1373 ds ss model
def rows1374 : List Int := [0,1,3,6,9,12,15,17,18,21,24,26,27,28,29]
def cols1374 : List Int := [0,1,3,6,9,12,15,17,18,21,24,26,27,28,29]
def requiredD1374 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1374 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1374_eq : pairedProblem rows1374 cols1374 requiredD1374 requiredS1374 =
    MomentData.problem1374 := by rfl
theorem leaf1374 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1374++rows1374))
    (hc : (q.map Prod.snd).Perm (cols1374++cols1374))
    (hd : ∀ k ∈ requiredD1374, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1374, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1374 cols1374 requiredD1374 requiredS1374
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1374_eq] at model
  exact MomentData.excluded1374 ds ss model
def rows1375 : List Int := [0,1,3,6,9,12,15,17,18,21,24,26,27,28,29]
def cols1375 : List Int := [0,1,3,6,9,12,15,17,18,21,24,26,27,28,29]
def requiredD1375 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1375 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1375_eq : pairedProblem rows1375 cols1375 requiredD1375 requiredS1375 =
    MomentData.problem1375 := by rfl
theorem leaf1375 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1375++rows1375))
    (hc : (q.map Prod.snd).Perm (cols1375++cols1375))
    (hd : ∀ k ∈ requiredD1375, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1375, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1375 cols1375 requiredD1375 requiredS1375
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1375_eq] at model
  exact MomentData.excluded1375 ds ss model
def rows1376 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1376 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1376 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1376 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem1376_eq : pairedProblem rows1376 cols1376 requiredD1376 requiredS1376 =
    MomentData.problem1376 := by rfl
theorem leaf1376 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1376++rows1376))
    (hc : (q.map Prod.snd).Perm (cols1376++cols1376))
    (hd : ∀ k ∈ requiredD1376, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1376, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1376 cols1376 requiredD1376 requiredS1376
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1376_eq] at model
  exact MomentData.excluded1376 ds ss model
def rows1377 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1377 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1377 : List Int := [-18,-15,-12,-9,-6,-5,-3,0,3,5,6,9,12,15,18]
def requiredS1377 : List Int := [10,13,16,19,22,23,25,28,31,34,37,40,43,46]
theorem problem1377_eq : pairedProblem rows1377 cols1377 requiredD1377 requiredS1377 =
    MomentData.problem1377 := by rfl
theorem leaf1377 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1377++rows1377))
    (hc : (q.map Prod.snd).Perm (cols1377++cols1377))
    (hd : ∀ k ∈ requiredD1377, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1377, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1377 cols1377 requiredD1377 requiredS1377
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1377_eq] at model
  exact MomentData.excluded1377 ds ss model
def rows1378 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1378 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1378 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1378 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1378_eq : pairedProblem rows1378 cols1378 requiredD1378 requiredS1378 =
    MomentData.problem1378 := by rfl
theorem leaf1378 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1378++rows1378))
    (hc : (q.map Prod.snd).Perm (cols1378++cols1378))
    (hd : ∀ k ∈ requiredD1378, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1378, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1378 cols1378 requiredD1378 requiredS1378
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1378_eq] at model
  exact MomentData.excluded1378 ds ss model
def rows1379 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1379 : List Int := [0,2,3,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1379 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1379 : List Int := [7,10,13,16,19,22,23,25,28,31,34,37,40,43]
theorem problem1379_eq : pairedProblem rows1379 cols1379 requiredD1379 requiredS1379 =
    MomentData.problem1379 := by rfl
theorem leaf1379 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1379++rows1379))
    (hc : (q.map Prod.snd).Perm (cols1379++cols1379))
    (hd : ∀ k ∈ requiredD1379, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1379, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1379 cols1379 requiredD1379 requiredS1379
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1379_eq] at model
  exact MomentData.excluded1379 ds ss model
def rows1380 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def cols1380 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def requiredD1380 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1380 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1380_eq : pairedProblem rows1380 cols1380 requiredD1380 requiredS1380 =
    MomentData.problem1380 := by rfl
theorem leaf1380 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1380++rows1380))
    (hc : (q.map Prod.snd).Perm (cols1380++cols1380))
    (hd : ∀ k ∈ requiredD1380, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1380, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1380 cols1380 requiredD1380 requiredS1380
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1380_eq] at model
  exact MomentData.excluded1380 ds ss model
def rows1381 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def cols1381 : List Int := [0,1,3,6,9,12,15,18,19,21,24,26,27,28,29]
def requiredD1381 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1381 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1381_eq : pairedProblem rows1381 cols1381 requiredD1381 requiredS1381 =
    MomentData.problem1381 := by rfl
theorem leaf1381 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1381++rows1381))
    (hc : (q.map Prod.snd).Perm (cols1381++cols1381))
    (hd : ∀ k ∈ requiredD1381, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1381, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1381 cols1381 requiredD1381 requiredS1381
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1381_eq] at model
  exact MomentData.excluded1381 ds ss model
def rows1382 : List Int := [0,2,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1382 : List Int := [0,2,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1382 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1382 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1382_eq : pairedProblem rows1382 cols1382 requiredD1382 requiredS1382 =
    MomentData.problem1382 := by rfl
theorem leaf1382 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1382++rows1382))
    (hc : (q.map Prod.snd).Perm (cols1382++cols1382))
    (hd : ∀ k ∈ requiredD1382, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1382, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1382 cols1382 requiredD1382 requiredS1382
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1382_eq] at model
  exact MomentData.excluded1382 ds ss model
def rows1383 : List Int := [0,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1383 : List Int := [0,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1383 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1383 : List Int := [4,7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1383_eq : pairedProblem rows1383 cols1383 requiredD1383 requiredS1383 =
    MomentData.problem1383 := by rfl
theorem leaf1383 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1383++rows1383))
    (hc : (q.map Prod.snd).Perm (cols1383++cols1383))
    (hd : ∀ k ∈ requiredD1383, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1383, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1383 cols1383 requiredD1383 requiredS1383
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1383_eq] at model
  exact MomentData.excluded1383 ds ss model
def rows1384 : List Int := [0,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def cols1384 : List Int := [0,2,4,5,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1384 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1384 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1384_eq : pairedProblem rows1384 cols1384 requiredD1384 requiredS1384 =
    MomentData.problem1384 := by rfl
theorem leaf1384 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1384++rows1384))
    (hc : (q.map Prod.snd).Perm (cols1384++cols1384))
    (hd : ∀ k ∈ requiredD1384, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1384, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1384 cols1384 requiredD1384 requiredS1384
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1384_eq] at model
  exact MomentData.excluded1384 ds ss model
def rows1385 : List Int := [0,1,3,6,9,12,15,18,20,21,24,26,27,28,29]
def cols1385 : List Int := [0,1,3,6,9,12,15,18,20,21,24,26,27,28,29]
def requiredD1385 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1385 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1385_eq : pairedProblem rows1385 cols1385 requiredD1385 requiredS1385 =
    MomentData.problem1385 := by rfl
theorem leaf1385 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1385++rows1385))
    (hc : (q.map Prod.snd).Perm (cols1385++cols1385))
    (hd : ∀ k ∈ requiredD1385, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1385, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1385 cols1385 requiredD1385 requiredS1385
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1385_eq] at model
  exact MomentData.excluded1385 ds ss model
def rows1386 : List Int := [0,1,3,6,9,12,15,18,20,21,24,26,27,28,29]
def cols1386 : List Int := [0,1,3,6,9,12,15,18,20,21,24,26,27,28,29]
def requiredD1386 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1386 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1386_eq : pairedProblem rows1386 cols1386 requiredD1386 requiredS1386 =
    MomentData.problem1386 := by rfl
theorem leaf1386 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1386++rows1386))
    (hc : (q.map Prod.snd).Perm (cols1386++cols1386))
    (hd : ∀ k ∈ requiredD1386, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1386, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1386 cols1386 requiredD1386 requiredS1386
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1386_eq] at model
  exact MomentData.excluded1386 ds ss model
def rows1387 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1387 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1387 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1387 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1387_eq : pairedProblem rows1387 cols1387 requiredD1387 requiredS1387 =
    MomentData.problem1387 := by rfl
theorem leaf1387 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1387++rows1387))
    (hc : (q.map Prod.snd).Perm (cols1387++cols1387))
    (hd : ∀ k ∈ requiredD1387, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1387, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1387 cols1387 requiredD1387 requiredS1387
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1387_eq] at model
  exact MomentData.excluded1387 ds ss model
def rows1388 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1388 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1388 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1388 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1388_eq : pairedProblem rows1388 cols1388 requiredD1388 requiredS1388 =
    MomentData.problem1388 := by rfl
theorem leaf1388 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1388++rows1388))
    (hc : (q.map Prod.snd).Perm (cols1388++cols1388))
    (hd : ∀ k ∈ requiredD1388, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1388, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1388 cols1388 requiredD1388 requiredS1388
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1388_eq] at model
  exact MomentData.excluded1388 ds ss model
def rows1389 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1389 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1389 : List Int := [-17,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,17]
def requiredS1389 : List Int := [11,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1389_eq : pairedProblem rows1389 cols1389 requiredD1389 requiredS1389 =
    MomentData.problem1389 := by rfl
theorem leaf1389 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1389++rows1389))
    (hc : (q.map Prod.snd).Perm (cols1389++cols1389))
    (hd : ∀ k ∈ requiredD1389, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1389, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1389 cols1389 requiredD1389 requiredS1389
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1389_eq] at model
  exact MomentData.excluded1389 ds ss model
def rows1390 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def cols1390 : List Int := [0,1,10,11,12,13,14,15,16,17,18,26,27,28,29]
def requiredD1390 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1390 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1390_eq : pairedProblem rows1390 cols1390 requiredD1390 requiredS1390 =
    MomentData.problem1390 := by rfl
theorem leaf1390 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1390++rows1390))
    (hc : (q.map Prod.snd).Perm (cols1390++cols1390))
    (hd : ∀ k ∈ requiredD1390, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1390, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1390 cols1390 requiredD1390 requiredS1390
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1390_eq] at model
  exact MomentData.excluded1390 ds ss model
def rows1391 : List Int := [0,3,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1391 : List Int := [0,3,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1391 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1391 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1391_eq : pairedProblem rows1391 cols1391 requiredD1391 requiredS1391 =
    MomentData.problem1391 := by rfl
theorem leaf1391 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1391++rows1391))
    (hc : (q.map Prod.snd).Perm (cols1391++cols1391))
    (hd : ∀ k ∈ requiredD1391, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1391, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1391 cols1391 requiredD1391 requiredS1391
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1391_eq] at model
  exact MomentData.excluded1391 ds ss model
def rows1392 : List Int := [0,3,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1392 : List Int := [0,3,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1392 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1392 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1392_eq : pairedProblem rows1392 cols1392 requiredD1392 requiredS1392 =
    MomentData.problem1392 := by rfl
theorem leaf1392 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1392++rows1392))
    (hc : (q.map Prod.snd).Perm (cols1392++cols1392))
    (hd : ∀ k ∈ requiredD1392, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1392, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1392 cols1392 requiredD1392 requiredS1392
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1392_eq] at model
  exact MomentData.excluded1392 ds ss model
def rows1393 : List Int := [0,1,10,11,12,13,14,15,16,17,19,26,27,28,29]
def cols1393 : List Int := [0,1,10,11,12,13,14,15,16,17,19,26,27,28,29]
def requiredD1393 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1393 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1393_eq : pairedProblem rows1393 cols1393 requiredD1393 requiredS1393 =
    MomentData.problem1393 := by rfl
theorem leaf1393 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1393++rows1393))
    (hc : (q.map Prod.snd).Perm (cols1393++cols1393))
    (hd : ∀ k ∈ requiredD1393, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1393, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1393 cols1393 requiredD1393 requiredS1393
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1393_eq] at model
  exact MomentData.excluded1393 ds ss model
def rows1394 : List Int := [0,1,10,11,12,13,14,15,16,17,19,26,27,28,29]
def cols1394 : List Int := [0,1,10,11,12,13,14,15,16,17,19,26,27,28,29]
def requiredD1394 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1394 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1394_eq : pairedProblem rows1394 cols1394 requiredD1394 requiredS1394 =
    MomentData.problem1394 := by rfl
theorem leaf1394 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1394++rows1394))
    (hc : (q.map Prod.snd).Perm (cols1394++cols1394))
    (hd : ∀ k ∈ requiredD1394, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1394, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1394 cols1394 requiredD1394 requiredS1394
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1394_eq] at model
  exact MomentData.excluded1394 ds ss model
def rows1395 : List Int := [0,4,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1395 : List Int := [0,4,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1395 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1395 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1395_eq : pairedProblem rows1395 cols1395 requiredD1395 requiredS1395 =
    MomentData.problem1395 := by rfl
theorem leaf1395 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1395++rows1395))
    (hc : (q.map Prod.snd).Perm (cols1395++cols1395))
    (hd : ∀ k ∈ requiredD1395, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1395, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1395 cols1395 requiredD1395 requiredS1395
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1395_eq] at model
  exact MomentData.excluded1395 ds ss model
def rows1396 : List Int := [0,4,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1396 : List Int := [0,4,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1396 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1396 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1396_eq : pairedProblem rows1396 cols1396 requiredD1396 requiredS1396 =
    MomentData.problem1396 := by rfl
theorem leaf1396 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1396++rows1396))
    (hc : (q.map Prod.snd).Perm (cols1396++cols1396))
    (hd : ∀ k ∈ requiredD1396, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1396, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1396 cols1396 requiredD1396 requiredS1396
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1396_eq] at model
  exact MomentData.excluded1396 ds ss model
def rows1397 : List Int := [0,1,10,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1397 : List Int := [0,1,10,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1397 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1397 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1397_eq : pairedProblem rows1397 cols1397 requiredD1397 requiredS1397 =
    MomentData.problem1397 := by rfl
theorem leaf1397 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1397++rows1397))
    (hc : (q.map Prod.snd).Perm (cols1397++cols1397))
    (hd : ∀ k ∈ requiredD1397, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1397, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1397 cols1397 requiredD1397 requiredS1397
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1397_eq] at model
  exact MomentData.excluded1397 ds ss model
def rows1398 : List Int := [0,1,10,11,12,13,14,15,16,17,20,26,27,28,29]
def cols1398 : List Int := [0,1,10,11,12,13,14,15,16,17,20,26,27,28,29]
def requiredD1398 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1398 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1398_eq : pairedProblem rows1398 cols1398 requiredD1398 requiredS1398 =
    MomentData.problem1398 := by rfl
theorem leaf1398 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1398++rows1398))
    (hc : (q.map Prod.snd).Perm (cols1398++cols1398))
    (hd : ∀ k ∈ requiredD1398, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1398, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1398 cols1398 requiredD1398 requiredS1398
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1398_eq] at model
  exact MomentData.excluded1398 ds ss model
def rows1399 : List Int := [0,1,3,6,9,12,15,18,21,22,24,26,27,28,29]
def cols1399 : List Int := [0,1,3,6,9,12,15,18,21,22,24,26,27,28,29]
def requiredD1399 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1399 : List Int := [6,9,12,15,18,21,24,27,30,33,36,39,42,45,48]
theorem problem1399_eq : pairedProblem rows1399 cols1399 requiredD1399 requiredS1399 =
    MomentData.problem1399 := by rfl
theorem leaf1399 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1399++rows1399))
    (hc : (q.map Prod.snd).Perm (cols1399++cols1399))
    (hd : ∀ k ∈ requiredD1399, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1399, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1399 cols1399 requiredD1399 requiredS1399
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1399_eq] at model
  exact MomentData.excluded1399 ds ss model
def rows1400 : List Int := [0,1,3,6,9,12,15,18,21,22,24,26,27,28,29]
def cols1400 : List Int := [0,1,3,6,9,12,15,18,21,22,24,26,27,28,29]
def requiredD1400 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1400 : List Int := [9,12,15,18,21,24,25,27,29,30,33,36,39,42,45]
theorem problem1400_eq : pairedProblem rows1400 cols1400 requiredD1400 requiredS1400 =
    MomentData.problem1400 := by rfl
theorem leaf1400 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1400++rows1400))
    (hc : (q.map Prod.snd).Perm (cols1400++cols1400))
    (hd : ∀ k ∈ requiredD1400, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1400, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1400 cols1400 requiredD1400 requiredS1400
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1400_eq] at model
  exact MomentData.excluded1400 ds ss model
def rows1401 : List Int := [0,2,5,6,8,11,14,17,20,23,25,26,27,28,29]
def cols1401 : List Int := [0,2,5,6,8,11,14,17,20,23,25,26,27,28,29]
def requiredD1401 : List Int := [-18,-15,-12,-9,-6,-3,-2,0,2,3,6,9,12,15,18]
def requiredS1401 : List Int := [7,10,13,16,19,22,23,25,27,28,31,34,37,40,43]
theorem problem1401_eq : pairedProblem rows1401 cols1401 requiredD1401 requiredS1401 =
    MomentData.problem1401 := by rfl
theorem leaf1401 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1401++rows1401))
    (hc : (q.map Prod.snd).Perm (cols1401++cols1401))
    (hd : ∀ k ∈ requiredD1401, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1401, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1401 cols1401 requiredD1401 requiredS1401
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1401_eq] at model
  exact MomentData.excluded1401 ds ss model
def rows1402 : List Int := [0,1,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1402 : List Int := [0,1,10,11,12,13,14,15,16,17,21,26,27,28,29]
def requiredD1402 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1402 : List Int := [11,21,22,23,24,25,26,27,28,29,30,31,32,33,43]
theorem problem1402_eq : pairedProblem rows1402 cols1402 requiredD1402 requiredS1402 =
    MomentData.problem1402 := by rfl
theorem leaf1402 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1402++rows1402))
    (hc : (q.map Prod.snd).Perm (cols1402++cols1402))
    (hd : ∀ k ∈ requiredD1402, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1402, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1402 cols1402 requiredD1402 requiredS1402
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1402_eq] at model
  exact MomentData.excluded1402 ds ss model
def rows1403 : List Int := [0,1,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1403 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1403 : List Int := [-15,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,17]
def requiredS1403 : List Int := [10,20,21,22,23,24,25,26,27,28,29,30,31,32,42]
theorem problem1403_eq : pairedProblem rows1403 cols1403 requiredD1403 requiredS1403 =
    MomentData.problem1403 := by rfl
theorem leaf1403 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1403++rows1403))
    (hc : (q.map Prod.snd).Perm (cols1403++cols1403))
    (hd : ∀ k ∈ requiredD1403, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1403, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1403 cols1403 requiredD1403 requiredS1403
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1403_eq] at model
  exact MomentData.excluded1403 ds ss model
def rows1404 : List Int := [0,1,10,11,12,13,14,15,16,17,21,26,27,28,29]
def cols1404 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1404 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS1404 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1404_eq : pairedProblem rows1404 cols1404 requiredD1404 requiredS1404 =
    MomentData.problem1404 := by rfl
theorem leaf1404 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1404++rows1404))
    (hc : (q.map Prod.snd).Perm (cols1404++cols1404))
    (hd : ∀ k ∈ requiredD1404, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1404, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1404 cols1404 requiredD1404 requiredS1404
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1404_eq] at model
  exact MomentData.excluded1404 ds ss model
def rows1405 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1405 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1405 : List Int := [-16,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,16]
def requiredS1405 : List Int := [9,19,20,21,22,23,24,25,26,27,28,29,30,31,41]
theorem problem1405_eq : pairedProblem rows1405 cols1405 requiredD1405 requiredS1405 =
    MomentData.problem1405 := by rfl
theorem leaf1405 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1405++rows1405))
    (hc : (q.map Prod.snd).Perm (cols1405++cols1405))
    (hd : ∀ k ∈ requiredD1405, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1405, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1405 cols1405 requiredD1405 requiredS1405
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1405_eq] at model
  exact MomentData.excluded1405 ds ss model
def rows1406 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def cols1406 : List Int := [0,5,9,10,11,12,13,14,15,16,25,26,27,28,29]
def requiredD1406 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1406 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem1406_eq : pairedProblem rows1406 cols1406 requiredD1406 requiredS1406 =
    MomentData.problem1406 := by rfl
theorem leaf1406 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1406++rows1406))
    (hc : (q.map Prod.snd).Perm (cols1406++cols1406))
    (hd : ∀ k ∈ requiredD1406, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1406, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1406 cols1406 requiredD1406 requiredS1406
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1406_eq] at model
  exact MomentData.excluded1406 ds ss model
def rows1407 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def cols1407 : List Int := [0,1,3,6,9,12,15,18,21,23,24,26,27,28,29]
def requiredD1407 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1407 : List Int := [6,9,12,15,18,21,24,27,29,30,33,36,39,42,45]
theorem problem1407_eq : pairedProblem rows1407 cols1407 requiredD1407 requiredS1407 =
    MomentData.problem1407 := by rfl
theorem leaf1407 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1407++rows1407))
    (hc : (q.map Prod.snd).Perm (cols1407++cols1407))
    (hd : ∀ k ∈ requiredD1407, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1407, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1407 cols1407 requiredD1407 requiredS1407
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1407_eq] at model
  exact MomentData.excluded1407 ds ss model
#print axioms leaf1280
end Gardner.Kernel.MomentContexts
