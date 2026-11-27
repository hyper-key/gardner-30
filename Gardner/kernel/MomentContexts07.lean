import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows896 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols896 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD896 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS896 : List Int := [18,20,22,24,26,28,30,32,34,36,38,40,42,46]
theorem problem896_eq : pairedProblem rows896 cols896 requiredD896 requiredS896 =
    MomentData.problem896 := by rfl
theorem leaf896 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows896++rows896))
    (hc : (q.map Prod.snd).Perm (cols896++cols896))
    (hd : ∀ k ∈ requiredD896, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS896, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows896 cols896 requiredD896 requiredS896
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem896_eq] at model
  exact MomentData.excluded896 ds ss model
def rows897 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols897 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD897 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS897 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,42,44]
theorem problem897_eq : pairedProblem rows897 cols897 requiredD897 requiredS897 =
    MomentData.problem897 := by rfl
theorem leaf897 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows897++rows897))
    (hc : (q.map Prod.snd).Perm (cols897++cols897))
    (hd : ∀ k ∈ requiredD897, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS897, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows897 cols897 requiredD897 requiredS897
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem897_eq] at model
  exact MomentData.excluded897 ds ss model
def rows898 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols898 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD898 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS898 : List Int := [18,20,22,24,26,28,30,32,34,36,38,40,42,44]
theorem problem898_eq : pairedProblem rows898 cols898 requiredD898 requiredS898 =
    MomentData.problem898 := by rfl
theorem leaf898 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows898++rows898))
    (hc : (q.map Prod.snd).Perm (cols898++cols898))
    (hd : ∀ k ∈ requiredD898, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS898, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows898 cols898 requiredD898 requiredS898
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem898_eq] at model
  exact MomentData.excluded898 ds ss model
def rows899 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols899 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD899 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS899 : List Int := [18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem899_eq : pairedProblem rows899 cols899 requiredD899 requiredS899 =
    MomentData.problem899 := by rfl
theorem leaf899 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows899++rows899))
    (hc : (q.map Prod.snd).Perm (cols899++cols899))
    (hd : ∀ k ∈ requiredD899, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS899, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows899 cols899 requiredD899 requiredS899
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem899_eq] at model
  exact MomentData.excluded899 ds ss model
def rows900 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols900 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD900 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS900 : List Int := [16,20,22,24,26,28,30,32,34,36,38,40,42,44,48]
theorem problem900_eq : pairedProblem rows900 cols900 requiredD900 requiredS900 =
    MomentData.problem900 := by rfl
theorem leaf900 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows900++rows900))
    (hc : (q.map Prod.snd).Perm (cols900++cols900))
    (hd : ∀ k ∈ requiredD900, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS900, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows900 cols900 requiredD900 requiredS900
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem900_eq] at model
  exact MomentData.excluded900 ds ss model
def rows901 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols901 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD901 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS901 : List Int := [16,20,22,24,26,28,30,32,34,36,38,40,42,44]
theorem problem901_eq : pairedProblem rows901 cols901 requiredD901 requiredS901 =
    MomentData.problem901 := by rfl
theorem leaf901 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows901++rows901))
    (hc : (q.map Prod.snd).Perm (cols901++cols901))
    (hd : ∀ k ∈ requiredD901, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS901, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows901 cols901 requiredD901 requiredS901
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem901_eq] at model
  exact MomentData.excluded901 ds ss model
def rows902 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols902 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD902 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS902 : List Int := [14,18,22,24,26,28,30,32,34,36,38,40,42,46,50]
theorem problem902_eq : pairedProblem rows902 cols902 requiredD902 requiredS902 =
    MomentData.problem902 := by rfl
theorem leaf902 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows902++rows902))
    (hc : (q.map Prod.snd).Perm (cols902++cols902))
    (hd : ∀ k ∈ requiredD902, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS902, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows902 cols902 requiredD902 requiredS902
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem902_eq] at model
  exact MomentData.excluded902 ds ss model
def rows903 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols903 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD903 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS903 : List Int := [14,18,22,24,26,28,30,32,34,36,38,40,42,46]
theorem problem903_eq : pairedProblem rows903 cols903 requiredD903 requiredS903 =
    MomentData.problem903 := by rfl
theorem leaf903 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows903++rows903))
    (hc : (q.map Prod.snd).Perm (cols903++cols903))
    (hd : ∀ k ∈ requiredD903, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS903, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows903 cols903 requiredD903 requiredS903
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem903_eq] at model
  exact MomentData.excluded903 ds ss model
def rows904 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols904 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD904 : List Int := [-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18]
def requiredS904 : List Int := [10,14,18,22,24,26,28,30,32,34,36,38,42,46,50]
theorem problem904_eq : pairedProblem rows904 cols904 requiredD904 requiredS904 =
    MomentData.problem904 := by rfl
theorem leaf904 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows904++rows904))
    (hc : (q.map Prod.snd).Perm (cols904++cols904))
    (hd : ∀ k ∈ requiredD904, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS904, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows904 cols904 requiredD904 requiredS904
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem904_eq] at model
  exact MomentData.excluded904 ds ss model
def rows905 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols905 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD905 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS905 : List Int := [14,18,22,24,26,28,30,32,34,36,38,42,46,50]
theorem problem905_eq : pairedProblem rows905 cols905 requiredD905 requiredS905 =
    MomentData.problem905 := by rfl
theorem leaf905 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows905++rows905))
    (hc : (q.map Prod.snd).Perm (cols905++cols905))
    (hd : ∀ k ∈ requiredD905, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS905, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows905 cols905 requiredD905 requiredS905
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem905_eq] at model
  exact MomentData.excluded905 ds ss model
def rows906 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols906 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD906 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS906 : List Int := [14,18,22,24,26,28,30,32,34,36,38,42,46]
theorem problem906_eq : pairedProblem rows906 cols906 requiredD906 requiredS906 =
    MomentData.problem906 := by rfl
theorem leaf906 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows906++rows906))
    (hc : (q.map Prod.snd).Perm (cols906++cols906))
    (hd : ∀ k ∈ requiredD906, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS906, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows906 cols906 requiredD906 requiredS906
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem906_eq] at model
  exact MomentData.excluded906 ds ss model
def rows907 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols907 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD907 : List Int := [-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16]
def requiredS907 : List Int := [12,16,20,22,24,26,28,30,32,34,36,38,40,44,48]
theorem problem907_eq : pairedProblem rows907 cols907 requiredD907 requiredS907 =
    MomentData.problem907 := by rfl
theorem leaf907 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows907++rows907))
    (hc : (q.map Prod.snd).Perm (cols907++cols907))
    (hd : ∀ k ∈ requiredD907, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS907, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows907 cols907 requiredD907 requiredS907
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem907_eq] at model
  exact MomentData.excluded907 ds ss model
def rows908 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols908 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD908 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS908 : List Int := [16,20,22,24,26,28,30,32,34,36,38,40,44,48]
theorem problem908_eq : pairedProblem rows908 cols908 requiredD908 requiredS908 =
    MomentData.problem908 := by rfl
theorem leaf908 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows908++rows908))
    (hc : (q.map Prod.snd).Perm (cols908++cols908))
    (hd : ∀ k ∈ requiredD908, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS908, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows908 cols908 requiredD908 requiredS908
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem908_eq] at model
  exact MomentData.excluded908 ds ss model
def rows909 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols909 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD909 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS909 : List Int := [16,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem909_eq : pairedProblem rows909 cols909 requiredD909 requiredS909 =
    MomentData.problem909 := by rfl
theorem leaf909 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows909++rows909))
    (hc : (q.map Prod.snd).Perm (cols909++cols909))
    (hd : ∀ k ∈ requiredD909, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS909, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows909 cols909 requiredD909 requiredS909
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem909_eq] at model
  exact MomentData.excluded909 ds ss model
def rows910 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols910 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD910 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS910 : List Int := [12,16,20,24,26,28,30,32,34,36,38,40,44,48,52]
theorem problem910_eq : pairedProblem rows910 cols910 requiredD910 requiredS910 =
    MomentData.problem910 := by rfl
theorem leaf910 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows910++rows910))
    (hc : (q.map Prod.snd).Perm (cols910++cols910))
    (hd : ∀ k ∈ requiredD910, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS910, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows910 cols910 requiredD910 requiredS910
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem910_eq] at model
  exact MomentData.excluded910 ds ss model
def rows911 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols911 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD911 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS911 : List Int := [12,16,20,24,26,28,30,32,34,36,38,40,44,48]
theorem problem911_eq : pairedProblem rows911 cols911 requiredD911 requiredS911 =
    MomentData.problem911 := by rfl
theorem leaf911 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows911++rows911))
    (hc : (q.map Prod.snd).Perm (cols911++cols911))
    (hd : ∀ k ∈ requiredD911, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS911, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows911 cols911 requiredD911 requiredS911
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem911_eq] at model
  exact MomentData.excluded911 ds ss model
def rows912 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols912 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD912 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS912 : List Int := [10,14,18,22,26,28,30,32,34,36,38,42,46,50,54]
theorem problem912_eq : pairedProblem rows912 cols912 requiredD912 requiredS912 =
    MomentData.problem912 := by rfl
theorem leaf912 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows912++rows912))
    (hc : (q.map Prod.snd).Perm (cols912++cols912))
    (hd : ∀ k ∈ requiredD912, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS912, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows912 cols912 requiredD912 requiredS912
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem912_eq] at model
  exact MomentData.excluded912 ds ss model
def rows913 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols913 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD913 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS913 : List Int := [10,14,18,22,26,28,30,32,34,36,38,42,46,50]
theorem problem913_eq : pairedProblem rows913 cols913 requiredD913 requiredS913 =
    MomentData.problem913 := by rfl
theorem leaf913 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows913++rows913))
    (hc : (q.map Prod.snd).Perm (cols913++cols913))
    (hd : ∀ k ∈ requiredD913, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS913, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows913 cols913 requiredD913 requiredS913
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem913_eq] at model
  exact MomentData.excluded913 ds ss model
def rows914 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols914 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD914 : List Int := [-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22]
def requiredS914 : List Int := [6,10,14,18,22,26,28,30,32,34,38,42,46,50,54]
theorem problem914_eq : pairedProblem rows914 cols914 requiredD914 requiredS914 =
    MomentData.problem914 := by rfl
theorem leaf914 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows914++rows914))
    (hc : (q.map Prod.snd).Perm (cols914++cols914))
    (hd : ∀ k ∈ requiredD914, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS914, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows914 cols914 requiredD914 requiredS914
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem914_eq] at model
  exact MomentData.excluded914 ds ss model
def rows915 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols915 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD915 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS915 : List Int := [10,14,18,22,26,28,30,32,34,38,42,46,50,54]
theorem problem915_eq : pairedProblem rows915 cols915 requiredD915 requiredS915 =
    MomentData.problem915 := by rfl
theorem leaf915 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows915++rows915))
    (hc : (q.map Prod.snd).Perm (cols915++cols915))
    (hd : ∀ k ∈ requiredD915, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS915, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows915 cols915 requiredD915 requiredS915
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem915_eq] at model
  exact MomentData.excluded915 ds ss model
def rows916 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols916 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD916 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS916 : List Int := [10,14,18,22,26,28,30,32,34,38,42,46,50]
theorem problem916_eq : pairedProblem rows916 cols916 requiredD916 requiredS916 =
    MomentData.problem916 := by rfl
theorem leaf916 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows916++rows916))
    (hc : (q.map Prod.snd).Perm (cols916++cols916))
    (hd : ∀ k ∈ requiredD916, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS916, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows916 cols916 requiredD916 requiredS916
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem916_eq] at model
  exact MomentData.excluded916 ds ss model
def rows917 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols917 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD917 : List Int := [-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20]
def requiredS917 : List Int := [8,12,16,20,24,26,28,30,32,34,36,40,44,48,52]
theorem problem917_eq : pairedProblem rows917 cols917 requiredD917 requiredS917 =
    MomentData.problem917 := by rfl
theorem leaf917 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows917++rows917))
    (hc : (q.map Prod.snd).Perm (cols917++cols917))
    (hd : ∀ k ∈ requiredD917, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS917, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows917 cols917 requiredD917 requiredS917
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem917_eq] at model
  exact MomentData.excluded917 ds ss model
def rows918 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols918 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD918 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS918 : List Int := [12,16,20,24,26,28,30,32,34,36,40,44,48,52]
theorem problem918_eq : pairedProblem rows918 cols918 requiredD918 requiredS918 =
    MomentData.problem918 := by rfl
theorem leaf918 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows918++rows918))
    (hc : (q.map Prod.snd).Perm (cols918++cols918))
    (hd : ∀ k ∈ requiredD918, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS918, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows918 cols918 requiredD918 requiredS918
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem918_eq] at model
  exact MomentData.excluded918 ds ss model
def rows919 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols919 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD919 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS919 : List Int := [12,16,20,24,26,28,30,32,34,36,40,44,48]
theorem problem919_eq : pairedProblem rows919 cols919 requiredD919 requiredS919 =
    MomentData.problem919 := by rfl
theorem leaf919 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows919++rows919))
    (hc : (q.map Prod.snd).Perm (cols919++cols919))
    (hd : ∀ k ∈ requiredD919, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS919, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows919 cols919 requiredD919 requiredS919
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem919_eq] at model
  exact MomentData.excluded919 ds ss model
def rows920 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols920 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD920 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS920 : List Int := [8,12,16,20,24,28,30,32,34,36,40,44,48,52]
theorem problem920_eq : pairedProblem rows920 cols920 requiredD920 requiredS920 =
    MomentData.problem920 := by rfl
theorem leaf920 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows920++rows920))
    (hc : (q.map Prod.snd).Perm (cols920++cols920))
    (hd : ∀ k ∈ requiredD920, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS920, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows920 cols920 requiredD920 requiredS920
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem920_eq] at model
  exact MomentData.excluded920 ds ss model
def rows921 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols921 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD921 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS921 : List Int := [6,10,14,18,22,26,30,32,34,38,42,46,50,54]
theorem problem921_eq : pairedProblem rows921 cols921 requiredD921 requiredS921 =
    MomentData.problem921 := by rfl
theorem leaf921 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows921++rows921))
    (hc : (q.map Prod.snd).Perm (cols921++cols921))
    (hd : ∀ k ∈ requiredD921, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS921, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows921 cols921 requiredD921 requiredS921
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem921_eq] at model
  exact MomentData.excluded921 ds ss model
def rows922 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols922 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD922 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS922 : List Int := [6,10,14,18,22,26,30,34,38,42,46,50,54]
theorem problem922_eq : pairedProblem rows922 cols922 requiredD922 requiredS922 =
    MomentData.problem922 := by rfl
theorem leaf922 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows922++rows922))
    (hc : (q.map Prod.snd).Perm (cols922++cols922))
    (hd : ∀ k ∈ requiredD922, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS922, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows922 cols922 requiredD922 requiredS922
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem922_eq] at model
  exact MomentData.excluded922 ds ss model
def rows923 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def cols923 : List Int := [0,2,4,6,8,10,12,14,16,18,20,22,24,26,28]
def requiredD923 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS923 : List Int := [8,12,16,20,24,28,30,32,36,40,44,48,52]
theorem problem923_eq : pairedProblem rows923 cols923 requiredD923 requiredS923 =
    MomentData.problem923 := by rfl
theorem leaf923 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows923++rows923))
    (hc : (q.map Prod.snd).Perm (cols923++cols923))
    (hd : ∀ k ∈ requiredD923, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS923, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows923 cols923 requiredD923 requiredS923
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem923_eq] at model
  exact MomentData.excluded923 ds ss model
def rows924 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols924 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD924 : List Int := [-24,-20,-16,-12,-8,-4,0,4,8,12,16,20,24]
def requiredS924 : List Int := [3,7,11,15,19,23,27,28,31,35,39,43,47,51,55]
theorem problem924_eq : pairedProblem rows924 cols924 requiredD924 requiredS924 =
    MomentData.problem924 := by rfl
theorem leaf924 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows924++rows924))
    (hc : (q.map Prod.snd).Perm (cols924++cols924))
    (hd : ∀ k ∈ requiredD924, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS924, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows924 cols924 requiredD924 requiredS924
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem924_eq] at model
  exact MomentData.excluded924 ds ss model
def rows925 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols925 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD925 : List Int := [-24,-20,-16,-12,-8,-4,-3,0,3,4,8,12,16,20,24]
def requiredS925 : List Int := [7,11,15,19,23,27,28,31,35,39,43,47,51,55]
theorem problem925_eq : pairedProblem rows925 cols925 requiredD925 requiredS925 =
    MomentData.problem925 := by rfl
theorem leaf925 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows925++rows925))
    (hc : (q.map Prod.snd).Perm (cols925++cols925))
    (hd : ∀ k ∈ requiredD925, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS925, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows925 cols925 requiredD925 requiredS925
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem925_eq] at model
  exact MomentData.excluded925 ds ss model
def rows926 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols926 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD926 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS926 : List Int := [3,7,11,15,19,23,27,28,31,35,39,43,47,51]
theorem problem926_eq : pairedProblem rows926 cols926 requiredD926 requiredS926 =
    MomentData.problem926 := by rfl
theorem leaf926 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows926++rows926))
    (hc : (q.map Prod.snd).Perm (cols926++cols926))
    (hd : ∀ k ∈ requiredD926, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS926, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows926 cols926 requiredD926 requiredS926
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem926_eq] at model
  exact MomentData.excluded926 ds ss model
def rows927 : List Int := [0,2,3,6,7,10,11,14,15,18,19,22,23,26,27]
def cols927 : List Int := [0,2,3,6,7,10,11,14,15,18,19,22,23,26,27]
def requiredD927 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS927 : List Int := [5,9,13,17,21,25,29,30,33,37,41,45,49,53]
theorem problem927_eq : pairedProblem rows927 cols927 requiredD927 requiredS927 =
    MomentData.problem927 := by rfl
theorem leaf927 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows927++rows927))
    (hc : (q.map Prod.snd).Perm (cols927++cols927))
    (hd : ∀ k ∈ requiredD927, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS927, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows927 cols927 requiredD927 requiredS927
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem927_eq] at model
  exact MomentData.excluded927 ds ss model
def rows928 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def cols928 : List Int := [0,10,11,12,13,14,15,16,17,18,19,20,21,22,23]
def requiredD928 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS928 : List Int := [10,25,26,27,28,29,30,31,32,33,34,35,36,37,38]
theorem problem928_eq : pairedProblem rows928 cols928 requiredD928 requiredS928 =
    MomentData.problem928 := by rfl
theorem leaf928 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows928++rows928))
    (hc : (q.map Prod.snd).Perm (cols928++cols928))
    (hd : ∀ k ∈ requiredD928, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS928, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows928 cols928 requiredD928 requiredS928
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem928_eq] at model
  exact MomentData.excluded928 ds ss model
def rows929 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,23]
def cols929 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD929 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS929 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem929_eq : pairedProblem rows929 cols929 requiredD929 requiredS929 =
    MomentData.problem929 := by rfl
theorem leaf929 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows929++rows929))
    (hc : (q.map Prod.snd).Perm (cols929++cols929))
    (hd : ∀ k ∈ requiredD929, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS929, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows929 cols929 requiredD929 requiredS929
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem929_eq] at model
  exact MomentData.excluded929 ds ss model
def rows930 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols930 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD930 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS930 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem930_eq : pairedProblem rows930 cols930 requiredD930 requiredS930 =
    MomentData.problem930 := by rfl
theorem leaf930 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows930++rows930))
    (hc : (q.map Prod.snd).Perm (cols930++cols930))
    (hd : ∀ k ∈ requiredD930, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS930, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows930 cols930 requiredD930 requiredS930
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem930_eq] at model
  exact MomentData.excluded930 ds ss model
def rows931 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols931 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD931 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS931 : List Int := [9,24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem931_eq : pairedProblem rows931 cols931 requiredD931 requiredS931 =
    MomentData.problem931 := by rfl
theorem leaf931 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows931++rows931))
    (hc : (q.map Prod.snd).Perm (cols931++cols931))
    (hd : ∀ k ∈ requiredD931, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS931, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows931 cols931 requiredD931 requiredS931
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem931_eq] at model
  exact MomentData.excluded931 ds ss model
def rows932 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols932 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD932 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS932 : List Int := [24,25,26,27,28,29,30,31,32,33,34,35,36,37]
theorem problem932_eq : pairedProblem rows932 cols932 requiredD932 requiredS932 =
    MomentData.problem932 := by rfl
theorem leaf932 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows932++rows932))
    (hc : (q.map Prod.snd).Perm (cols932++cols932))
    (hd : ∀ k ∈ requiredD932, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS932, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows932 cols932 requiredD932 requiredS932
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem932_eq] at model
  exact MomentData.excluded932 ds ss model
def rows933 : List Int := [0,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols933 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD933 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7,8]
def requiredS933 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem933_eq : pairedProblem rows933 cols933 requiredD933 requiredS933 =
    MomentData.problem933 := by rfl
theorem leaf933 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows933++rows933))
    (hc : (q.map Prod.snd).Perm (cols933++cols933))
    (hd : ∀ k ∈ requiredD933, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS933, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows933 cols933 requiredD933 requiredS933
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem933_eq] at model
  exact MomentData.excluded933 ds ss model
def rows934 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols934 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD934 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS934 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,49]
theorem problem934_eq : pairedProblem rows934 cols934 requiredD934 requiredS934 =
    MomentData.problem934 := by rfl
theorem leaf934 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows934++rows934))
    (hc : (q.map Prod.snd).Perm (cols934++cols934))
    (hd : ∀ k ∈ requiredD934, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS934, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows934 cols934 requiredD934 requiredS934
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem934_eq] at model
  exact MomentData.excluded934 ds ss model
def rows935 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols935 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD935 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS935 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem935_eq : pairedProblem rows935 cols935 requiredD935 requiredS935 =
    MomentData.problem935 := by rfl
theorem leaf935 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows935++rows935))
    (hc : (q.map Prod.snd).Perm (cols935++cols935))
    (hd : ∀ k ∈ requiredD935, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS935, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows935 cols935 requiredD935 requiredS935
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem935_eq] at model
  exact MomentData.excluded935 ds ss model
def rows936 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def cols936 : List Int := [0,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def requiredD936 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS936 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem936_eq : pairedProblem rows936 cols936 requiredD936 requiredS936 =
    MomentData.problem936 := by rfl
theorem leaf936 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows936++rows936))
    (hc : (q.map Prod.snd).Perm (cols936++cols936))
    (hd : ∀ k ∈ requiredD936, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS936, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows936 cols936 requiredD936 requiredS936
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem936_eq] at model
  exact MomentData.excluded936 ds ss model
def rows937 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def cols937 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def requiredD937 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS937 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,48]
theorem problem937_eq : pairedProblem rows937 cols937 requiredD937 requiredS937 =
    MomentData.problem937 := by rfl
theorem leaf937 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows937++rows937))
    (hc : (q.map Prod.snd).Perm (cols937++cols937))
    (hd : ∀ k ∈ requiredD937, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS937, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows937 cols937 requiredD937 requiredS937
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem937_eq] at model
  exact MomentData.excluded937 ds ss model
def rows938 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,28]
def cols938 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,28]
def requiredD938 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS938 : List Int := [5,9,13,17,21,25,29,30,33,37,41,45,49,53]
theorem problem938_eq : pairedProblem rows938 cols938 requiredD938 requiredS938 =
    MomentData.problem938 := by rfl
theorem leaf938 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows938++rows938))
    (hc : (q.map Prod.snd).Perm (cols938++cols938))
    (hd : ∀ k ∈ requiredD938, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS938, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows938 cols938 requiredD938 requiredS938
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem938_eq] at model
  exact MomentData.excluded938 ds ss model
def rows939 : List Int := [1,2,4,7,10,13,16,18,19,21,22,24,25,27,28]
def cols939 : List Int := [1,2,4,7,10,13,16,18,19,21,22,24,25,27,28]
def requiredD939 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS939 : List Int := [5,8,11,14,17,20,23,26,29,32,34,35,38,41,44]
theorem problem939_eq : pairedProblem rows939 cols939 requiredD939 requiredS939 =
    MomentData.problem939 := by rfl
theorem leaf939 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows939++rows939))
    (hc : (q.map Prod.snd).Perm (cols939++cols939))
    (hd : ∀ k ∈ requiredD939, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS939, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows939 cols939 requiredD939 requiredS939
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem939_eq] at model
  exact MomentData.excluded939 ds ss model
def rows940 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols940 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD940 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS940 : List Int := [8,11,14,17,20,23,26,29,32,35,37,38,41,44,47]
theorem problem940_eq : pairedProblem rows940 cols940 requiredD940 requiredS940 =
    MomentData.problem940 := by rfl
theorem leaf940 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows940++rows940))
    (hc : (q.map Prod.snd).Perm (cols940++cols940))
    (hd : ∀ k ∈ requiredD940, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS940, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows940 cols940 requiredD940 requiredS940
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem940_eq] at model
  exact MomentData.excluded940 ds ss model
def rows941 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols941 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD941 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS941 : List Int := [11,14,17,20,23,26,29,32,35,37,38,41,44,47]
theorem problem941_eq : pairedProblem rows941 cols941 requiredD941 requiredS941 =
    MomentData.problem941 := by rfl
theorem leaf941 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows941++rows941))
    (hc : (q.map Prod.snd).Perm (cols941++cols941))
    (hd : ∀ k ∈ requiredD941, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS941, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows941 cols941 requiredD941 requiredS941
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem941_eq] at model
  exact MomentData.excluded941 ds ss model
def rows942 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols942 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD942 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS942 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem942_eq : pairedProblem rows942 cols942 requiredD942 requiredS942 =
    MomentData.problem942 := by rfl
theorem leaf942 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows942++rows942))
    (hc : (q.map Prod.snd).Perm (cols942++cols942))
    (hd : ∀ k ∈ requiredD942, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS942, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows942 cols942 requiredD942 requiredS942
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem942_eq] at model
  exact MomentData.excluded942 ds ss model
def rows943 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols943 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD943 : List Int := [-18,-15,-12,-11,-9,-6,-3,0,3,6,9,11,12,15,18]
def requiredS943 : List Int := [8,11,14,17,20,23,26,29,32,35,37,38,41,44]
theorem problem943_eq : pairedProblem rows943 cols943 requiredD943 requiredS943 =
    MomentData.problem943 := by rfl
theorem leaf943 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows943++rows943))
    (hc : (q.map Prod.snd).Perm (cols943++cols943))
    (hd : ∀ k ∈ requiredD943, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS943, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows943 cols943 requiredD943 requiredS943
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem943_eq] at model
  exact MomentData.excluded943 ds ss model
def rows944 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def cols944 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def requiredD944 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS944 : List Int := [11,14,17,20,21,23,26,29,32,35,38,41,44,47,50]
theorem problem944_eq : pairedProblem rows944 cols944 requiredD944 requiredS944 =
    MomentData.problem944 := by rfl
theorem leaf944 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows944++rows944))
    (hc : (q.map Prod.snd).Perm (cols944++cols944))
    (hd : ∀ k ∈ requiredD944, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS944, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows944 cols944 requiredD944 requiredS944
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem944_eq] at model
  exact MomentData.excluded944 ds ss model
def rows945 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def cols945 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def requiredD945 : List Int := [-18,-15,-12,-11,-9,-6,-3,0,3,6,9,11,12,15,18]
def requiredS945 : List Int := [14,17,20,21,23,26,29,32,35,38,41,44,47,50]
theorem problem945_eq : pairedProblem rows945 cols945 requiredD945 requiredS945 =
    MomentData.problem945 := by rfl
theorem leaf945 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows945++rows945))
    (hc : (q.map Prod.snd).Perm (cols945++cols945))
    (hd : ∀ k ∈ requiredD945, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS945, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows945 cols945 requiredD945 requiredS945
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem945_eq] at model
  exact MomentData.excluded945 ds ss model
def rows946 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def cols946 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def requiredD946 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS946 : List Int := [11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem946_eq : pairedProblem rows946 cols946 requiredD946 requiredS946 =
    MomentData.problem946 := by rfl
theorem leaf946 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows946++rows946))
    (hc : (q.map Prod.snd).Perm (cols946++cols946))
    (hd : ∀ k ∈ requiredD946, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS946, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows946 cols946 requiredD946 requiredS946
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem946_eq] at model
  exact MomentData.excluded946 ds ss model
def rows947 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def cols947 : List Int := [1,2,4,5,7,8,10,13,16,19,22,24,25,27,28]
def requiredD947 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS947 : List Int := [11,14,17,20,21,23,26,29,32,35,38,41,44,47]
theorem problem947_eq : pairedProblem rows947 cols947 requiredD947 requiredS947 =
    MomentData.problem947 := by rfl
theorem leaf947 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows947++rows947))
    (hc : (q.map Prod.snd).Perm (cols947++cols947))
    (hd : ∀ k ∈ requiredD947, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS947, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows947 cols947 requiredD947 requiredS947
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem947_eq] at model
  exact MomentData.excluded947 ds ss model
def rows948 : List Int := [1,2,4,5,7,8,10,11,13,16,19,22,25,27,28]
def cols948 : List Int := [1,2,4,5,7,8,10,11,13,16,19,22,25,27,28]
def requiredD948 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS948 : List Int := [14,17,20,23,24,26,29,32,35,38,41,44,47,50,53]
theorem problem948_eq : pairedProblem rows948 cols948 requiredD948 requiredS948 =
    MomentData.problem948 := by rfl
theorem leaf948 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows948++rows948))
    (hc : (q.map Prod.snd).Perm (cols948++cols948))
    (hd : ∀ k ∈ requiredD948, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS948, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows948 cols948 requiredD948 requiredS948
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem948_eq] at model
  exact MomentData.excluded948 ds ss model
def rows949 : List Int := [1,3,5,7,9,11,13,15,17,18,20,22,24,26,28]
def cols949 : List Int := [1,3,5,7,9,11,13,15,17,18,20,22,24,26,28]
def requiredD949 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS949 : List Int := [16,19,21,23,25,27,29,31,33,35,37,39,41,43,45]
theorem problem949_eq : pairedProblem rows949 cols949 requiredD949 requiredS949 =
    MomentData.problem949 := by rfl
theorem leaf949 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows949++rows949))
    (hc : (q.map Prod.snd).Perm (cols949++cols949))
    (hd : ∀ k ∈ requiredD949, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS949, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows949 cols949 requiredD949 requiredS949
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem949_eq] at model
  exact MomentData.excluded949 ds ss model
def rows950 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols950 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD950 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS950 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem950_eq : pairedProblem rows950 cols950 requiredD950 requiredS950 =
    MomentData.problem950 := by rfl
theorem leaf950 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows950++rows950))
    (hc : (q.map Prod.snd).Perm (cols950++cols950))
    (hd : ∀ k ∈ requiredD950, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS950, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows950 cols950 requiredD950 requiredS950
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem950_eq] at model
  exact MomentData.excluded950 ds ss model
def rows951 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols951 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD951 : List Int := [-17,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,17]
def requiredS951 : List Int := [14,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem951_eq : pairedProblem rows951 cols951 requiredD951 requiredS951 =
    MomentData.problem951 := by rfl
theorem leaf951 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows951++rows951))
    (hc : (q.map Prod.snd).Perm (cols951++cols951))
    (hd : ∀ k ∈ requiredD951, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS951, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows951 cols951 requiredD951 requiredS951
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem951_eq] at model
  exact MomentData.excluded951 ds ss model
def rows952 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols952 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD952 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS952 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem952_eq : pairedProblem rows952 cols952 requiredD952 requiredS952 =
    MomentData.problem952 := by rfl
theorem leaf952 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows952++rows952))
    (hc : (q.map Prod.snd).Perm (cols952++cols952))
    (hd : ∀ k ∈ requiredD952, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS952, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows952 cols952 requiredD952 requiredS952
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem952_eq] at model
  exact MomentData.excluded952 ds ss model
def rows953 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def cols953 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def requiredD953 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS953 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem953_eq : pairedProblem rows953 cols953 requiredD953 requiredS953 =
    MomentData.problem953 := by rfl
theorem leaf953 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows953++rows953))
    (hc : (q.map Prod.snd).Perm (cols953++cols953))
    (hd : ∀ k ∈ requiredD953, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS953, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows953 cols953 requiredD953 requiredS953
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem953_eq] at model
  exact MomentData.excluded953 ds ss model
def rows954 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def cols954 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def requiredD954 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS954 : List Int := [17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem954_eq : pairedProblem rows954 cols954 requiredD954 requiredS954 =
    MomentData.problem954 := by rfl
theorem leaf954 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows954++rows954))
    (hc : (q.map Prod.snd).Perm (cols954++cols954))
    (hd : ∀ k ∈ requiredD954, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS954, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows954 cols954 requiredD954 requiredS954
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem954_eq] at model
  exact MomentData.excluded954 ds ss model
def rows955 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def cols955 : List Int := [1,3,5,7,9,11,13,14,16,18,20,22,24,26,28]
def requiredD955 : List Int := [-17,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,17]
def requiredS955 : List Int := [15,17,19,21,23,25,27,29,31,33,35,37,39,44]
theorem problem955_eq : pairedProblem rows955 cols955 requiredD955 requiredS955 =
    MomentData.problem955 := by rfl
theorem leaf955 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows955++rows955))
    (hc : (q.map Prod.snd).Perm (cols955++cols955))
    (hd : ∀ k ∈ requiredD955, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS955, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows955 cols955 requiredD955 requiredS955
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem955_eq] at model
  exact MomentData.excluded955 ds ss model
def rows956 : List Int := [1,3,5,7,9,11,12,14,16,18,20,22,24,26,28]
def cols956 : List Int := [1,3,5,7,9,11,12,14,16,18,20,22,24,26,28]
def requiredD956 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS956 : List Int := [13,15,17,19,21,23,25,27,29,31,33,35,37,39,42]
theorem problem956_eq : pairedProblem rows956 cols956 requiredD956 requiredS956 =
    MomentData.problem956 := by rfl
theorem leaf956 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows956++rows956))
    (hc : (q.map Prod.snd).Perm (cols956++cols956))
    (hd : ∀ k ∈ requiredD956, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS956, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows956 cols956 requiredD956 requiredS956
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem956_eq] at model
  exact MomentData.excluded956 ds ss model
def rows957 : List Int := [1,2,3,6,7,10,11,14,15,18,19,22,23,26,27]
def cols957 : List Int := [1,2,3,6,7,10,11,14,15,18,19,22,23,26,27]
def requiredD957 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS957 : List Int := [5,9,13,17,21,25,28,29,33,37,41,45,49,53]
theorem problem957_eq : pairedProblem rows957 cols957 requiredD957 requiredS957 =
    MomentData.problem957 := by rfl
theorem leaf957 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows957++rows957))
    (hc : (q.map Prod.snd).Perm (cols957++cols957))
    (hd : ∀ k ∈ requiredD957, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS957, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows957 cols957 requiredD957 requiredS957
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem957_eq] at model
  exact MomentData.excluded957 ds ss model
def rows958 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols958 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD958 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS958 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem958_eq : pairedProblem rows958 cols958 requiredD958 requiredS958 =
    MomentData.problem958 := by rfl
theorem leaf958 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows958++rows958))
    (hc : (q.map Prod.snd).Perm (cols958++cols958))
    (hd : ∀ k ∈ requiredD958, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS958, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows958 cols958 requiredD958 requiredS958
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem958_eq] at model
  exact MomentData.excluded958 ds ss model
def rows959 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def cols959 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,21]
def requiredD959 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS959 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem959_eq : pairedProblem rows959 cols959 requiredD959 requiredS959 =
    MomentData.problem959 := by rfl
theorem leaf959 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows959++rows959))
    (hc : (q.map Prod.snd).Perm (cols959++cols959))
    (hd : ∀ k ∈ requiredD959, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS959, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows959 cols959 requiredD959 requiredS959
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem959_eq] at model
  exact MomentData.excluded959 ds ss model
def rows960 : List Int := [0,1,2,3,4,5,14,22,23,24,25,26,27,28,29]
def cols960 : List Int := [0,1,2,3,4,5,14,22,23,24,25,26,27,28,29]
def requiredD960 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS960 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem960_eq : pairedProblem rows960 cols960 requiredD960 requiredS960 =
    MomentData.problem960 := by rfl
theorem leaf960 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows960++rows960))
    (hc : (q.map Prod.snd).Perm (cols960++cols960))
    (hd : ∀ k ∈ requiredD960, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS960, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows960 cols960 requiredD960 requiredS960
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem960_eq] at model
  exact MomentData.excluded960 ds ss model
def rows961 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def cols961 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def requiredD961 : List Int := [-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7]
def requiredS961 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem961_eq : pairedProblem rows961 cols961 requiredD961 requiredS961 =
    MomentData.problem961 := by rfl
theorem leaf961 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows961++rows961))
    (hc : (q.map Prod.snd).Perm (cols961++cols961))
    (hd : ∀ k ∈ requiredD961, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS961, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows961 cols961 requiredD961 requiredS961
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem961_eq] at model
  exact MomentData.excluded961 ds ss model
def rows962 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def cols962 : List Int := [0,1,2,3,4,5,15,22,23,24,25,26,27,28,29]
def requiredD962 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS962 : List Int := [20,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem962_eq : pairedProblem rows962 cols962 requiredD962 requiredS962 =
    MomentData.problem962 := by rfl
theorem leaf962 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows962++rows962))
    (hc : (q.map Prod.snd).Perm (cols962++cols962))
    (hd : ∀ k ∈ requiredD962, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS962, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows962 cols962 requiredD962 requiredS962
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem962_eq] at model
  exact MomentData.excluded962 ds ss model
def rows963 : List Int := [0,1,2,3,4,5,16,22,23,24,25,26,27,28,29]
def cols963 : List Int := [0,1,2,3,4,5,16,22,23,24,25,26,27,28,29]
def requiredD963 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS963 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem963_eq : pairedProblem rows963 cols963 requiredD963 requiredS963 =
    MomentData.problem963 := by rfl
theorem leaf963 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows963++rows963))
    (hc : (q.map Prod.snd).Perm (cols963++cols963))
    (hd : ∀ k ∈ requiredD963, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS963, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows963 cols963 requiredD963 requiredS963
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem963_eq] at model
  exact MomentData.excluded963 ds ss model
def rows964 : List Int := [0,1,2,3,4,5,17,22,23,24,25,26,27,28,29]
def cols964 : List Int := [0,1,2,3,4,5,17,22,23,24,25,26,27,28,29]
def requiredD964 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS964 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem964_eq : pairedProblem rows964 cols964 requiredD964 requiredS964 =
    MomentData.problem964 := by rfl
theorem leaf964 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows964++rows964))
    (hc : (q.map Prod.snd).Perm (cols964++cols964))
    (hd : ∀ k ∈ requiredD964, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS964, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows964 cols964 requiredD964 requiredS964
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem964_eq] at model
  exact MomentData.excluded964 ds ss model
def rows965 : List Int := [0,1,2,3,4,5,18,22,23,24,25,26,27,28,29]
def cols965 : List Int := [0,1,2,3,4,5,18,22,23,24,25,26,27,28,29]
def requiredD965 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS965 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem965_eq : pairedProblem rows965 cols965 requiredD965 requiredS965 =
    MomentData.problem965 := by rfl
theorem leaf965 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows965++rows965))
    (hc : (q.map Prod.snd).Perm (cols965++cols965))
    (hd : ∀ k ∈ requiredD965, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS965, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows965 cols965 requiredD965 requiredS965
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem965_eq] at model
  exact MomentData.excluded965 ds ss model
def rows966 : List Int := [0,1,2,3,4,5,19,22,23,24,25,26,27,28,29]
def cols966 : List Int := [0,1,2,3,4,5,19,22,23,24,25,26,27,28,29]
def requiredD966 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS966 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem966_eq : pairedProblem rows966 cols966 requiredD966 requiredS966 =
    MomentData.problem966 := by rfl
theorem leaf966 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows966++rows966))
    (hc : (q.map Prod.snd).Perm (cols966++cols966))
    (hd : ∀ k ∈ requiredD966, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS966, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows966 cols966 requiredD966 requiredS966
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem966_eq] at model
  exact MomentData.excluded966 ds ss model
def rows967 : List Int := [0,1,2,3,4,5,20,22,23,24,25,26,27,28,29]
def cols967 : List Int := [0,1,2,3,4,5,20,22,23,24,25,26,27,28,29]
def requiredD967 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS967 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem967_eq : pairedProblem rows967 cols967 requiredD967 requiredS967 =
    MomentData.problem967 := by rfl
theorem leaf967 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows967++rows967))
    (hc : (q.map Prod.snd).Perm (cols967++cols967))
    (hd : ∀ k ∈ requiredD967, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS967, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows967 cols967 requiredD967 requiredS967
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem967_eq] at model
  exact MomentData.excluded967 ds ss model
def rows968 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def cols968 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def requiredD968 : List Int := [-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8]
def requiredS968 : List Int := [15,17,19,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem968_eq : pairedProblem rows968 cols968 requiredD968 requiredS968 =
    MomentData.problem968 := by rfl
theorem leaf968 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows968++rows968))
    (hc : (q.map Prod.snd).Perm (cols968++cols968))
    (hd : ∀ k ∈ requiredD968, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS968, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows968 cols968 requiredD968 requiredS968
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem968_eq] at model
  exact MomentData.excluded968 ds ss model
def rows969 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def cols969 : List Int := [0,1,2,3,4,15,21,22,23,24,25,26,27,28,29]
def requiredD969 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS969 : List Int := [17,19,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem969_eq : pairedProblem rows969 cols969 requiredD969 requiredS969 =
    MomentData.problem969 := by rfl
theorem leaf969 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows969++rows969))
    (hc : (q.map Prod.snd).Perm (cols969++cols969))
    (hd : ∀ k ∈ requiredD969, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS969, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows969 cols969 requiredD969 requiredS969
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem969_eq] at model
  exact MomentData.excluded969 ds ss model
def rows970 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def cols970 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def requiredD970 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS970 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem970_eq : pairedProblem rows970 cols970 requiredD970 requiredS970 =
    MomentData.problem970 := by rfl
theorem leaf970 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows970++rows970))
    (hc : (q.map Prod.snd).Perm (cols970++cols970))
    (hd : ∀ k ∈ requiredD970, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS970, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows970 cols970 requiredD970 requiredS970
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem970_eq] at model
  exact MomentData.excluded970 ds ss model
def rows971 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def cols971 : List Int := [0,1,2,3,4,16,21,22,23,24,25,26,27,28,29]
def requiredD971 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS971 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem971_eq : pairedProblem rows971 cols971 requiredD971 requiredS971 =
    MomentData.problem971 := by rfl
theorem leaf971 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows971++rows971))
    (hc : (q.map Prod.snd).Perm (cols971++cols971))
    (hd : ∀ k ∈ requiredD971, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS971, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows971 cols971 requiredD971 requiredS971
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem971_eq] at model
  exact MomentData.excluded971 ds ss model
def rows972 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def cols972 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def requiredD972 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS972 : List Int := [17,19,20,21,22,23,24,25,26,27,28,29,30,31,33]
theorem problem972_eq : pairedProblem rows972 cols972 requiredD972 requiredS972 =
    MomentData.problem972 := by rfl
theorem leaf972 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows972++rows972))
    (hc : (q.map Prod.snd).Perm (cols972++cols972))
    (hd : ∀ k ∈ requiredD972, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS972, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows972 cols972 requiredD972 requiredS972
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem972_eq] at model
  exact MomentData.excluded972 ds ss model
def rows973 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def cols973 : List Int := [0,1,2,3,4,17,21,22,23,24,25,26,27,28,29]
def requiredD973 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS973 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem973_eq : pairedProblem rows973 cols973 requiredD973 requiredS973 =
    MomentData.problem973 := by rfl
theorem leaf973 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows973++rows973))
    (hc : (q.map Prod.snd).Perm (cols973++cols973))
    (hd : ∀ k ∈ requiredD973, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS973, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows973 cols973 requiredD973 requiredS973
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem973_eq] at model
  exact MomentData.excluded973 ds ss model
def rows974 : List Int := [0,1,2,3,4,18,21,22,23,24,25,26,27,28,29]
def cols974 : List Int := [0,1,2,3,4,18,21,22,23,24,25,26,27,28,29]
def requiredD974 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS974 : List Int := [18,19,20,21,22,23,24,25,26,27,28,29,30,31,32]
theorem problem974_eq : pairedProblem rows974 cols974 requiredD974 requiredS974 =
    MomentData.problem974 := by rfl
theorem leaf974 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows974++rows974))
    (hc : (q.map Prod.snd).Perm (cols974++cols974))
    (hd : ∀ k ∈ requiredD974, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS974, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows974 cols974 requiredD974 requiredS974
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem974_eq] at model
  exact MomentData.excluded974 ds ss model
def rows975 : List Int := [0,1,2,3,16,20,21,22,23,24,25,26,27,28,29]
def cols975 : List Int := [0,1,2,3,16,20,21,22,23,24,25,26,27,28,29]
def requiredD975 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS975 : List Int := [16,17,18,19,20,21,22,23,24,25,26,27,28,29,30]
theorem problem975_eq : pairedProblem rows975 cols975 requiredD975 requiredS975 =
    MomentData.problem975 := by rfl
theorem leaf975 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows975++rows975))
    (hc : (q.map Prod.snd).Perm (cols975++cols975))
    (hd : ∀ k ∈ requiredD975, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS975, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows975 cols975 requiredD975 requiredS975
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem975_eq] at model
  exact MomentData.excluded975 ds ss model
def rows976 : List Int := [0,1,2,3,4,5,7,15,23,24,25,26,27,28,29]
def cols976 : List Int := [0,1,2,3,4,5,7,15,23,24,25,26,27,28,29]
def requiredD976 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS976 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem976_eq : pairedProblem rows976 cols976 requiredD976 requiredS976 =
    MomentData.problem976 := by rfl
theorem leaf976 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows976++rows976))
    (hc : (q.map Prod.snd).Perm (cols976++cols976))
    (hd : ∀ k ∈ requiredD976, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS976, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows976 cols976 requiredD976 requiredS976
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem976_eq] at model
  exact MomentData.excluded976 ds ss model
def rows977 : List Int := [0,1,2,3,4,5,8,14,23,24,25,26,27,28,29]
def cols977 : List Int := [0,1,2,3,4,5,8,14,23,24,25,26,27,28,29]
def requiredD977 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS977 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem977_eq : pairedProblem rows977 cols977 requiredD977 requiredS977 =
    MomentData.problem977 := by rfl
theorem leaf977 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows977++rows977))
    (hc : (q.map Prod.snd).Perm (cols977++cols977))
    (hd : ∀ k ∈ requiredD977, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS977, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows977 cols977 requiredD977 requiredS977
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem977_eq] at model
  exact MomentData.excluded977 ds ss model
def rows978 : List Int := [0,1,2,3,4,5,10,17,23,24,25,26,27,28,29]
def cols978 : List Int := [0,1,2,3,4,5,10,17,23,24,25,26,27,28,29]
def requiredD978 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS978 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem978_eq : pairedProblem rows978 cols978 requiredD978 requiredS978 =
    MomentData.problem978 := by rfl
theorem leaf978 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows978++rows978))
    (hc : (q.map Prod.snd).Perm (cols978++cols978))
    (hd : ∀ k ∈ requiredD978, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS978, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows978 cols978 requiredD978 requiredS978
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem978_eq] at model
  exact MomentData.excluded978 ds ss model
def rows979 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def cols979 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def requiredD979 : List Int := [-13,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,13]
def requiredS979 : List Int := [18,20,22,23,24,26,27,28,29,30,32,33,34,36,38]
theorem problem979_eq : pairedProblem rows979 cols979 requiredD979 requiredS979 =
    MomentData.problem979 := by rfl
theorem leaf979 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows979++rows979))
    (hc : (q.map Prod.snd).Perm (cols979++cols979))
    (hd : ∀ k ∈ requiredD979, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS979, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows979 cols979 requiredD979 requiredS979
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem979_eq] at model
  exact MomentData.excluded979 ds ss model
def rows980 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def cols980 : List Int := [0,1,2,3,4,5,10,18,23,24,25,26,27,28,29]
def requiredD980 : List Int := [-10,-8,-6,-5,-4,-2,-1,0,1,2,4,5,6,8,10]
def requiredS980 : List Int := [15,19,21,23,25,26,27,28,29,30,31,33,35,37,41]
theorem problem980_eq : pairedProblem rows980 cols980 requiredD980 requiredS980 =
    MomentData.problem980 := by rfl
theorem leaf980 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows980++rows980))
    (hc : (q.map Prod.snd).Perm (cols980++cols980))
    (hd : ∀ k ∈ requiredD980, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS980, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows980 cols980 requiredD980 requiredS980
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem980_eq] at model
  exact MomentData.excluded980 ds ss model
def rows981 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols981 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD981 : List Int := [-12,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,12]
def requiredS981 : List Int := [19,21,22,23,25,26,27,28,29,30,31,33,34,35,37]
theorem problem981_eq : pairedProblem rows981 cols981 requiredD981 requiredS981 =
    MomentData.problem981 := by rfl
theorem leaf981 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows981++rows981))
    (hc : (q.map Prod.snd).Perm (cols981++cols981))
    (hd : ∀ k ∈ requiredD981, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS981, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows981 cols981 requiredD981 requiredS981
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem981_eq] at model
  exact MomentData.excluded981 ds ss model
def rows982 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols982 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD982 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS982 : List Int := [16,20,22,24,25,26,27,28,29,30,31,32,34,36,40]
theorem problem982_eq : pairedProblem rows982 cols982 requiredD982 requiredS982 =
    MomentData.problem982 := by rfl
theorem leaf982 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows982++rows982))
    (hc : (q.map Prod.snd).Perm (cols982++cols982))
    (hd : ∀ k ∈ requiredD982, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS982, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows982 cols982 requiredD982 requiredS982
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem982_eq] at model
  exact MomentData.excluded982 ds ss model
def rows983 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols983 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD983 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS983 : List Int := [18,20,22,24,25,26,27,28,29,30,31,32,34,36,38]
theorem problem983_eq : pairedProblem rows983 cols983 requiredD983 requiredS983 =
    MomentData.problem983 := by rfl
theorem leaf983 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows983++rows983))
    (hc : (q.map Prod.snd).Perm (cols983++cols983))
    (hd : ∀ k ∈ requiredD983, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS983, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows983 cols983 requiredD983 requiredS983
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem983_eq] at model
  exact MomentData.excluded983 ds ss model
def rows984 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def cols984 : List Int := [0,1,2,3,4,5,11,17,23,24,25,26,27,28,29]
def requiredD984 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS984 : List Int := [19,21,23,24,25,26,27,28,29,30,31,32,33,35,37]
theorem problem984_eq : pairedProblem rows984 cols984 requiredD984 requiredS984 =
    MomentData.problem984 := by rfl
theorem leaf984 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows984++rows984))
    (hc : (q.map Prod.snd).Perm (cols984++cols984))
    (hd : ∀ k ∈ requiredD984, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS984, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows984 cols984 requiredD984 requiredS984
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem984_eq] at model
  exact MomentData.excluded984 ds ss model
def rows985 : List Int := [0,1,2,3,4,5,11,18,23,24,25,26,27,28,29]
def cols985 : List Int := [0,1,2,3,4,5,11,18,23,24,25,26,27,28,29]
def requiredD985 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS985 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem985_eq : pairedProblem rows985 cols985 requiredD985 requiredS985 =
    MomentData.problem985 := by rfl
theorem leaf985 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows985++rows985))
    (hc : (q.map Prod.snd).Perm (cols985++cols985))
    (hd : ∀ k ∈ requiredD985, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS985, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows985 cols985 requiredD985 requiredS985
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem985_eq] at model
  exact MomentData.excluded985 ds ss model
def rows986 : List Int := [0,1,2,3,4,5,12,17,23,24,25,26,27,28,29]
def cols986 : List Int := [0,1,2,3,4,5,12,17,23,24,25,26,27,28,29]
def requiredD986 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS986 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem986_eq : pairedProblem rows986 cols986 requiredD986 requiredS986 =
    MomentData.problem986 := by rfl
theorem leaf986 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows986++rows986))
    (hc : (q.map Prod.snd).Perm (cols986++cols986))
    (hd : ∀ k ∈ requiredD986, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS986, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows986 cols986 requiredD986 requiredS986
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem986_eq] at model
  exact MomentData.excluded986 ds ss model
def rows987 : List Int := [0,1,2,3,4,5,14,17,23,24,25,26,27,28,29]
def cols987 : List Int := [0,1,2,3,4,5,14,17,23,24,25,26,27,28,29]
def requiredD987 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS987 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem987_eq : pairedProblem rows987 cols987 requiredD987 requiredS987 =
    MomentData.problem987 := by rfl
theorem leaf987 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows987++rows987))
    (hc : (q.map Prod.snd).Perm (cols987++cols987))
    (hd : ∀ k ∈ requiredD987, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS987, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows987 cols987 requiredD987 requiredS987
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem987_eq] at model
  exact MomentData.excluded987 ds ss model
def rows988 : List Int := [0,1,2,3,4,5,14,18,23,24,25,26,27,28,29]
def cols988 : List Int := [0,1,2,3,4,5,14,18,23,24,25,26,27,28,29]
def requiredD988 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS988 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem988_eq : pairedProblem rows988 cols988 requiredD988 requiredS988 =
    MomentData.problem988 := by rfl
theorem leaf988 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows988++rows988))
    (hc : (q.map Prod.snd).Perm (cols988++cols988))
    (hd : ∀ k ∈ requiredD988, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS988, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows988 cols988 requiredD988 requiredS988
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem988_eq] at model
  exact MomentData.excluded988 ds ss model
def rows989 : List Int := [0,1,2,3,4,5,14,19,23,24,25,26,27,28,29]
def cols989 : List Int := [0,1,2,3,4,5,14,19,23,24,25,26,27,28,29]
def requiredD989 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS989 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem989_eq : pairedProblem rows989 cols989 requiredD989 requiredS989 =
    MomentData.problem989 := by rfl
theorem leaf989 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows989++rows989))
    (hc : (q.map Prod.snd).Perm (cols989++cols989))
    (hd : ∀ k ∈ requiredD989, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS989, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows989 cols989 requiredD989 requiredS989
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem989_eq] at model
  exact MomentData.excluded989 ds ss model
def rows990 : List Int := [0,1,2,3,4,5,13,21,23,24,25,26,27,28,29]
def cols990 : List Int := [0,1,2,3,4,5,13,21,23,24,25,26,27,28,29]
def requiredD990 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS990 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem990_eq : pairedProblem rows990 cols990 requiredD990 requiredS990 =
    MomentData.problem990 := by rfl
theorem leaf990 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows990++rows990))
    (hc : (q.map Prod.snd).Perm (cols990++cols990))
    (hd : ∀ k ∈ requiredD990, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS990, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows990 cols990 requiredD990 requiredS990
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem990_eq] at model
  exact MomentData.excluded990 ds ss model
def rows991 : List Int := [0,1,2,3,4,5,14,20,23,24,25,26,27,28,29]
def cols991 : List Int := [0,1,2,3,4,5,14,20,23,24,25,26,27,28,29]
def requiredD991 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS991 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem991_eq : pairedProblem rows991 cols991 requiredD991 requiredS991 =
    MomentData.problem991 := by rfl
theorem leaf991 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows991++rows991))
    (hc : (q.map Prod.snd).Perm (cols991++cols991))
    (hd : ∀ k ∈ requiredD991, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS991, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows991 cols991 requiredD991 requiredS991
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem991_eq] at model
  exact MomentData.excluded991 ds ss model
def rows992 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def cols992 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def requiredD992 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS992 : List Int := [19,22,23,24,25,26,27,28,29,30,31,32,33,34,37]
theorem problem992_eq : pairedProblem rows992 cols992 requiredD992 requiredS992 =
    MomentData.problem992 := by rfl
theorem leaf992 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows992++rows992))
    (hc : (q.map Prod.snd).Perm (cols992++cols992))
    (hd : ∀ k ∈ requiredD992, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS992, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows992 cols992 requiredD992 requiredS992
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem992_eq] at model
  exact MomentData.excluded992 ds ss model
def rows993 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def cols993 : List Int := [0,1,2,3,4,5,14,21,23,24,25,26,27,28,29]
def requiredD993 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS993 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem993_eq : pairedProblem rows993 cols993 requiredD993 requiredS993 =
    MomentData.problem993 := by rfl
theorem leaf993 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows993++rows993))
    (hc : (q.map Prod.snd).Perm (cols993++cols993))
    (hd : ∀ k ∈ requiredD993, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS993, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows993 cols993 requiredD993 requiredS993
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem993_eq] at model
  exact MomentData.excluded993 ds ss model
def rows994 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def cols994 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def requiredD994 : List Int := [-9,-7,-6,-5,-3,-2,-1,0,1,2,3,5,6,7,9]
def requiredS994 : List Int := [14,18,20,22,23,24,25,26,27,28,29,30,32,34,38]
theorem problem994_eq : pairedProblem rows994 cols994 requiredD994 requiredS994 =
    MomentData.problem994 := by rfl
theorem leaf994 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows994++rows994))
    (hc : (q.map Prod.snd).Perm (cols994++cols994))
    (hd : ∀ k ∈ requiredD994, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS994, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows994 cols994 requiredD994 requiredS994
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem994_eq] at model
  exact MomentData.excluded994 ds ss model
def rows995 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def cols995 : List Int := [0,1,2,3,4,10,16,22,23,24,25,26,27,28,29]
def requiredD995 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS995 : List Int := [16,18,20,22,23,24,25,26,27,28,29,30,32,34,36]
theorem problem995_eq : pairedProblem rows995 cols995 requiredD995 requiredS995 =
    MomentData.problem995 := by rfl
theorem leaf995 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows995++rows995))
    (hc : (q.map Prod.snd).Perm (cols995++cols995))
    (hd : ∀ k ∈ requiredD995, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS995, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows995 cols995 requiredD995 requiredS995
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem995_eq] at model
  exact MomentData.excluded995 ds ss model
def rows996 : List Int := [0,1,2,3,4,10,17,22,23,24,25,26,27,28,29]
def cols996 : List Int := [0,1,2,3,4,10,17,22,23,24,25,26,27,28,29]
def requiredD996 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS996 : List Int := [17,19,21,23,24,25,26,27,28,29,30,31,33,35,37]
theorem problem996_eq : pairedProblem rows996 cols996 requiredD996 requiredS996 =
    MomentData.problem996 := by rfl
theorem leaf996 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows996++rows996))
    (hc : (q.map Prod.snd).Perm (cols996++cols996))
    (hd : ∀ k ∈ requiredD996, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS996, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows996 cols996 requiredD996 requiredS996
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem996_eq] at model
  exact MomentData.excluded996 ds ss model
def rows997 : List Int := [0,1,2,3,4,11,16,22,23,24,25,26,27,28,29]
def cols997 : List Int := [0,1,2,3,4,11,16,22,23,24,25,26,27,28,29]
def requiredD997 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS997 : List Int := [18,20,22,23,24,25,26,27,28,29,30,31,32,34,36]
theorem problem997_eq : pairedProblem rows997 cols997 requiredD997 requiredS997 =
    MomentData.problem997 := by rfl
theorem leaf997 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows997++rows997))
    (hc : (q.map Prod.snd).Perm (cols997++cols997))
    (hd : ∀ k ∈ requiredD997, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS997, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows997 cols997 requiredD997 requiredS997
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem997_eq] at model
  exact MomentData.excluded997 ds ss model
def rows998 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def cols998 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def requiredD998 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS998 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem998_eq : pairedProblem rows998 cols998 requiredD998 requiredS998 =
    MomentData.problem998 := by rfl
theorem leaf998 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows998++rows998))
    (hc : (q.map Prod.snd).Perm (cols998++cols998))
    (hd : ∀ k ∈ requiredD998, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS998, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows998 cols998 requiredD998 requiredS998
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem998_eq] at model
  exact MomentData.excluded998 ds ss model
def rows999 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def cols999 : List Int := [0,1,2,3,4,13,17,22,23,24,25,26,27,28,29]
def requiredD999 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS999 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem999_eq : pairedProblem rows999 cols999 requiredD999 requiredS999 =
    MomentData.problem999 := by rfl
theorem leaf999 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows999++rows999))
    (hc : (q.map Prod.snd).Perm (cols999++cols999))
    (hd : ∀ k ∈ requiredD999, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS999, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows999 cols999 requiredD999 requiredS999
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem999_eq] at model
  exact MomentData.excluded999 ds ss model
def rows1000 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def cols1000 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def requiredD1000 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS1000 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem1000_eq : pairedProblem rows1000 cols1000 requiredD1000 requiredS1000 =
    MomentData.problem1000 := by rfl
theorem leaf1000 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1000++rows1000))
    (hc : (q.map Prod.snd).Perm (cols1000++cols1000))
    (hd : ∀ k ∈ requiredD1000, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1000, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1000 cols1000 requiredD1000 requiredS1000
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1000_eq] at model
  exact MomentData.excluded1000 ds ss model
def rows1001 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def cols1001 : List Int := [0,1,2,3,4,13,18,22,23,24,25,26,27,28,29]
def requiredD1001 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1001 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1001_eq : pairedProblem rows1001 cols1001 requiredD1001 requiredS1001 =
    MomentData.problem1001 := by rfl
theorem leaf1001 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1001++rows1001))
    (hc : (q.map Prod.snd).Perm (cols1001++cols1001))
    (hd : ∀ k ∈ requiredD1001, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1001, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1001 cols1001 requiredD1001 requiredS1001
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1001_eq] at model
  exact MomentData.excluded1001 ds ss model
def rows1002 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def cols1002 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def requiredD1002 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS1002 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem1002_eq : pairedProblem rows1002 cols1002 requiredD1002 requiredS1002 =
    MomentData.problem1002 := by rfl
theorem leaf1002 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1002++rows1002))
    (hc : (q.map Prod.snd).Perm (cols1002++cols1002))
    (hd : ∀ k ∈ requiredD1002, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1002, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1002 cols1002 requiredD1002 requiredS1002
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1002_eq] at model
  exact MomentData.excluded1002 ds ss model
def rows1003 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def cols1003 : List Int := [0,1,2,3,4,13,19,22,23,24,25,26,27,28,29]
def requiredD1003 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1003 : List Int := [19,20,21,22,23,24,25,26,27,28,29,30,31,32,33]
theorem problem1003_eq : pairedProblem rows1003 cols1003 requiredD1003 requiredS1003 =
    MomentData.problem1003 := by rfl
theorem leaf1003 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1003++rows1003))
    (hc : (q.map Prod.snd).Perm (cols1003++cols1003))
    (hd : ∀ k ∈ requiredD1003, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1003, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1003 cols1003 requiredD1003 requiredS1003
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1003_eq] at model
  exact MomentData.excluded1003 ds ss model
def rows1004 : List Int := [0,1,2,3,4,13,20,22,23,24,25,26,27,28,29]
def cols1004 : List Int := [0,1,2,3,4,13,20,22,23,24,25,26,27,28,29]
def requiredD1004 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS1004 : List Int := [17,20,21,22,23,24,25,26,27,28,29,30,31,32,35]
theorem problem1004_eq : pairedProblem rows1004 cols1004 requiredD1004 requiredS1004 =
    MomentData.problem1004 := by rfl
theorem leaf1004 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1004++rows1004))
    (hc : (q.map Prod.snd).Perm (cols1004++cols1004))
    (hd : ∀ k ∈ requiredD1004, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1004, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1004 cols1004 requiredD1004 requiredS1004
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1004_eq] at model
  exact MomentData.excluded1004 ds ss model
def rows1005 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def cols1005 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def requiredD1005 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS1005 : List Int := [15,18,19,20,21,22,23,24,25,26,27,28,29,30,33]
theorem problem1005_eq : pairedProblem rows1005 cols1005 requiredD1005 requiredS1005 =
    MomentData.problem1005 := by rfl
theorem leaf1005 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1005++rows1005))
    (hc : (q.map Prod.snd).Perm (cols1005++cols1005))
    (hd : ∀ k ∈ requiredD1005, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1005, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1005 cols1005 requiredD1005 requiredS1005
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1005_eq] at model
  exact MomentData.excluded1005 ds ss model
def rows1006 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def cols1006 : List Int := [0,1,2,3,12,17,21,22,23,24,25,26,27,28,29]
def requiredD1006 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1006 : List Int := [17,18,19,20,21,22,23,24,25,26,27,28,29,30,31]
theorem problem1006_eq : pairedProblem rows1006 cols1006 requiredD1006 requiredS1006 =
    MomentData.problem1006 := by rfl
theorem leaf1006 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1006++rows1006))
    (hc : (q.map Prod.snd).Perm (cols1006++cols1006))
    (hd : ∀ k ∈ requiredD1006, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1006, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1006 cols1006 requiredD1006 requiredS1006
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1006_eq] at model
  exact MomentData.excluded1006 ds ss model
def rows1007 : List Int := [0,1,2,3,12,18,21,22,23,24,25,26,27,28,29]
def cols1007 : List Int := [0,1,2,3,12,18,21,22,23,24,25,26,27,28,29]
def requiredD1007 : List Int := [-9,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,9]
def requiredS1007 : List Int := [15,18,19,20,21,22,23,24,25,26,27,28,29,30,33]
theorem problem1007_eq : pairedProblem rows1007 cols1007 requiredD1007 requiredS1007 =
    MomentData.problem1007 := by rfl
theorem leaf1007 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1007++rows1007))
    (hc : (q.map Prod.snd).Perm (cols1007++cols1007))
    (hd : ∀ k ∈ requiredD1007, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1007, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1007 cols1007 requiredD1007 requiredS1007
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1007_eq] at model
  exact MomentData.excluded1007 ds ss model
def rows1008 : List Int := [0,1,2,3,4,5,9,15,20,24,25,26,27,28,29]
def cols1008 : List Int := [0,1,2,3,4,5,9,15,20,24,25,26,27,28,29]
def requiredD1008 : List Int := [-12,-10,-8,-6,-4,-2,-1,0,1,2,4,6,8,10,12]
def requiredS1008 : List Int := [17,19,21,23,25,27,28,29,30,31,33,35,37,39,41]
theorem problem1008_eq : pairedProblem rows1008 cols1008 requiredD1008 requiredS1008 =
    MomentData.problem1008 := by rfl
theorem leaf1008 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1008++rows1008))
    (hc : (q.map Prod.snd).Perm (cols1008++cols1008))
    (hd : ∀ k ∈ requiredD1008, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1008, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1008 cols1008 requiredD1008 requiredS1008
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1008_eq] at model
  exact MomentData.excluded1008 ds ss model
def rows1009 : List Int := [0,1,2,3,4,5,10,15,19,24,25,26,27,28,29]
def cols1009 : List Int := [0,1,2,3,4,5,10,15,19,24,25,26,27,28,29]
def requiredD1009 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1009 : List Int := [18,20,22,24,26,27,28,29,30,31,32,34,36,38,40]
theorem problem1009_eq : pairedProblem rows1009 cols1009 requiredD1009 requiredS1009 =
    MomentData.problem1009 := by rfl
theorem leaf1009 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1009++rows1009))
    (hc : (q.map Prod.snd).Perm (cols1009++cols1009))
    (hd : ∀ k ∈ requiredD1009, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1009, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1009 cols1009 requiredD1009 requiredS1009
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1009_eq] at model
  exact MomentData.excluded1009 ds ss model
def rows1010 : List Int := [0,1,2,3,4,5,10,16,19,24,25,26,27,28,29]
def cols1010 : List Int := [0,1,2,3,4,5,10,16,19,24,25,26,27,28,29]
def requiredD1010 : List Int := [-11,-9,-7,-5,-3,-2,-1,0,1,2,3,5,7,9,11]
def requiredS1010 : List Int := [18,20,22,24,26,27,28,29,30,31,32,34,36,38,40]
theorem problem1010_eq : pairedProblem rows1010 cols1010 requiredD1010 requiredS1010 =
    MomentData.problem1010 := by rfl
theorem leaf1010 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1010++rows1010))
    (hc : (q.map Prod.snd).Perm (cols1010++cols1010))
    (hd : ∀ k ∈ requiredD1010, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1010, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1010 cols1010 requiredD1010 requiredS1010
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1010_eq] at model
  exact MomentData.excluded1010 ds ss model
def rows1011 : List Int := [0,1,2,3,4,5,11,15,18,24,25,26,27,28,29]
def cols1011 : List Int := [0,1,2,3,4,5,11,15,18,24,25,26,27,28,29]
def requiredD1011 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1011 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1011_eq : pairedProblem rows1011 cols1011 requiredD1011 requiredS1011 =
    MomentData.problem1011 := by rfl
theorem leaf1011 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1011++rows1011))
    (hc : (q.map Prod.snd).Perm (cols1011++cols1011))
    (hd : ∀ k ∈ requiredD1011, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1011, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1011 cols1011 requiredD1011 requiredS1011
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1011_eq] at model
  exact MomentData.excluded1011 ds ss model
def rows1012 : List Int := [0,1,2,3,4,5,11,16,18,24,25,26,27,28,29]
def cols1012 : List Int := [0,1,2,3,4,5,11,16,18,24,25,26,27,28,29]
def requiredD1012 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1012 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1012_eq : pairedProblem rows1012 cols1012 requiredD1012 requiredS1012 =
    MomentData.problem1012 := by rfl
theorem leaf1012 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1012++rows1012))
    (hc : (q.map Prod.snd).Perm (cols1012++cols1012))
    (hd : ∀ k ∈ requiredD1012, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1012, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1012 cols1012 requiredD1012 requiredS1012
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1012_eq] at model
  exact MomentData.excluded1012 ds ss model
def rows1013 : List Int := [0,1,2,3,4,5,12,15,17,24,25,26,27,28,29]
def cols1013 : List Int := [0,1,2,3,4,5,12,15,17,24,25,26,27,28,29]
def requiredD1013 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1013 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1013_eq : pairedProblem rows1013 cols1013 requiredD1013 requiredS1013 =
    MomentData.problem1013 := by rfl
theorem leaf1013 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1013++rows1013))
    (hc : (q.map Prod.snd).Perm (cols1013++cols1013))
    (hd : ∀ k ∈ requiredD1013, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1013, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1013 cols1013 requiredD1013 requiredS1013
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1013_eq] at model
  exact MomentData.excluded1013 ds ss model
def rows1014 : List Int := [0,1,2,3,4,5,12,16,17,24,25,26,27,28,29]
def cols1014 : List Int := [0,1,2,3,4,5,12,16,17,24,25,26,27,28,29]
def requiredD1014 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1014 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1014_eq : pairedProblem rows1014 cols1014 requiredD1014 requiredS1014 =
    MomentData.problem1014 := by rfl
theorem leaf1014 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1014++rows1014))
    (hc : (q.map Prod.snd).Perm (cols1014++cols1014))
    (hd : ∀ k ∈ requiredD1014, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1014, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1014 cols1014 requiredD1014 requiredS1014
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1014_eq] at model
  exact MomentData.excluded1014 ds ss model
def rows1015 : List Int := [0,1,2,3,4,5,11,17,18,24,25,26,27,28,29]
def cols1015 : List Int := [0,1,2,3,4,5,11,17,18,24,25,26,27,28,29]
def requiredD1015 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1015 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1015_eq : pairedProblem rows1015 cols1015 requiredD1015 requiredS1015 =
    MomentData.problem1015 := by rfl
theorem leaf1015 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1015++rows1015))
    (hc : (q.map Prod.snd).Perm (cols1015++cols1015))
    (hd : ∀ k ∈ requiredD1015, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1015, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1015 cols1015 requiredD1015 requiredS1015
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1015_eq] at model
  exact MomentData.excluded1015 ds ss model
def rows1016 : List Int := [0,1,2,3,4,5,12,17,18,24,25,26,27,28,29]
def cols1016 : List Int := [0,1,2,3,4,5,12,17,18,24,25,26,27,28,29]
def requiredD1016 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1016 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1016_eq : pairedProblem rows1016 cols1016 requiredD1016 requiredS1016 =
    MomentData.problem1016 := by rfl
theorem leaf1016 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1016++rows1016))
    (hc : (q.map Prod.snd).Perm (cols1016++cols1016))
    (hd : ∀ k ∈ requiredD1016, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1016, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1016 cols1016 requiredD1016 requiredS1016
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1016_eq] at model
  exact MomentData.excluded1016 ds ss model
def rows1017 : List Int := [0,1,2,3,4,5,11,18,19,24,25,26,27,28,29]
def cols1017 : List Int := [0,1,2,3,4,5,11,18,19,24,25,26,27,28,29]
def requiredD1017 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1017 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1017_eq : pairedProblem rows1017 cols1017 requiredD1017 requiredS1017 =
    MomentData.problem1017 := by rfl
theorem leaf1017 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1017++rows1017))
    (hc : (q.map Prod.snd).Perm (cols1017++cols1017))
    (hd : ∀ k ∈ requiredD1017, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1017, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1017 cols1017 requiredD1017 requiredS1017
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1017_eq] at model
  exact MomentData.excluded1017 ds ss model
def rows1018 : List Int := [0,1,2,3,4,5,12,17,19,24,25,26,27,28,29]
def cols1018 : List Int := [0,1,2,3,4,5,12,17,19,24,25,26,27,28,29]
def requiredD1018 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1018 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1018_eq : pairedProblem rows1018 cols1018 requiredD1018 requiredS1018 =
    MomentData.problem1018 := by rfl
theorem leaf1018 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1018++rows1018))
    (hc : (q.map Prod.snd).Perm (cols1018++cols1018))
    (hd : ∀ k ∈ requiredD1018, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1018, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1018 cols1018 requiredD1018 requiredS1018
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1018_eq] at model
  exact MomentData.excluded1018 ds ss model
def rows1019 : List Int := [0,1,2,3,4,5,13,16,19,24,25,26,27,28,29]
def cols1019 : List Int := [0,1,2,3,4,5,13,16,19,24,25,26,27,28,29]
def requiredD1019 : List Int := [-8,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,8]
def requiredS1019 : List Int := [21,23,24,25,26,27,28,29,30,31,32,33,34,35,37]
theorem problem1019_eq : pairedProblem rows1019 cols1019 requiredD1019 requiredS1019 =
    MomentData.problem1019 := by rfl
theorem leaf1019 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1019++rows1019))
    (hc : (q.map Prod.snd).Perm (cols1019++cols1019))
    (hd : ∀ k ∈ requiredD1019, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1019, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1019 cols1019 requiredD1019 requiredS1019
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1019_eq] at model
  exact MomentData.excluded1019 ds ss model
def rows1020 : List Int := [0,1,2,3,4,5,11,18,20,24,25,26,27,28,29]
def cols1020 : List Int := [0,1,2,3,4,5,11,18,20,24,25,26,27,28,29]
def requiredD1020 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1020 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1020_eq : pairedProblem rows1020 cols1020 requiredD1020 requiredS1020 =
    MomentData.problem1020 := by rfl
theorem leaf1020 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1020++rows1020))
    (hc : (q.map Prod.snd).Perm (cols1020++cols1020))
    (hd : ∀ k ∈ requiredD1020, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1020, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1020 cols1020 requiredD1020 requiredS1020
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1020_eq] at model
  exact MomentData.excluded1020 ds ss model
def rows1021 : List Int := [0,1,2,3,4,5,12,17,20,24,25,26,27,28,29]
def cols1021 : List Int := [0,1,2,3,4,5,12,17,20,24,25,26,27,28,29]
def requiredD1021 : List Int := [-9,-7,-5,-4,-3,-2,-1,0,1,2,3,4,5,7,9]
def requiredS1021 : List Int := [20,22,24,25,26,27,28,29,30,31,32,33,34,36,38]
theorem problem1021_eq : pairedProblem rows1021 cols1021 requiredD1021 requiredS1021 =
    MomentData.problem1021 := by rfl
theorem leaf1021 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1021++rows1021))
    (hc : (q.map Prod.snd).Perm (cols1021++cols1021))
    (hd : ∀ k ∈ requiredD1021, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1021, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1021 cols1021 requiredD1021 requiredS1021
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1021_eq] at model
  exact MomentData.excluded1021 ds ss model
def rows1022 : List Int := [0,1,2,3,4,5,14,15,20,24,25,26,27,28,29]
def cols1022 : List Int := [0,1,2,3,4,5,14,15,20,24,25,26,27,28,29]
def requiredD1022 : List Int := [-10,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,10]
def requiredS1022 : List Int := [19,23,24,25,26,27,28,29,30,31,32,33,34,35,39]
theorem problem1022_eq : pairedProblem rows1022 cols1022 requiredD1022 requiredS1022 =
    MomentData.problem1022 := by rfl
theorem leaf1022 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1022++rows1022))
    (hc : (q.map Prod.snd).Perm (cols1022++cols1022))
    (hd : ∀ k ∈ requiredD1022, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1022, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1022 cols1022 requiredD1022 requiredS1022
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1022_eq] at model
  exact MomentData.excluded1022 ds ss model
def rows1023 : List Int := [0,1,2,3,4,5,11,18,21,24,25,26,27,28,29]
def cols1023 : List Int := [0,1,2,3,4,5,11,18,21,24,25,26,27,28,29]
def requiredD1023 : List Int := [-10,-8,-6,-4,-3,-2,-1,0,1,2,3,4,6,8,10]
def requiredS1023 : List Int := [19,21,23,25,26,27,28,29,30,31,32,33,35,37,39]
theorem problem1023_eq : pairedProblem rows1023 cols1023 requiredD1023 requiredS1023 =
    MomentData.problem1023 := by rfl
theorem leaf1023 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1023++rows1023))
    (hc : (q.map Prod.snd).Perm (cols1023++cols1023))
    (hd : ∀ k ∈ requiredD1023, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1023, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1023 cols1023 requiredD1023 requiredS1023
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1023_eq] at model
  exact MomentData.excluded1023 ds ss model
#print axioms leaf896
end Gardner.Kernel.MomentContexts
