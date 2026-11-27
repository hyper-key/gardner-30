import Gardner.kernel.MomentData
import Gardner.kernel.PairedResiduals
namespace Gardner.Kernel.MomentContexts
open MomentCuts
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000000
def rows1920 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols1920 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD1920 : List Int := [-24,-20,-16,-12,-8,-4,-3,0,3,4,8,12,16,20,24]
def requiredS1920 : List Int := [7,11,15,19,23,27,28,31,35,39,43,47,51,55]
theorem problem1920_eq : pairedProblem rows1920 cols1920 requiredD1920 requiredS1920 =
    MomentData.problem1920 := by rfl
theorem leaf1920 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1920++rows1920))
    (hc : (q.map Prod.snd).Perm (cols1920++cols1920))
    (hd : ∀ k ∈ requiredD1920, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1920, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1920 cols1920 requiredD1920 requiredS1920
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1920_eq] at model
  exact MomentData.excluded1920 ds ss model
def rows1921 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def cols1921 : List Int := [1,2,5,6,9,10,13,14,17,18,21,22,25,26,29]
def requiredD1921 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS1921 : List Int := [3,7,11,15,19,23,27,28,31,35,39,43,47,51]
theorem problem1921_eq : pairedProblem rows1921 cols1921 requiredD1921 requiredS1921 =
    MomentData.problem1921 := by rfl
theorem leaf1921 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1921++rows1921))
    (hc : (q.map Prod.snd).Perm (cols1921++cols1921))
    (hd : ∀ k ∈ requiredD1921, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1921, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1921 cols1921 requiredD1921 requiredS1921
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1921_eq] at model
  exact MomentData.excluded1921 ds ss model
def rows1922 : List Int := [1,2,4,5,8,11,13,14,17,20,23,24,26,27,29]
def cols1922 : List Int := [1,2,4,5,8,11,13,14,17,20,23,24,26,27,29]
def requiredD1922 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1922 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1922_eq : pairedProblem rows1922 cols1922 requiredD1922 requiredS1922 =
    MomentData.problem1922 := by rfl
theorem leaf1922 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1922++rows1922))
    (hc : (q.map Prod.snd).Perm (cols1922++cols1922))
    (hd : ∀ k ∈ requiredD1922, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1922, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1922 cols1922 requiredD1922 requiredS1922
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1922_eq] at model
  exact MomentData.excluded1922 ds ss model
def rows1923 : List Int := [1,2,4,5,8,11,13,14,17,20,23,24,26,27,29]
def cols1923 : List Int := [1,2,4,5,8,11,13,14,17,20,23,24,26,27,29]
def requiredD1923 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1923 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1923_eq : pairedProblem rows1923 cols1923 requiredD1923 requiredS1923 =
    MomentData.problem1923 := by rfl
theorem leaf1923 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1923++rows1923))
    (hc : (q.map Prod.snd).Perm (cols1923++cols1923))
    (hd : ∀ k ∈ requiredD1923, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1923, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1923 cols1923 requiredD1923 requiredS1923
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1923_eq] at model
  exact MomentData.excluded1923 ds ss model
def rows1924 : List Int := [1,2,4,5,8,11,14,15,17,20,23,24,26,27,29]
def cols1924 : List Int := [1,2,4,5,8,11,14,15,17,20,23,24,26,27,29]
def requiredD1924 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1924 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1924_eq : pairedProblem rows1924 cols1924 requiredD1924 requiredS1924 =
    MomentData.problem1924 := by rfl
theorem leaf1924 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1924++rows1924))
    (hc : (q.map Prod.snd).Perm (cols1924++cols1924))
    (hd : ∀ k ∈ requiredD1924, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1924, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1924 cols1924 requiredD1924 requiredS1924
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1924_eq] at model
  exact MomentData.excluded1924 ds ss model
def rows1925 : List Int := [1,2,4,5,8,11,14,15,17,20,23,24,26,27,29]
def cols1925 : List Int := [1,2,4,5,8,11,14,15,17,20,23,24,26,27,29]
def requiredD1925 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1925 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1925_eq : pairedProblem rows1925 cols1925 requiredD1925 requiredS1925 =
    MomentData.problem1925 := by rfl
theorem leaf1925 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1925++rows1925))
    (hc : (q.map Prod.snd).Perm (cols1925++cols1925))
    (hd : ∀ k ∈ requiredD1925, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1925, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1925 cols1925 requiredD1925 requiredS1925
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1925_eq] at model
  exact MomentData.excluded1925 ds ss model
def rows1926 : List Int := [1,2,4,5,8,11,14,16,17,20,23,24,26,27,29]
def cols1926 : List Int := [1,2,4,5,8,11,14,16,17,20,23,24,26,27,29]
def requiredD1926 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1926 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1926_eq : pairedProblem rows1926 cols1926 requiredD1926 requiredS1926 =
    MomentData.problem1926 := by rfl
theorem leaf1926 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1926++rows1926))
    (hc : (q.map Prod.snd).Perm (cols1926++cols1926))
    (hd : ∀ k ∈ requiredD1926, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1926, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1926 cols1926 requiredD1926 requiredS1926
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1926_eq] at model
  exact MomentData.excluded1926 ds ss model
def rows1927 : List Int := [1,2,4,5,8,11,14,16,17,20,23,24,26,27,29]
def cols1927 : List Int := [1,2,4,5,8,11,14,16,17,20,23,24,26,27,29]
def requiredD1927 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1927 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1927_eq : pairedProblem rows1927 cols1927 requiredD1927 requiredS1927 =
    MomentData.problem1927 := by rfl
theorem leaf1927 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1927++rows1927))
    (hc : (q.map Prod.snd).Perm (cols1927++cols1927))
    (hd : ∀ k ∈ requiredD1927, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1927, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1927 cols1927 requiredD1927 requiredS1927
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1927_eq] at model
  exact MomentData.excluded1927 ds ss model
def rows1928 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1928 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1928 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS1928 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,42,44]
theorem problem1928_eq : pairedProblem rows1928 cols1928 requiredD1928 requiredS1928 =
    MomentData.problem1928 := by rfl
theorem leaf1928 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1928++rows1928))
    (hc : (q.map Prod.snd).Perm (cols1928++cols1928))
    (hd : ∀ k ∈ requiredD1928, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1928, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1928 cols1928 requiredD1928 requiredS1928
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1928_eq] at model
  exact MomentData.excluded1928 ds ss model
def rows1929 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1929 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1929 : List Int := [-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14]
def requiredS1929 : List Int := [12,16,18,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem1929_eq : pairedProblem rows1929 cols1929 requiredD1929 requiredS1929 =
    MomentData.problem1929 := by rfl
theorem leaf1929 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1929++rows1929))
    (hc : (q.map Prod.snd).Perm (cols1929++cols1929))
    (hd : ∀ k ∈ requiredD1929, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1929, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1929 cols1929 requiredD1929 requiredS1929
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1929_eq] at model
  exact MomentData.excluded1929 ds ss model
def rows1930 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1930 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1930 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS1930 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem1930_eq : pairedProblem rows1930 cols1930 requiredD1930 requiredS1930 =
    MomentData.problem1930 := by rfl
theorem leaf1930 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1930++rows1930))
    (hc : (q.map Prod.snd).Perm (cols1930++cols1930))
    (hd : ∀ k ∈ requiredD1930, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1930, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1930 cols1930 requiredD1930 requiredS1930
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1930_eq] at model
  exact MomentData.excluded1930 ds ss model
def rows1931 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1931 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1931 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS1931 : List Int := [14,16,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem1931_eq : pairedProblem rows1931 cols1931 requiredD1931 requiredS1931 =
    MomentData.problem1931 := by rfl
theorem leaf1931 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1931++rows1931))
    (hc : (q.map Prod.snd).Perm (cols1931++cols1931))
    (hd : ∀ k ∈ requiredD1931, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1931, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1931 cols1931 requiredD1931 requiredS1931
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1931_eq] at model
  exact MomentData.excluded1931 ds ss model
def rows1932 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1932 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1932 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS1932 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem1932_eq : pairedProblem rows1932 cols1932 requiredD1932 requiredS1932 =
    MomentData.problem1932 := by rfl
theorem leaf1932 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1932++rows1932))
    (hc : (q.map Prod.snd).Perm (cols1932++cols1932))
    (hd : ∀ k ∈ requiredD1932, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1932, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1932 cols1932 requiredD1932 requiredS1932
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1932_eq] at model
  exact MomentData.excluded1932 ds ss model
def rows1933 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1933 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1933 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS1933 : List Int := [16,18,20,22,24,26,28,30,32,34,36,38,40]
theorem problem1933_eq : pairedProblem rows1933 cols1933 requiredD1933 requiredS1933 =
    MomentData.problem1933 := by rfl
theorem leaf1933 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1933++rows1933))
    (hc : (q.map Prod.snd).Perm (cols1933++cols1933))
    (hd : ∀ k ∈ requiredD1933, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1933, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1933 cols1933 requiredD1933 requiredS1933
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1933_eq] at model
  exact MomentData.excluded1933 ds ss model
def rows1934 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1934 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1934 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS1934 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,40,42,46]
theorem problem1934_eq : pairedProblem rows1934 cols1934 requiredD1934 requiredS1934 =
    MomentData.problem1934 := by rfl
theorem leaf1934 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1934++rows1934))
    (hc : (q.map Prod.snd).Perm (cols1934++cols1934))
    (hd : ∀ k ∈ requiredD1934, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1934, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1934 cols1934 requiredD1934 requiredS1934
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1934_eq] at model
  exact MomentData.excluded1934 ds ss model
def rows1935 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1935 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1935 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS1935 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,40,42]
theorem problem1935_eq : pairedProblem rows1935 cols1935 requiredD1935 requiredS1935 =
    MomentData.problem1935 := by rfl
theorem leaf1935 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1935++rows1935))
    (hc : (q.map Prod.snd).Perm (cols1935++cols1935))
    (hd : ∀ k ∈ requiredD1935, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1935, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1935 cols1935 requiredD1935 requiredS1935
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1935_eq] at model
  exact MomentData.excluded1935 ds ss model
def rows1936 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1936 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1936 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS1936 : List Int := [12,16,20,22,24,26,28,30,32,34,36,38,40,44,48]
theorem problem1936_eq : pairedProblem rows1936 cols1936 requiredD1936 requiredS1936 =
    MomentData.problem1936 := by rfl
theorem leaf1936 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1936++rows1936))
    (hc : (q.map Prod.snd).Perm (cols1936++cols1936))
    (hd : ∀ k ∈ requiredD1936, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1936, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1936 cols1936 requiredD1936 requiredS1936
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1936_eq] at model
  exact MomentData.excluded1936 ds ss model
def rows1937 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1937 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1937 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS1937 : List Int := [12,16,20,22,24,26,28,30,32,34,36,38,40,44]
theorem problem1937_eq : pairedProblem rows1937 cols1937 requiredD1937 requiredS1937 =
    MomentData.problem1937 := by rfl
theorem leaf1937 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1937++rows1937))
    (hc : (q.map Prod.snd).Perm (cols1937++cols1937))
    (hd : ∀ k ∈ requiredD1937, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1937, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1937 cols1937 requiredD1937 requiredS1937
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1937_eq] at model
  exact MomentData.excluded1937 ds ss model
def rows1938 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1938 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1938 : List Int := [-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18]
def requiredS1938 : List Int := [8,12,16,20,22,24,26,28,30,32,34,36,40,44,48]
theorem problem1938_eq : pairedProblem rows1938 cols1938 requiredD1938 requiredS1938 =
    MomentData.problem1938 := by rfl
theorem leaf1938 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1938++rows1938))
    (hc : (q.map Prod.snd).Perm (cols1938++cols1938))
    (hd : ∀ k ∈ requiredD1938, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1938, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1938 cols1938 requiredD1938 requiredS1938
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1938_eq] at model
  exact MomentData.excluded1938 ds ss model
def rows1939 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1939 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1939 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS1939 : List Int := [12,16,20,22,24,26,28,30,32,34,36,40,44,48]
theorem problem1939_eq : pairedProblem rows1939 cols1939 requiredD1939 requiredS1939 =
    MomentData.problem1939 := by rfl
theorem leaf1939 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1939++rows1939))
    (hc : (q.map Prod.snd).Perm (cols1939++cols1939))
    (hd : ∀ k ∈ requiredD1939, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1939, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1939 cols1939 requiredD1939 requiredS1939
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1939_eq] at model
  exact MomentData.excluded1939 ds ss model
def rows1940 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1940 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1940 : List Int := [-18,-14,-10,-8,-6,-4,-2,0,2,4,6,8,10,14,18]
def requiredS1940 : List Int := [12,16,20,22,24,26,28,30,32,34,36,40,44]
theorem problem1940_eq : pairedProblem rows1940 cols1940 requiredD1940 requiredS1940 =
    MomentData.problem1940 := by rfl
theorem leaf1940 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1940++rows1940))
    (hc : (q.map Prod.snd).Perm (cols1940++cols1940))
    (hd : ∀ k ∈ requiredD1940, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1940, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1940 cols1940 requiredD1940 requiredS1940
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1940_eq] at model
  exact MomentData.excluded1940 ds ss model
def rows1941 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1941 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1941 : List Int := [-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16]
def requiredS1941 : List Int := [10,14,18,20,22,24,26,28,30,32,34,36,38,42,46]
theorem problem1941_eq : pairedProblem rows1941 cols1941 requiredD1941 requiredS1941 =
    MomentData.problem1941 := by rfl
theorem leaf1941 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1941++rows1941))
    (hc : (q.map Prod.snd).Perm (cols1941++cols1941))
    (hd : ∀ k ∈ requiredD1941, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1941, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1941 cols1941 requiredD1941 requiredS1941
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1941_eq] at model
  exact MomentData.excluded1941 ds ss model
def rows1942 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1942 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1942 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS1942 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,42,46]
theorem problem1942_eq : pairedProblem rows1942 cols1942 requiredD1942 requiredS1942 =
    MomentData.problem1942 := by rfl
theorem leaf1942 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1942++rows1942))
    (hc : (q.map Prod.snd).Perm (cols1942++cols1942))
    (hd : ∀ k ∈ requiredD1942, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1942, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1942 cols1942 requiredD1942 requiredS1942
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1942_eq] at model
  exact MomentData.excluded1942 ds ss model
def rows1943 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1943 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1943 : List Int := [-16,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,16]
def requiredS1943 : List Int := [14,18,20,22,24,26,28,30,32,34,36,38,42]
theorem problem1943_eq : pairedProblem rows1943 cols1943 requiredD1943 requiredS1943 =
    MomentData.problem1943 := by rfl
theorem leaf1943 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1943++rows1943))
    (hc : (q.map Prod.snd).Perm (cols1943++cols1943))
    (hd : ∀ k ∈ requiredD1943, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1943, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1943 cols1943 requiredD1943 requiredS1943
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1943_eq] at model
  exact MomentData.excluded1943 ds ss model
def rows1944 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1944 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1944 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS1944 : List Int := [10,14,18,22,24,26,28,30,32,34,36,38,42,46,50]
theorem problem1944_eq : pairedProblem rows1944 cols1944 requiredD1944 requiredS1944 =
    MomentData.problem1944 := by rfl
theorem leaf1944 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1944++rows1944))
    (hc : (q.map Prod.snd).Perm (cols1944++cols1944))
    (hd : ∀ k ∈ requiredD1944, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1944, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1944 cols1944 requiredD1944 requiredS1944
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1944_eq] at model
  exact MomentData.excluded1944 ds ss model
def rows1945 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1945 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1945 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS1945 : List Int := [10,14,18,22,24,26,28,30,32,34,36,38,42,46]
theorem problem1945_eq : pairedProblem rows1945 cols1945 requiredD1945 requiredS1945 =
    MomentData.problem1945 := by rfl
theorem leaf1945 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1945++rows1945))
    (hc : (q.map Prod.snd).Perm (cols1945++cols1945))
    (hd : ∀ k ∈ requiredD1945, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1945, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1945 cols1945 requiredD1945 requiredS1945
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1945_eq] at model
  exact MomentData.excluded1945 ds ss model
def rows1946 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1946 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1946 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS1946 : List Int := [8,12,16,20,24,26,28,30,32,34,36,40,44,48,52]
theorem problem1946_eq : pairedProblem rows1946 cols1946 requiredD1946 requiredS1946 =
    MomentData.problem1946 := by rfl
theorem leaf1946 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1946++rows1946))
    (hc : (q.map Prod.snd).Perm (cols1946++cols1946))
    (hd : ∀ k ∈ requiredD1946, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1946, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1946 cols1946 requiredD1946 requiredS1946
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1946_eq] at model
  exact MomentData.excluded1946 ds ss model
def rows1947 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1947 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1947 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS1947 : List Int := [8,12,16,20,24,26,28,30,32,34,36,40,44,48]
theorem problem1947_eq : pairedProblem rows1947 cols1947 requiredD1947 requiredS1947 =
    MomentData.problem1947 := by rfl
theorem leaf1947 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1947++rows1947))
    (hc : (q.map Prod.snd).Perm (cols1947++cols1947))
    (hd : ∀ k ∈ requiredD1947, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1947, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1947 cols1947 requiredD1947 requiredS1947
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1947_eq] at model
  exact MomentData.excluded1947 ds ss model
def rows1948 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1948 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1948 : List Int := [-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22]
def requiredS1948 : List Int := [4,8,12,16,20,24,26,28,30,32,36,40,44,48,52]
theorem problem1948_eq : pairedProblem rows1948 cols1948 requiredD1948 requiredS1948 =
    MomentData.problem1948 := by rfl
theorem leaf1948 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1948++rows1948))
    (hc : (q.map Prod.snd).Perm (cols1948++cols1948))
    (hd : ∀ k ∈ requiredD1948, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1948, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1948 cols1948 requiredD1948 requiredS1948
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1948_eq] at model
  exact MomentData.excluded1948 ds ss model
def rows1949 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1949 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1949 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS1949 : List Int := [8,12,16,20,24,26,28,30,32,36,40,44,48,52]
theorem problem1949_eq : pairedProblem rows1949 cols1949 requiredD1949 requiredS1949 =
    MomentData.problem1949 := by rfl
theorem leaf1949 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1949++rows1949))
    (hc : (q.map Prod.snd).Perm (cols1949++cols1949))
    (hd : ∀ k ∈ requiredD1949, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1949, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1949 cols1949 requiredD1949 requiredS1949
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1949_eq] at model
  exact MomentData.excluded1949 ds ss model
def rows1950 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1950 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1950 : List Int := [-22,-18,-14,-10,-6,-4,-2,0,2,4,6,10,14,18,22]
def requiredS1950 : List Int := [8,12,16,20,24,26,28,30,32,36,40,44,48]
theorem problem1950_eq : pairedProblem rows1950 cols1950 requiredD1950 requiredS1950 =
    MomentData.problem1950 := by rfl
theorem leaf1950 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1950++rows1950))
    (hc : (q.map Prod.snd).Perm (cols1950++cols1950))
    (hd : ∀ k ∈ requiredD1950, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1950, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1950 cols1950 requiredD1950 requiredS1950
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1950_eq] at model
  exact MomentData.excluded1950 ds ss model
def rows1951 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1951 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1951 : List Int := [-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20]
def requiredS1951 : List Int := [6,10,14,18,22,24,26,28,30,32,34,38,42,46,50]
theorem problem1951_eq : pairedProblem rows1951 cols1951 requiredD1951 requiredS1951 =
    MomentData.problem1951 := by rfl
theorem leaf1951 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1951++rows1951))
    (hc : (q.map Prod.snd).Perm (cols1951++cols1951))
    (hd : ∀ k ∈ requiredD1951, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1951, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1951 cols1951 requiredD1951 requiredS1951
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1951_eq] at model
  exact MomentData.excluded1951 ds ss model
def rows1952 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1952 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1952 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS1952 : List Int := [10,14,18,22,24,26,28,30,32,34,38,42,46,50]
theorem problem1952_eq : pairedProblem rows1952 cols1952 requiredD1952 requiredS1952 =
    MomentData.problem1952 := by rfl
theorem leaf1952 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1952++rows1952))
    (hc : (q.map Prod.snd).Perm (cols1952++cols1952))
    (hd : ∀ k ∈ requiredD1952, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1952, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1952 cols1952 requiredD1952 requiredS1952
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1952_eq] at model
  exact MomentData.excluded1952 ds ss model
def rows1953 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1953 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1953 : List Int := [-20,-16,-12,-8,-6,-4,-2,0,2,4,6,8,12,16,20]
def requiredS1953 : List Int := [10,14,18,22,24,26,28,30,32,34,38,42,46]
theorem problem1953_eq : pairedProblem rows1953 cols1953 requiredD1953 requiredS1953 =
    MomentData.problem1953 := by rfl
theorem leaf1953 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1953++rows1953))
    (hc : (q.map Prod.snd).Perm (cols1953++cols1953))
    (hd : ∀ k ∈ requiredD1953, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1953, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1953 cols1953 requiredD1953 requiredS1953
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1953_eq] at model
  exact MomentData.excluded1953 ds ss model
def rows1954 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1954 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1954 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS1954 : List Int := [6,10,14,18,22,26,28,30,32,34,38,42,46,50]
theorem problem1954_eq : pairedProblem rows1954 cols1954 requiredD1954 requiredS1954 =
    MomentData.problem1954 := by rfl
theorem leaf1954 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1954++rows1954))
    (hc : (q.map Prod.snd).Perm (cols1954++cols1954))
    (hd : ∀ k ∈ requiredD1954, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1954, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1954 cols1954 requiredD1954 requiredS1954
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1954_eq] at model
  exact MomentData.excluded1954 ds ss model
def rows1955 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1955 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1955 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS1955 : List Int := [4,8,12,16,20,24,28,30,32,36,40,44,48,52]
theorem problem1955_eq : pairedProblem rows1955 cols1955 requiredD1955 requiredS1955 =
    MomentData.problem1955 := by rfl
theorem leaf1955 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1955++rows1955))
    (hc : (q.map Prod.snd).Perm (cols1955++cols1955))
    (hd : ∀ k ∈ requiredD1955, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1955, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1955 cols1955 requiredD1955 requiredS1955
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1955_eq] at model
  exact MomentData.excluded1955 ds ss model
def rows1956 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1956 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1956 : List Int := [-26,-22,-18,-14,-10,-6,-2,0,2,6,10,14,18,22,26]
def requiredS1956 : List Int := [4,8,12,16,20,24,28,32,36,40,44,48,52]
theorem problem1956_eq : pairedProblem rows1956 cols1956 requiredD1956 requiredS1956 =
    MomentData.problem1956 := by rfl
theorem leaf1956 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1956++rows1956))
    (hc : (q.map Prod.snd).Perm (cols1956++cols1956))
    (hd : ∀ k ∈ requiredD1956, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1956, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1956 cols1956 requiredD1956 requiredS1956
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1956_eq] at model
  exact MomentData.excluded1956 ds ss model
def rows1957 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def cols1957 : List Int := [1,3,5,7,9,11,13,15,17,19,21,23,25,27,29]
def requiredD1957 : List Int := [-24,-20,-16,-12,-8,-4,-2,0,2,4,8,12,16,20,24]
def requiredS1957 : List Int := [6,10,14,18,22,26,28,30,34,38,42,46,50]
theorem problem1957_eq : pairedProblem rows1957 cols1957 requiredD1957 requiredS1957 =
    MomentData.problem1957 := by rfl
theorem leaf1957 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1957++rows1957))
    (hc : (q.map Prod.snd).Perm (cols1957++cols1957))
    (hd : ∀ k ∈ requiredD1957, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1957, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1957 cols1957 requiredD1957 requiredS1957
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1957_eq] at model
  exact MomentData.excluded1957 ds ss model
def rows1958 : List Int := [1,2,4,5,8,11,14,17,18,20,23,24,26,27,29]
def cols1958 : List Int := [1,2,4,5,8,11,14,17,18,20,23,24,26,27,29]
def requiredD1958 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1958 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1958_eq : pairedProblem rows1958 cols1958 requiredD1958 requiredS1958 =
    MomentData.problem1958 := by rfl
theorem leaf1958 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1958++rows1958))
    (hc : (q.map Prod.snd).Perm (cols1958++cols1958))
    (hd : ∀ k ∈ requiredD1958, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1958, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1958 cols1958 requiredD1958 requiredS1958
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1958_eq] at model
  exact MomentData.excluded1958 ds ss model
def rows1959 : List Int := [1,2,4,5,8,11,14,17,18,20,23,24,26,27,29]
def cols1959 : List Int := [1,2,4,5,8,11,14,17,18,20,23,24,26,27,29]
def requiredD1959 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1959 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1959_eq : pairedProblem rows1959 cols1959 requiredD1959 requiredS1959 =
    MomentData.problem1959 := by rfl
theorem leaf1959 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1959++rows1959))
    (hc : (q.map Prod.snd).Perm (cols1959++cols1959))
    (hd : ∀ k ∈ requiredD1959, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1959, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1959 cols1959 requiredD1959 requiredS1959
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1959_eq] at model
  exact MomentData.excluded1959 ds ss model
def rows1960 : List Int := [1,2,4,5,8,11,14,17,19,20,23,24,26,27,29]
def cols1960 : List Int := [1,2,4,5,8,11,14,17,19,20,23,24,26,27,29]
def requiredD1960 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1960 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1960_eq : pairedProblem rows1960 cols1960 requiredD1960 requiredS1960 =
    MomentData.problem1960 := by rfl
theorem leaf1960 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1960++rows1960))
    (hc : (q.map Prod.snd).Perm (cols1960++cols1960))
    (hd : ∀ k ∈ requiredD1960, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1960, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1960 cols1960 requiredD1960 requiredS1960
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1960_eq] at model
  exact MomentData.excluded1960 ds ss model
def rows1961 : List Int := [1,2,4,5,8,11,14,17,19,20,23,24,26,27,29]
def cols1961 : List Int := [1,2,4,5,8,11,14,17,19,20,23,24,26,27,29]
def requiredD1961 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1961 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1961_eq : pairedProblem rows1961 cols1961 requiredD1961 requiredS1961 =
    MomentData.problem1961 := by rfl
theorem leaf1961 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1961++rows1961))
    (hc : (q.map Prod.snd).Perm (cols1961++cols1961))
    (hd : ∀ k ∈ requiredD1961, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1961, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1961 cols1961 requiredD1961 requiredS1961
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1961_eq] at model
  exact MomentData.excluded1961 ds ss model
def rows1962 : List Int := [1,2,4,5,7,8,10,11,14,17,20,23,26,27,29]
def cols1962 : List Int := [1,2,4,5,7,8,10,11,14,17,20,23,26,27,29]
def requiredD1962 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1962 : List Int := [13,16,19,22,24,25,28,31,34,37,40,43,46,49,52]
theorem problem1962_eq : pairedProblem rows1962 cols1962 requiredD1962 requiredS1962 =
    MomentData.problem1962 := by rfl
theorem leaf1962 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1962++rows1962))
    (hc : (q.map Prod.snd).Perm (cols1962++cols1962))
    (hd : ∀ k ∈ requiredD1962, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1962, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1962 cols1962 requiredD1962 requiredS1962
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1962_eq] at model
  exact MomentData.excluded1962 ds ss model
def rows1963 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1963 : List Int := [4,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1963 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1963 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1963_eq : pairedProblem rows1963 cols1963 requiredD1963 requiredS1963 =
    MomentData.problem1963 := by rfl
theorem leaf1963 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1963++rows1963))
    (hc : (q.map Prod.snd).Perm (cols1963++cols1963))
    (hd : ∀ k ∈ requiredD1963, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1963, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1963 cols1963 requiredD1963 requiredS1963
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1963_eq] at model
  exact MomentData.excluded1963 ds ss model
def rows1964 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1964 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1964 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1964 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1964_eq : pairedProblem rows1964 cols1964 requiredD1964 requiredS1964 =
    MomentData.problem1964 := by rfl
theorem leaf1964 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1964++rows1964))
    (hc : (q.map Prod.snd).Perm (cols1964++cols1964))
    (hd : ∀ k ∈ requiredD1964, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1964, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1964 cols1964 requiredD1964 requiredS1964
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1964_eq] at model
  exact MomentData.excluded1964 ds ss model
def rows1965 : List Int := [5,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1965 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1965 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1965 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1965_eq : pairedProblem rows1965 cols1965 requiredD1965 requiredS1965 =
    MomentData.problem1965 := by rfl
theorem leaf1965 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1965++rows1965))
    (hc : (q.map Prod.snd).Perm (cols1965++cols1965))
    (hd : ∀ k ∈ requiredD1965, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1965, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1965 cols1965 requiredD1965 requiredS1965
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1965_eq] at model
  exact MomentData.excluded1965 ds ss model
def rows1966 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1966 : List Int := [3,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1966 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1966 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1966_eq : pairedProblem rows1966 cols1966 requiredD1966 requiredS1966 =
    MomentData.problem1966 := by rfl
theorem leaf1966 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1966++rows1966))
    (hc : (q.map Prod.snd).Perm (cols1966++cols1966))
    (hd : ∀ k ∈ requiredD1966, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1966, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1966 cols1966 requiredD1966 requiredS1966
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1966_eq] at model
  exact MomentData.excluded1966 ds ss model
def rows1967 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1967 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1967 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1967 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1967_eq : pairedProblem rows1967 cols1967 requiredD1967 requiredS1967 =
    MomentData.problem1967 := by rfl
theorem leaf1967 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1967++rows1967))
    (hc : (q.map Prod.snd).Perm (cols1967++cols1967))
    (hd : ∀ k ∈ requiredD1967, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1967, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1967 cols1967 requiredD1967 requiredS1967
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1967_eq] at model
  exact MomentData.excluded1967 ds ss model
def rows1968 : List Int := [6,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1968 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1968 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1968 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1968_eq : pairedProblem rows1968 cols1968 requiredD1968 requiredS1968 =
    MomentData.problem1968 := by rfl
theorem leaf1968 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1968++rows1968))
    (hc : (q.map Prod.snd).Perm (cols1968++cols1968))
    (hd : ∀ k ∈ requiredD1968, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1968, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1968 cols1968 requiredD1968 requiredS1968
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1968_eq] at model
  exact MomentData.excluded1968 ds ss model
def rows1969 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1969 : List Int := [2,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1969 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1969 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1969_eq : pairedProblem rows1969 cols1969 requiredD1969 requiredS1969 =
    MomentData.problem1969 := by rfl
theorem leaf1969 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1969++rows1969))
    (hc : (q.map Prod.snd).Perm (cols1969++cols1969))
    (hd : ∀ k ∈ requiredD1969, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1969, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1969 cols1969 requiredD1969 requiredS1969
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1969_eq] at model
  exact MomentData.excluded1969 ds ss model
def rows1970 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols1970 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD1970 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1970 : List Int := [7,10,13,16,19,22,25,28,31,34,35,37,40,43,46]
theorem problem1970_eq : pairedProblem rows1970 cols1970 requiredD1970 requiredS1970 =
    MomentData.problem1970 := by rfl
theorem leaf1970 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1970++rows1970))
    (hc : (q.map Prod.snd).Perm (cols1970++cols1970))
    (hd : ∀ k ∈ requiredD1970, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1970, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1970 cols1970 requiredD1970 requiredS1970
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1970_eq] at model
  exact MomentData.excluded1970 ds ss model
def rows1971 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols1971 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD1971 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1971 : List Int := [10,13,16,19,22,25,28,31,34,35,37,40,43,46]
theorem problem1971_eq : pairedProblem rows1971 cols1971 requiredD1971 requiredS1971 =
    MomentData.problem1971 := by rfl
theorem leaf1971 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1971++rows1971))
    (hc : (q.map Prod.snd).Perm (cols1971++cols1971))
    (hd : ∀ k ∈ requiredD1971, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1971, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1971 cols1971 requiredD1971 requiredS1971
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1971_eq] at model
  exact MomentData.excluded1971 ds ss model
def rows1972 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols1972 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD1972 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1972 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46]
theorem problem1972_eq : pairedProblem rows1972 cols1972 requiredD1972 requiredS1972 =
    MomentData.problem1972 := by rfl
theorem leaf1972 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1972++rows1972))
    (hc : (q.map Prod.snd).Perm (cols1972++cols1972))
    (hd : ∀ k ∈ requiredD1972, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1972, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1972 cols1972 requiredD1972 requiredS1972
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1972_eq] at model
  exact MomentData.excluded1972 ds ss model
def rows1973 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def cols1973 : List Int := [1,2,4,5,8,11,14,17,20,21,23,24,26,27,29]
def requiredD1973 : List Int := [-18,-15,-12,-10,-9,-6,-3,0,3,6,9,10,12,15,18]
def requiredS1973 : List Int := [7,10,13,16,19,22,25,28,31,34,35,37,40,43]
theorem problem1973_eq : pairedProblem rows1973 cols1973 requiredD1973 requiredS1973 =
    MomentData.problem1973 := by rfl
theorem leaf1973 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1973++rows1973))
    (hc : (q.map Prod.snd).Perm (cols1973++cols1973))
    (hd : ∀ k ∈ requiredD1973, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1973, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1973 cols1973 requiredD1973 requiredS1973
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1973_eq] at model
  exact MomentData.excluded1973 ds ss model
def rows1974 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1974 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1974 : List Int := [-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6]
def requiredS1974 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,49]
theorem problem1974_eq : pairedProblem rows1974 cols1974 requiredD1974 requiredS1974 =
    MomentData.problem1974 := by rfl
theorem leaf1974 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1974++rows1974))
    (hc : (q.map Prod.snd).Perm (cols1974++cols1974))
    (hd : ∀ k ∈ requiredD1974, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1974, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1974 cols1974 requiredD1974 requiredS1974
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1974_eq] at model
  exact MomentData.excluded1974 ds ss model
def rows1975 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1975 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1975 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1975 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34]
theorem problem1975_eq : pairedProblem rows1975 cols1975 requiredD1975 requiredS1975 =
    MomentData.problem1975 := by rfl
theorem leaf1975 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1975++rows1975))
    (hc : (q.map Prod.snd).Perm (cols1975++cols1975))
    (hd : ∀ k ∈ requiredD1975, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1975, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1975 cols1975 requiredD1975 requiredS1975
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1975_eq] at model
  exact MomentData.excluded1975 ds ss model
def rows1976 : List Int := [7,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1976 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1976 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1976 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1976_eq : pairedProblem rows1976 cols1976 requiredD1976 requiredS1976 =
    MomentData.problem1976 := by rfl
theorem leaf1976 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1976++rows1976))
    (hc : (q.map Prod.snd).Perm (cols1976++cols1976))
    (hd : ∀ k ∈ requiredD1976, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1976, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1976 cols1976 requiredD1976 requiredS1976
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1976_eq] at model
  exact MomentData.excluded1976 ds ss model
def rows1977 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def cols1977 : List Int := [1,8,9,10,11,12,13,14,15,16,17,18,19,20,29]
def requiredD1977 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1977 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1977_eq : pairedProblem rows1977 cols1977 requiredD1977 requiredS1977 =
    MomentData.problem1977 := by rfl
theorem leaf1977 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1977++rows1977))
    (hc : (q.map Prod.snd).Perm (cols1977++cols1977))
    (hd : ∀ k ∈ requiredD1977, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1977, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1977 cols1977 requiredD1977 requiredS1977
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1977_eq] at model
  exact MomentData.excluded1977 ds ss model
def rows1978 : List Int := [1,2,4,5,8,11,14,17,20,22,23,24,26,27,29]
def cols1978 : List Int := [1,2,4,5,8,11,14,17,20,22,23,24,26,27,29]
def requiredD1978 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1978 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1978_eq : pairedProblem rows1978 cols1978 requiredD1978 requiredS1978 =
    MomentData.problem1978 := by rfl
theorem leaf1978 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1978++rows1978))
    (hc : (q.map Prod.snd).Perm (cols1978++cols1978))
    (hd : ∀ k ∈ requiredD1978, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1978, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1978 cols1978 requiredD1978 requiredS1978
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1978_eq] at model
  exact MomentData.excluded1978 ds ss model
def rows1979 : List Int := [1,2,4,5,8,11,14,17,20,22,23,24,26,27,29]
def cols1979 : List Int := [1,2,4,5,8,11,14,17,20,22,23,24,26,27,29]
def requiredD1979 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1979 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1979_eq : pairedProblem rows1979 cols1979 requiredD1979 requiredS1979 =
    MomentData.problem1979 := by rfl
theorem leaf1979 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1979++rows1979))
    (hc : (q.map Prod.snd).Perm (cols1979++cols1979))
    (hd : ∀ k ∈ requiredD1979, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1979, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1979 cols1979 requiredD1979 requiredS1979
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1979_eq] at model
  exact MomentData.excluded1979 ds ss model
def rows1980 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,29]
def cols1980 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,29]
def requiredD1980 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS1980 : List Int := [5,9,13,17,21,25,28,29,33,37,41,45,49,53]
theorem problem1980_eq : pairedProblem rows1980 cols1980 requiredD1980 requiredS1980 =
    MomentData.problem1980 := by rfl
theorem leaf1980 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1980++rows1980))
    (hc : (q.map Prod.snd).Perm (cols1980++cols1980))
    (hd : ∀ k ∈ requiredD1980, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1980, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1980 cols1980 requiredD1980 requiredS1980
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1980_eq] at model
  exact MomentData.excluded1980 ds ss model
def rows1981 : List Int := [1,2,4,5,8,11,14,17,20,23,24,25,26,27,29]
def cols1981 : List Int := [1,2,4,5,8,11,14,17,20,23,24,25,26,27,29]
def requiredD1981 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1981 : List Int := [7,10,13,16,19,22,25,28,31,34,37,40,43,46,49]
theorem problem1981_eq : pairedProblem rows1981 cols1981 requiredD1981 requiredS1981 =
    MomentData.problem1981 := by rfl
theorem leaf1981 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1981++rows1981))
    (hc : (q.map Prod.snd).Perm (cols1981++cols1981))
    (hd : ∀ k ∈ requiredD1981, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1981, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1981 cols1981 requiredD1981 requiredS1981
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1981_eq] at model
  exact MomentData.excluded1981 ds ss model
def rows1982 : List Int := [1,2,4,5,8,11,14,17,20,23,24,25,26,27,29]
def cols1982 : List Int := [1,2,4,5,8,11,14,17,20,23,24,25,26,27,29]
def requiredD1982 : List Int := [-18,-15,-12,-9,-7,-6,-3,0,3,6,7,9,12,15,18]
def requiredS1982 : List Int := [10,13,16,19,21,22,25,28,31,34,35,37,40,43,46]
theorem problem1982_eq : pairedProblem rows1982 cols1982 requiredD1982 requiredS1982 =
    MomentData.problem1982 := by rfl
theorem leaf1982 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1982++rows1982))
    (hc : (q.map Prod.snd).Perm (cols1982++cols1982))
    (hd : ∀ k ∈ requiredD1982, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1982, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1982 cols1982 requiredD1982 requiredS1982
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1982_eq] at model
  exact MomentData.excluded1982 ds ss model
def rows1983 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def cols1983 : List Int := [6,7,8,9,10,11,12,13,14,15,16,17,18,19,29]
def requiredD1983 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1983 : List Int := [20,21,22,23,24,25,26,27,28,29,30,31,32,33,48]
theorem problem1983_eq : pairedProblem rows1983 cols1983 requiredD1983 requiredS1983 =
    MomentData.problem1983 := by rfl
theorem leaf1983 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1983++rows1983))
    (hc : (q.map Prod.snd).Perm (cols1983++cols1983))
    (hd : ∀ k ∈ requiredD1983, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1983, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1983 cols1983 requiredD1983 requiredS1983
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1983_eq] at model
  exact MomentData.excluded1983 ds ss model
def rows1984 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def cols1984 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,29]
def requiredD1984 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1984 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1984_eq : pairedProblem rows1984 cols1984 requiredD1984 requiredS1984 =
    MomentData.problem1984 := by rfl
theorem leaf1984 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1984++rows1984))
    (hc : (q.map Prod.snd).Perm (cols1984++cols1984))
    (hd : ∀ k ∈ requiredD1984, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1984, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1984 cols1984 requiredD1984 requiredS1984
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1984_eq] at model
  exact MomentData.excluded1984 ds ss model
def rows1985 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def cols1985 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,22,29]
def requiredD1985 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1985 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1985_eq : pairedProblem rows1985 cols1985 requiredD1985 requiredS1985 =
    MomentData.problem1985 := by rfl
theorem leaf1985 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1985++rows1985))
    (hc : (q.map Prod.snd).Perm (cols1985++cols1985))
    (hd : ∀ k ∈ requiredD1985, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1985, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1985 cols1985 requiredD1985 requiredS1985
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1985_eq] at model
  exact MomentData.excluded1985 ds ss model
def rows1986 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def cols1986 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,23,29]
def requiredD1986 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1986 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1986_eq : pairedProblem rows1986 cols1986 requiredD1986 requiredS1986 =
    MomentData.problem1986 := by rfl
theorem leaf1986 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1986++rows1986))
    (hc : (q.map Prod.snd).Perm (cols1986++cols1986))
    (hd : ∀ k ∈ requiredD1986, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1986, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1986 cols1986 requiredD1986 requiredS1986
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1986_eq] at model
  exact MomentData.excluded1986 ds ss model
def rows1987 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def cols1987 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,24,29]
def requiredD1987 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1987 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1987_eq : pairedProblem rows1987 cols1987 requiredD1987 requiredS1987 =
    MomentData.problem1987 := by rfl
theorem leaf1987 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1987++rows1987))
    (hc : (q.map Prod.snd).Perm (cols1987++cols1987))
    (hd : ∀ k ∈ requiredD1987, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1987, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1987 cols1987 requiredD1987 requiredS1987
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1987_eq] at model
  exact MomentData.excluded1987 ds ss model
def rows1988 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def cols1988 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,25,29]
def requiredD1988 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1988 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1988_eq : pairedProblem rows1988 cols1988 requiredD1988 requiredS1988 =
    MomentData.problem1988 := by rfl
theorem leaf1988 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1988++rows1988))
    (hc : (q.map Prod.snd).Perm (cols1988++cols1988))
    (hd : ∀ k ∈ requiredD1988, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1988, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1988 cols1988 requiredD1988 requiredS1988
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1988_eq] at model
  exact MomentData.excluded1988 ds ss model
def rows1989 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def cols1989 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,26,29]
def requiredD1989 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1989 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1989_eq : pairedProblem rows1989 cols1989 requiredD1989 requiredS1989 =
    MomentData.problem1989 := by rfl
theorem leaf1989 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1989++rows1989))
    (hc : (q.map Prod.snd).Perm (cols1989++cols1989))
    (hd : ∀ k ∈ requiredD1989, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1989, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1989 cols1989 requiredD1989 requiredS1989
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1989_eq] at model
  exact MomentData.excluded1989 ds ss model
def rows1990 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def cols1990 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,27,29]
def requiredD1990 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS1990 : List Int := [21,22,23,24,25,26,27,28,29,30,31,32,33,34,35]
theorem problem1990_eq : pairedProblem rows1990 cols1990 requiredD1990 requiredS1990 =
    MomentData.problem1990 := by rfl
theorem leaf1990 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1990++rows1990))
    (hc : (q.map Prod.snd).Perm (cols1990++cols1990))
    (hd : ∀ k ∈ requiredD1990, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1990, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1990 cols1990 requiredD1990 requiredS1990
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1990_eq] at model
  exact MomentData.excluded1990 ds ss model
def rows1991 : List Int := [1,2,4,5,7,10,13,15,16,19,22,24,25,27,28]
def cols1991 : List Int := [1,2,4,5,7,10,13,15,16,19,22,24,25,27,28]
def requiredD1991 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1991 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1991_eq : pairedProblem rows1991 cols1991 requiredD1991 requiredS1991 =
    MomentData.problem1991 := by rfl
theorem leaf1991 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1991++rows1991))
    (hc : (q.map Prod.snd).Perm (cols1991++cols1991))
    (hd : ∀ k ∈ requiredD1991, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1991, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1991 cols1991 requiredD1991 requiredS1991
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1991_eq] at model
  exact MomentData.excluded1991 ds ss model
def rows1992 : List Int := [1,2,4,5,7,10,13,15,16,19,22,24,25,27,28]
def cols1992 : List Int := [1,2,4,5,7,10,13,15,16,19,22,24,25,27,28]
def requiredD1992 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1992 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem1992_eq : pairedProblem rows1992 cols1992 requiredD1992 requiredS1992 =
    MomentData.problem1992 := by rfl
theorem leaf1992 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1992++rows1992))
    (hc : (q.map Prod.snd).Perm (cols1992++cols1992))
    (hd : ∀ k ∈ requiredD1992, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1992, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1992 cols1992 requiredD1992 requiredS1992
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1992_eq] at model
  exact MomentData.excluded1992 ds ss model
def rows1993 : List Int := [1,2,4,5,7,10,13,16,17,19,22,24,25,27,28]
def cols1993 : List Int := [1,2,4,5,7,10,13,16,17,19,22,24,25,27,28]
def requiredD1993 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1993 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1993_eq : pairedProblem rows1993 cols1993 requiredD1993 requiredS1993 =
    MomentData.problem1993 := by rfl
theorem leaf1993 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1993++rows1993))
    (hc : (q.map Prod.snd).Perm (cols1993++cols1993))
    (hd : ∀ k ∈ requiredD1993, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1993, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1993 cols1993 requiredD1993 requiredS1993
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1993_eq] at model
  exact MomentData.excluded1993 ds ss model
def rows1994 : List Int := [1,2,4,5,7,10,13,16,17,19,22,24,25,27,28]
def cols1994 : List Int := [1,2,4,5,7,10,13,16,17,19,22,24,25,27,28]
def requiredD1994 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1994 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem1994_eq : pairedProblem rows1994 cols1994 requiredD1994 requiredS1994 =
    MomentData.problem1994 := by rfl
theorem leaf1994 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1994++rows1994))
    (hc : (q.map Prod.snd).Perm (cols1994++cols1994))
    (hd : ∀ k ∈ requiredD1994, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1994, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1994 cols1994 requiredD1994 requiredS1994
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1994_eq] at model
  exact MomentData.excluded1994 ds ss model
def rows1995 : List Int := [1,2,4,5,7,10,13,16,18,19,22,24,25,27,28]
def cols1995 : List Int := [1,2,4,5,7,10,13,16,18,19,22,24,25,27,28]
def requiredD1995 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1995 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1995_eq : pairedProblem rows1995 cols1995 requiredD1995 requiredS1995 =
    MomentData.problem1995 := by rfl
theorem leaf1995 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1995++rows1995))
    (hc : (q.map Prod.snd).Perm (cols1995++cols1995))
    (hd : ∀ k ∈ requiredD1995, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1995, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1995 cols1995 requiredD1995 requiredS1995
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1995_eq] at model
  exact MomentData.excluded1995 ds ss model
def rows1996 : List Int := [1,2,4,5,7,10,13,16,18,19,22,24,25,27,28]
def cols1996 : List Int := [1,2,4,5,7,10,13,16,18,19,22,24,25,27,28]
def requiredD1996 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1996 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem1996_eq : pairedProblem rows1996 cols1996 requiredD1996 requiredS1996 =
    MomentData.problem1996 := by rfl
theorem leaf1996 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1996++rows1996))
    (hc : (q.map Prod.snd).Perm (cols1996++cols1996))
    (hd : ∀ k ∈ requiredD1996, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1996, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1996 cols1996 requiredD1996 requiredS1996
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1996_eq] at model
  exact MomentData.excluded1996 ds ss model
def rows1997 : List Int := [1,2,4,5,7,10,13,16,19,20,22,24,25,27,28]
def cols1997 : List Int := [1,2,4,5,7,10,13,16,19,20,22,24,25,27,28]
def requiredD1997 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS1997 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem1997_eq : pairedProblem rows1997 cols1997 requiredD1997 requiredS1997 =
    MomentData.problem1997 := by rfl
theorem leaf1997 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1997++rows1997))
    (hc : (q.map Prod.snd).Perm (cols1997++cols1997))
    (hd : ∀ k ∈ requiredD1997, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1997, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1997 cols1997 requiredD1997 requiredS1997
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1997_eq] at model
  exact MomentData.excluded1997 ds ss model
def rows1998 : List Int := [1,2,4,5,7,10,13,16,19,20,22,24,25,27,28]
def cols1998 : List Int := [1,2,4,5,7,10,13,16,19,20,22,24,25,27,28]
def requiredD1998 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS1998 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem1998_eq : pairedProblem rows1998 cols1998 requiredD1998 requiredS1998 =
    MomentData.problem1998 := by rfl
theorem leaf1998 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1998++rows1998))
    (hc : (q.map Prod.snd).Perm (cols1998++cols1998))
    (hd : ∀ k ∈ requiredD1998, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1998, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1998 cols1998 requiredD1998 requiredS1998
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1998_eq] at model
  exact MomentData.excluded1998 ds ss model
def rows1999 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols1999 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD1999 : List Int := [-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18]
def requiredS1999 : List Int := [8,11,14,17,20,23,26,29,32,35,37,38,41,44,47]
theorem problem1999_eq : pairedProblem rows1999 cols1999 requiredD1999 requiredS1999 =
    MomentData.problem1999 := by rfl
theorem leaf1999 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows1999++rows1999))
    (hc : (q.map Prod.snd).Perm (cols1999++cols1999))
    (hd : ∀ k ∈ requiredD1999, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS1999, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows1999 cols1999 requiredD1999 requiredS1999
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem1999_eq] at model
  exact MomentData.excluded1999 ds ss model
def rows2000 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols2000 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD2000 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS2000 : List Int := [11,14,17,20,23,26,29,32,35,37,38,41,44,47]
theorem problem2000_eq : pairedProblem rows2000 cols2000 requiredD2000 requiredS2000 =
    MomentData.problem2000 := by rfl
theorem leaf2000 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2000++rows2000))
    (hc : (q.map Prod.snd).Perm (cols2000++cols2000))
    (hd : ∀ k ∈ requiredD2000, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2000, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2000 cols2000 requiredD2000 requiredS2000
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2000_eq] at model
  exact MomentData.excluded2000 ds ss model
def rows2001 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols2001 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD2001 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS2001 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47]
theorem problem2001_eq : pairedProblem rows2001 cols2001 requiredD2001 requiredS2001 =
    MomentData.problem2001 := by rfl
theorem leaf2001 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2001++rows2001))
    (hc : (q.map Prod.snd).Perm (cols2001++cols2001))
    (hd : ∀ k ∈ requiredD2001, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2001, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2001 cols2001 requiredD2001 requiredS2001
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2001_eq] at model
  exact MomentData.excluded2001 ds ss model
def rows2002 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def cols2002 : List Int := [1,2,4,5,7,10,13,16,19,21,22,24,25,27,28]
def requiredD2002 : List Int := [-18,-15,-12,-11,-9,-6,-3,0,3,6,9,11,12,15,18]
def requiredS2002 : List Int := [8,11,14,17,20,23,26,29,32,35,37,38,41,44]
theorem problem2002_eq : pairedProblem rows2002 cols2002 requiredD2002 requiredS2002 =
    MomentData.problem2002 := by rfl
theorem leaf2002 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2002++rows2002))
    (hc : (q.map Prod.snd).Perm (cols2002++cols2002))
    (hd : ∀ k ∈ requiredD2002, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2002, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2002 cols2002 requiredD2002 requiredS2002
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2002_eq] at model
  exact MomentData.excluded2002 ds ss model
def rows2003 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols2003 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD2003 : List Int := [-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12]
def requiredS2003 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem2003_eq : pairedProblem rows2003 cols2003 requiredD2003 requiredS2003 =
    MomentData.problem2003 := by rfl
theorem leaf2003 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2003++rows2003))
    (hc : (q.map Prod.snd).Perm (cols2003++cols2003))
    (hd : ∀ k ∈ requiredD2003, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2003, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2003 cols2003 requiredD2003 requiredS2003
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2003_eq] at model
  exact MomentData.excluded2003 ds ss model
def rows2004 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols2004 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD2004 : List Int := [-17,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,17]
def requiredS2004 : List Int := [14,19,21,23,25,27,29,31,33,35,37,39,41,43]
theorem problem2004_eq : pairedProblem rows2004 cols2004 requiredD2004 requiredS2004 =
    MomentData.problem2004 := by rfl
theorem leaf2004 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2004++rows2004))
    (hc : (q.map Prod.snd).Perm (cols2004++cols2004))
    (hd : ∀ k ∈ requiredD2004, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2004, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2004 cols2004 requiredD2004 requiredS2004
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2004_eq] at model
  exact MomentData.excluded2004 ds ss model
def rows2005 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def cols2005 : List Int := [1,3,5,7,9,11,13,15,16,18,20,22,24,26,28]
def requiredD2005 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2005 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41]
theorem problem2005_eq : pairedProblem rows2005 cols2005 requiredD2005 requiredS2005 =
    MomentData.problem2005 := by rfl
theorem leaf2005 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2005++rows2005))
    (hc : (q.map Prod.snd).Perm (cols2005++cols2005))
    (hd : ∀ k ∈ requiredD2005, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2005, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2005 cols2005 requiredD2005 requiredS2005
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2005_eq] at model
  exact MomentData.excluded2005 ds ss model
def rows2006 : List Int := [1,3,5,7,9,11,13,15,17,18,20,22,24,26,28]
def cols2006 : List Int := [1,3,5,7,9,11,13,15,17,18,20,22,24,26,28]
def requiredD2006 : List Int := [-14,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,14]
def requiredS2006 : List Int := [16,19,21,23,25,27,29,31,33,35,37,39,41,43,45]
theorem problem2006_eq : pairedProblem rows2006 cols2006 requiredD2006 requiredS2006 =
    MomentData.problem2006 := by rfl
theorem leaf2006 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2006++rows2006))
    (hc : (q.map Prod.snd).Perm (cols2006++cols2006))
    (hd : ∀ k ∈ requiredD2006, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2006, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2006 cols2006 requiredD2006 requiredS2006
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2006_eq] at model
  exact MomentData.excluded2006 ds ss model
def rows2007 : List Int := [1,2,4,5,7,10,13,16,19,22,23,24,25,27,28]
def cols2007 : List Int := [1,2,4,5,7,10,13,16,19,22,23,24,25,27,28]
def requiredD2007 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS2007 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem2007_eq : pairedProblem rows2007 cols2007 requiredD2007 requiredS2007 =
    MomentData.problem2007 := by rfl
theorem leaf2007 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2007++rows2007))
    (hc : (q.map Prod.snd).Perm (cols2007++cols2007))
    (hd : ∀ k ∈ requiredD2007, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2007, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2007 cols2007 requiredD2007 requiredS2007
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2007_eq] at model
  exact MomentData.excluded2007 ds ss model
def rows2008 : List Int := [1,2,4,5,7,10,13,16,19,22,23,24,25,27,28]
def cols2008 : List Int := [1,2,4,5,7,10,13,16,19,22,23,24,25,27,28]
def requiredD2008 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS2008 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem2008_eq : pairedProblem rows2008 cols2008 requiredD2008 requiredS2008 =
    MomentData.problem2008 := by rfl
theorem leaf2008 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2008++rows2008))
    (hc : (q.map Prod.snd).Perm (cols2008++cols2008))
    (hd : ∀ k ∈ requiredD2008, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2008, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2008 cols2008 requiredD2008 requiredS2008
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2008_eq] at model
  exact MomentData.excluded2008 ds ss model
def rows2009 : List Int := [1,3,5,7,9,11,13,16,17,18,20,22,24,26,28]
def cols2009 : List Int := [1,3,5,7,9,11,13,16,17,18,20,22,24,26,28]
def requiredD2009 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2009 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2009_eq : pairedProblem rows2009 cols2009 requiredD2009 requiredS2009 =
    MomentData.problem2009 := by rfl
theorem leaf2009 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2009++rows2009))
    (hc : (q.map Prod.snd).Perm (cols2009++cols2009))
    (hd : ∀ k ∈ requiredD2009, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2009, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2009 cols2009 requiredD2009 requiredS2009
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2009_eq] at model
  exact MomentData.excluded2009 ds ss model
def rows2010 : List Int := [1,3,5,7,9,11,13,16,18,19,20,22,24,26,28]
def cols2010 : List Int := [1,3,5,7,9,11,13,16,18,19,20,22,24,26,28]
def requiredD2010 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2010 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2010_eq : pairedProblem rows2010 cols2010 requiredD2010 requiredS2010 =
    MomentData.problem2010 := by rfl
theorem leaf2010 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2010++rows2010))
    (hc : (q.map Prod.snd).Perm (cols2010++cols2010))
    (hd : ∀ k ∈ requiredD2010, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2010, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2010 cols2010 requiredD2010 requiredS2010
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2010_eq] at model
  exact MomentData.excluded2010 ds ss model
def rows2011 : List Int := [2,3,6,7,10,11,14,15,16,18,19,22,23,26,27]
def cols2011 : List Int := [2,3,6,7,10,11,14,15,16,18,19,22,23,26,27]
def requiredD2011 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2011 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2011_eq : pairedProblem rows2011 cols2011 requiredD2011 requiredS2011 =
    MomentData.problem2011 := by rfl
theorem leaf2011 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2011++rows2011))
    (hc : (q.map Prod.snd).Perm (cols2011++cols2011))
    (hd : ∀ k ∈ requiredD2011, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2011, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2011 cols2011 requiredD2011 requiredS2011
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2011_eq] at model
  exact MomentData.excluded2011 ds ss model
def rows2012 : List Int := [2,3,6,7,10,11,14,15,17,18,19,22,23,26,27]
def cols2012 : List Int := [2,3,6,7,10,11,14,15,17,18,19,22,23,26,27]
def requiredD2012 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2012 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2012_eq : pairedProblem rows2012 cols2012 requiredD2012 requiredS2012 =
    MomentData.problem2012 := by rfl
theorem leaf2012 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2012++rows2012))
    (hc : (q.map Prod.snd).Perm (cols2012++cols2012))
    (hd : ∀ k ∈ requiredD2012, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2012, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2012 cols2012 requiredD2012 requiredS2012
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2012_eq] at model
  exact MomentData.excluded2012 ds ss model
def rows2013 : List Int := [1,3,5,7,9,11,13,16,18,20,21,22,24,26,28]
def cols2013 : List Int := [1,3,5,7,9,11,13,16,18,20,21,22,24,26,28]
def requiredD2013 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2013 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2013_eq : pairedProblem rows2013 cols2013 requiredD2013 requiredS2013 =
    MomentData.problem2013 := by rfl
theorem leaf2013 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2013++rows2013))
    (hc : (q.map Prod.snd).Perm (cols2013++cols2013))
    (hd : ∀ k ∈ requiredD2013, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2013, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2013 cols2013 requiredD2013 requiredS2013
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2013_eq] at model
  exact MomentData.excluded2013 ds ss model
def rows2014 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,26,27,28]
def cols2014 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,26,27,28]
def requiredD2014 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS2014 : List Int := [8,11,14,17,20,23,26,29,32,35,38,41,44,47,50]
theorem problem2014_eq : pairedProblem rows2014 cols2014 requiredD2014 requiredS2014 =
    MomentData.problem2014 := by rfl
theorem leaf2014 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2014++rows2014))
    (hc : (q.map Prod.snd).Perm (cols2014++cols2014))
    (hd : ∀ k ∈ requiredD2014, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2014, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2014 cols2014 requiredD2014 requiredS2014
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2014_eq] at model
  exact MomentData.excluded2014 ds ss model
def rows2015 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,26,27,28]
def cols2015 : List Int := [1,2,4,5,7,10,13,16,19,22,24,25,26,27,28]
def requiredD2015 : List Int := [-18,-15,-12,-9,-8,-6,-3,0,3,6,8,9,12,15,18]
def requiredS2015 : List Int := [11,14,17,20,21,23,26,29,32,35,37,38,41,44,47]
theorem problem2015_eq : pairedProblem rows2015 cols2015 requiredD2015 requiredS2015 =
    MomentData.problem2015 := by rfl
theorem leaf2015 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2015++rows2015))
    (hc : (q.map Prod.snd).Perm (cols2015++cols2015))
    (hd : ∀ k ∈ requiredD2015, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2015, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2015 cols2015 requiredD2015 requiredS2015
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2015_eq] at model
  exact MomentData.excluded2015 ds ss model
def rows2016 : List Int := [2,3,6,7,10,11,14,15,18,19,20,22,23,26,27]
def cols2016 : List Int := [2,3,6,7,10,11,14,15,18,19,20,22,23,26,27]
def requiredD2016 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2016 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2016_eq : pairedProblem rows2016 cols2016 requiredD2016 requiredS2016 =
    MomentData.problem2016 := by rfl
theorem leaf2016 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2016++rows2016))
    (hc : (q.map Prod.snd).Perm (cols2016++cols2016))
    (hd : ∀ k ∈ requiredD2016, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2016, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2016 cols2016 requiredD2016 requiredS2016
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2016_eq] at model
  exact MomentData.excluded2016 ds ss model
def rows2017 : List Int := [1,3,5,7,9,11,13,16,18,20,22,23,24,26,28]
def cols2017 : List Int := [1,3,5,7,9,11,13,16,18,20,22,23,24,26,28]
def requiredD2017 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2017 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2017_eq : pairedProblem rows2017 cols2017 requiredD2017 requiredS2017 =
    MomentData.problem2017 := by rfl
theorem leaf2017 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2017++rows2017))
    (hc : (q.map Prod.snd).Perm (cols2017++cols2017))
    (hd : ∀ k ∈ requiredD2017, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2017, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2017 cols2017 requiredD2017 requiredS2017
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2017_eq] at model
  exact MomentData.excluded2017 ds ss model
def rows2018 : List Int := [2,3,6,7,10,11,14,15,18,19,21,22,23,26,27]
def cols2018 : List Int := [2,3,6,7,10,11,14,15,18,19,21,22,23,26,27]
def requiredD2018 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2018 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2018_eq : pairedProblem rows2018 cols2018 requiredD2018 requiredS2018 =
    MomentData.problem2018 := by rfl
theorem leaf2018 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2018++rows2018))
    (hc : (q.map Prod.snd).Perm (cols2018++cols2018))
    (hd : ∀ k ∈ requiredD2018, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2018, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2018 cols2018 requiredD2018 requiredS2018
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2018_eq] at model
  exact MomentData.excluded2018 ds ss model
def rows2019 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,25,26,28]
def cols2019 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,25,26,28]
def requiredD2019 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2019 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2019_eq : pairedProblem rows2019 cols2019 requiredD2019 requiredS2019 =
    MomentData.problem2019 := by rfl
theorem leaf2019 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2019++rows2019))
    (hc : (q.map Prod.snd).Perm (cols2019++cols2019))
    (hd : ∀ k ∈ requiredD2019, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2019, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2019 cols2019 requiredD2019 requiredS2019
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2019_eq] at model
  exact MomentData.excluded2019 ds ss model
def rows2020 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,24,26,27]
def cols2020 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,24,26,27]
def requiredD2020 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2020 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2020_eq : pairedProblem rows2020 cols2020 requiredD2020 requiredS2020 =
    MomentData.problem2020 := by rfl
theorem leaf2020 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2020++rows2020))
    (hc : (q.map Prod.snd).Perm (cols2020++cols2020))
    (hd : ∀ k ∈ requiredD2020, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2020, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2020 cols2020 requiredD2020 requiredS2020
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2020_eq] at model
  exact MomentData.excluded2020 ds ss model
def rows2021 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,25,26,27]
def cols2021 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,25,26,27]
def requiredD2021 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2021 : List Int := [5,9,13,17,21,25,28,29,30,33,37,41,45,49,53]
theorem problem2021_eq : pairedProblem rows2021 cols2021 requiredD2021 requiredS2021 =
    MomentData.problem2021 := by rfl
theorem leaf2021 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2021++rows2021))
    (hc : (q.map Prod.snd).Perm (cols2021++cols2021))
    (hd : ∀ k ∈ requiredD2021, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2021, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2021 cols2021 requiredD2021 requiredS2021
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2021_eq] at model
  exact MomentData.excluded2021 ds ss model
def rows2022 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,27,28]
def cols2022 : List Int := [1,3,5,7,9,11,13,16,18,20,22,24,26,27,28]
def requiredD2022 : List Int := [-15,-12,-10,-8,-6,-4,-2,0,2,4,6,8,10,12,15]
def requiredS2022 : List Int := [14,17,19,21,23,25,27,29,31,33,35,37,39,41,44]
theorem problem2022_eq : pairedProblem rows2022 cols2022 requiredD2022 requiredS2022 =
    MomentData.problem2022 := by rfl
theorem leaf2022 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2022++rows2022))
    (hc : (q.map Prod.snd).Perm (cols2022++cols2022))
    (hd : ∀ k ∈ requiredD2022, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2022, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2022 cols2022 requiredD2022 requiredS2022
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2022_eq] at model
  exact MomentData.excluded2022 ds ss model
def rows2023 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,28]
def cols2023 : List Int := [2,3,6,7,10,11,14,15,18,19,22,23,26,27,28]
def requiredD2023 : List Int := [-24,-20,-16,-12,-8,-4,-1,0,1,4,8,12,16,20,24]
def requiredS2023 : List Int := [5,9,13,17,21,25,29,30,33,37,41,45,49,53]
theorem problem2023_eq : pairedProblem rows2023 cols2023 requiredD2023 requiredS2023 =
    MomentData.problem2023 := by rfl
theorem leaf2023 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2023++rows2023))
    (hc : (q.map Prod.snd).Perm (cols2023++cols2023))
    (hd : ∀ k ∈ requiredD2023, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2023, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2023 cols2023 requiredD2023 requiredS2023
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2023_eq] at model
  exact MomentData.excluded2023 ds ss model
def rows2024 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def cols2024 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,22]
def requiredD2024 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2024 : List Int := [23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2024_eq : pairedProblem rows2024 cols2024 requiredD2024 requiredS2024 =
    MomentData.problem2024 := by rfl
theorem leaf2024 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2024++rows2024))
    (hc : (q.map Prod.snd).Perm (cols2024++cols2024))
    (hd : ∀ k ∈ requiredD2024, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2024, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2024 cols2024 requiredD2024 requiredS2024
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2024_eq] at model
  exact MomentData.excluded2024 ds ss model
def rows2025 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,23]
def cols2025 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,23]
def requiredD2025 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2025 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2025_eq : pairedProblem rows2025 cols2025 requiredD2025 requiredS2025 =
    MomentData.problem2025 := by rfl
theorem leaf2025 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2025++rows2025))
    (hc : (q.map Prod.snd).Perm (cols2025++cols2025))
    (hd : ∀ k ∈ requiredD2025, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2025, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2025 cols2025 requiredD2025 requiredS2025
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2025_eq] at model
  exact MomentData.excluded2025 ds ss model
def rows2026 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,24]
def cols2026 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,24]
def requiredD2026 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2026 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2026_eq : pairedProblem rows2026 cols2026 requiredD2026 requiredS2026 =
    MomentData.problem2026 := by rfl
theorem leaf2026 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2026++rows2026))
    (hc : (q.map Prod.snd).Perm (cols2026++cols2026))
    (hd : ∀ k ∈ requiredD2026, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2026, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2026 cols2026 requiredD2026 requiredS2026
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2026_eq] at model
  exact MomentData.excluded2026 ds ss model
def rows2027 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,25]
def cols2027 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,25]
def requiredD2027 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2027 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2027_eq : pairedProblem rows2027 cols2027 requiredD2027 requiredS2027 =
    MomentData.problem2027 := by rfl
theorem leaf2027 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2027++rows2027))
    (hc : (q.map Prod.snd).Perm (cols2027++cols2027))
    (hd : ∀ k ∈ requiredD2027, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2027, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2027 cols2027 requiredD2027 requiredS2027
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2027_eq] at model
  exact MomentData.excluded2027 ds ss model
def rows2028 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,26]
def cols2028 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,26]
def requiredD2028 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2028 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2028_eq : pairedProblem rows2028 cols2028 requiredD2028 requiredS2028 =
    MomentData.problem2028 := by rfl
theorem leaf2028 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2028++rows2028))
    (hc : (q.map Prod.snd).Perm (cols2028++cols2028))
    (hd : ∀ k ∈ requiredD2028, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2028, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2028 cols2028 requiredD2028 requiredS2028
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2028_eq] at model
  exact MomentData.excluded2028 ds ss model
def rows2029 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,27]
def cols2029 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,27]
def requiredD2029 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2029 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2029_eq : pairedProblem rows2029 cols2029 requiredD2029 requiredS2029 =
    MomentData.problem2029 := by rfl
theorem leaf2029 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2029++rows2029))
    (hc : (q.map Prod.snd).Perm (cols2029++cols2029))
    (hd : ∀ k ∈ requiredD2029, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2029, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2029 cols2029 requiredD2029 requiredS2029
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2029_eq] at model
  exact MomentData.excluded2029 ds ss model
def rows2030 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,28]
def cols2030 : List Int := [8,9,10,11,12,13,14,15,16,17,18,19,20,21,28]
def requiredD2030 : List Int := [-7,-6,-5,-4,-3,-2,-1,0,1,2,3,4,5,6,7]
def requiredS2030 : List Int := [22,23,24,25,26,27,28,29,30,31,32,33,34,35,36]
theorem problem2030_eq : pairedProblem rows2030 cols2030 requiredD2030 requiredS2030 =
    MomentData.problem2030 := by rfl
theorem leaf2030 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2030++rows2030))
    (hc : (q.map Prod.snd).Perm (cols2030++cols2030))
    (hd : ∀ k ∈ requiredD2030, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2030, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2030 cols2030 requiredD2030 requiredS2030
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2030_eq] at model
  exact MomentData.excluded2030 ds ss model
def rows2031 : List Int := [1,2,4,7,10,13,16,18,19,21,22,24,25,27,28]
def cols2031 : List Int := [1,2,4,7,10,13,16,18,19,21,22,24,25,27,28]
def requiredD2031 : List Int := [-21,-18,-15,-12,-9,-6,-3,0,3,6,9,12,15,18,21]
def requiredS2031 : List Int := [5,8,11,14,17,20,23,26,29,32,34,35,38,41,44]
theorem problem2031_eq : pairedProblem rows2031 cols2031 requiredD2031 requiredS2031 =
    MomentData.problem2031 := by rfl
theorem leaf2031 (q : List (Int × Int))
    (hr : (q.map Prod.fst).Perm (rows2031++rows2031))
    (hc : (q.map Prod.snd).Perm (cols2031++cols2031))
    (hd : ∀ k ∈ requiredD2031, (Gardner.Marginal.differences q).count k = 2)
    (hs : ∀ k ∈ requiredS2031, (Gardner.Marginal.sums q).count k = 2) : False := by
  obtain ⟨ds,ss,model⟩ := paired_residual_realizes q rows2031 cols2031 requiredD2031 requiredS2031
    (by decide) hr hc (by decide) (by decide) hd hs
  rw [problem2031_eq] at model
  exact MomentData.excluded2031 ds ss model
#print axioms leaf1920
end Gardner.Kernel.MomentContexts
