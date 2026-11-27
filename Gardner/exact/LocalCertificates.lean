import Lean

/- An executable certificate validator, compiled from Lean source. A difference
   d has array index d+29 and a sum s has index s. The moment calculation below
   converts indices back to ordinary signed key values. -/
namespace Gardner.LocalCertificates
open Lean

abbrev Check := Except String
abbrev Edge := Nat × Nat

private def requireC (ok : Bool) (message : String) : Check Unit :=
  if ok then .ok () else .error message

private def tuple (v : Json) (len : Nat) : Check (Array Json) := do
  let xs ← v.getArr?
  requireC (xs.size == len) "wrong tuple arity"
  return xs

private def keyIndex (diff : Bool) (v : Json) : Check Nat := do
  let k ← v.getInt?
  let i := if diff then k+29 else k
  requireC (0 ≤ i && i < 59) "diagonal outside board"
  return i.toNat

private def edge (v : Json) : Check Edge := do
  let p ← tuple v 2
  return (← keyIndex true p[0]!, ← keyIndex false p[1]!)

private def keys (v : Json) (diff : Bool) : Check Nat := do
  let mut m := 0
  for k in (← v.getArr?) do
    m := m ||| (1 <<< (← keyIndex diff k))
  return m

private partial def card (x : Nat) : Nat :=
  if x == 0 then 0 else 1 + card (x &&& (x-1))

private def contains (bits i : Nat) : Bool := bits &&& (1 <<< i) != 0

private structure Board where
  rows : Nat
  cols : Nat
  holes : Array Edge
  capD : Array Nat
  capS : Array Nat
  forceD : Nat
  forceS : Nat
  firstD : Int
  firstS : Int
  squareTarget : Nat
  hR : Int
  hC : Int

private def board (rows cols : Nat) : Board := Id.run do
  let mut d := Array.replicate 59 0
  let mut s := Array.replicate 59 0
  let mut holes := #[]
  let mut sumR : Int := 0
  let mut sumC : Int := 0
  let mut squares := 0
  let mut r1 : Int := 0
  let mut c1 : Int := 0
  let mut r2 : Int := 0
  let mut c2 : Int := 0
  for r in [:30] do
    let centered : Int := 2*(r : Int)-29
    if !contains rows r then
      sumR := sumR+r
      squares := squares+r*r
      r1 := r1+centered
      r2 := r2+centered*centered
    if !contains cols r then
      sumC := sumC+r
      squares := squares+r*r
      c1 := c1+centered
      c2 := c2+centered*centered
    for c in [:30] do
      let i := r+29-c
      let j := r+c
      if contains rows r && contains cols c then
        holes := holes.push (i,j)
      else if !contains rows r && !contains cols c then
        d := d.modify i (·+1)
        s := s.modify j (·+1)
  let mut fd := 0
  let mut fs := 0
  for (i,j) in holes do
    if d[i]! < 2 then fs := fs ||| (1 <<< j)
    if s[j]! < 2 then fd := fd ||| (1 <<< i)
  return ⟨rows,cols,holes,d,s,fd,fs,2*(sumR-sumC),2*(sumR+sumC),4*squares,
           21*r1*r1-5*r2,21*c1*c1-5*c2⟩

private def matching (b : Board) (v : Json) (fd fs : Nat) : Check Unit := do
  let pairs ← v.getArr?
  requireC (pairs.size+card fd+card fs>30) "insufficient matching"
  let mut d := fd
  let mut s := fs
  for p in pairs do
    let (i,j) ← edge p
    requireC (b.holes.contains (i,j)) "matching edge is not an uncovered-axis target"
    requireC (!contains d i && !contains s j) "matching or forced vertices overlap"
    d := d ||| (1 <<< i)
    s := s ||| (1 <<< j)

-- Enumerate remaining key multisets in increasing-key order. A key can
-- occur once, or twice when the active rectangle has two supporting cells.
private partial def extend (choices : Array (Int × Nat)) (start left : Nat) (total : Int)
    (squares : Nat) (out : Array Nat) : Array Nat := Id.run do
  if left==0 then return if total==0 then out.push squares else out
  if start>=choices.size then return out
  if total < (left:Int)*choices[start]!.1 || total>(left:Int)*choices.back!.1 then return out
  let mut out := out
  for j in [start:choices.size] do
    let (k,cap) := choices[j]!
    if (left:Int)*k>total then break
    let k2 := k.natAbs*k.natAbs
    out := extend choices (j+1) (left-1) (total-k) (squares+k2) out
    if left≥2 && cap≥2 then
      out := extend choices (j+1) (left-2) (total-2*k) (squares+2*k2) out
  return out

private def moments (mask : Nat) (cap : Array Nat) (offset first : Int) : Check (Array Nat) := do
  let mut options := #[]
  let mut sum := first
  let mut sq := 0
  let left := 30-2*card mask
  requireC (card mask ≤ 15 && left ≤ 6) "invalid marginal dimension"
  for i in [:59] do
    let k : Int := (i:Int)-offset
    if contains mask i then
      sum := sum-2*k
      sq := sq+2*k.natAbs*k.natAbs
    else if cap[i]! > 0 then options := options.push (k,cap[i]!)
  return extend options 0 left sum sq #[]

private structure Stats where
  quotas : Nat := 0
  moments : Nat := 0
  deriving Inhabited

private partial def tree (b : Board) (d s : Nat) (node : Json) : Check Stats := do
  if node == Json.str "Q" then
    requireC (card d>15 || card s>15) "quota leaf within quota"
    return {quotas := 1}
  if node == Json.str "M" then
    requireC (b.holes.all fun (i,j) => contains d i || contains s j) "unfinished cover"
    let dm ← moments d b.capD 29 b.firstD
    let sm ← moments s b.capS 0 b.firstS
    requireC (!(dm.any fun x => sm.any fun y => x+y==b.squareTarget)) "compatible marginal moments"
    return {moments := 1}
  let p ← tuple node 4
  let family ← p[0]!.getNat?
  requireC (family<2) "invalid split family"
  let diff := family==0
  let k ← keyIndex diff p[1]!
  let mut neighbors := 0
  for (i,j) in b.holes do
    if !contains d i && !contains s j then
      if diff && i==k then neighbors := neighbors ||| (1 <<< j)
      if !diff && j==k then neighbors := neighbors ||| (1 <<< i)
  requireC (neighbors != 0) "invalid cover split"
  let add := 1 <<< k
  let l ← if diff then tree b (d ||| add) s p[2]! else tree b d (s ||| add) p[2]!
  let r ← if diff then tree b d (s ||| neighbors) p[3]! else tree b (d ||| neighbors) s p[3]!
  return ⟨l.quotas+r.quotas,l.moments+r.moments⟩

private def verify (json : Json) : Check (Nat × Nat × Nat × Stats) := do
  let recd ← tuple json 8
  let family ← recd[0]!.getNat?
  let e ← recd[1]!.getNat?
  let u ← recd[2]!.getNat?
  let v ← recd[3]!.getNat?
  let t ← recd[4]!.getNat?
  let w ← recd[5]!.getNat?
  requireC (family==29 || family==30) "unexpected frame case"
  requireC (14≤e && e<30 && t+e<30 && w+e<30) "invalid translated span"
  requireC (u<1<<<e && v<1<<<e && contains u 0 && contains v 0 &&
            card u==14 && card v==14) "invalid normalized axis"
  let rows := (u ||| (1<<<e)) <<< t
  let cols := (v ||| (1<<<e)) <<< w
  let b := board rows cols
  requireC (if family==29 then b.firstD==0 else b.hR==b.hC) "axis invariant fails"
  let kind ← recd[6]!.getStr?
  let p := recd[7]!
  let result ← match kind with
    | "survives" => tree b b.forceD b.forceS p
    | "uncoverable" => do
      let (i,j) ← edge p
      requireC (b.holes.contains (i,j) && b.capD[i]!<2 && b.capS[j]!<2) "hole is coverable"
      pure {}
    | "matching" => do matching b p 0 0; pure {}
    | "forced_lane_capacity" | "matching_after_forcing" => do
      let x ← tuple p (if kind=="forced_lane_capacity" then 2 else 3)
      let fd ← keys x[0]! true
      let fs ← keys x[1]! false
      requireC (fd &&& b.forceD == fd && fs &&& b.forceS == fs) "unforced keys"
      if kind=="matching_after_forcing" then matching b x[2]! fd fs
      else requireC (card fd>15 || card fs>15) "forced count within quota"
      pure {}
    | _ => throw "unknown certificate kind"
  return (family,rows,cols,result)

def run (args : List String) : IO Unit := do
  let path :: mode :: domains := args | throw (IO.userError "usage: LocalCertificates file.jsonl sample | full domain29 domain30")
  if mode != "sample" && mode != "full" then throw (IO.userError "invalid mode")
  let started ← IO.monoMsNow
  let mut seen : Std.HashSet (Nat × Nat × Nat) := {}
  let mut n29 := 0
  let mut n30 := 0
  let mut leaves29 : Stats := {}
  let mut leaves30 : Stats := {}
  for line in (← IO.FS.lines path) do
    let x ← IO.ofExcept (Json.parse line >>= verify)
    let (fam,r,c,localStats) := x
    let key := (fam,r,c)
    if seen.contains key then throw (IO.userError "duplicate frame/axis record")
    seen := seen.insert key
    if fam==29 then
      n29 := n29+1
      leaves29 := ⟨leaves29.quotas+localStats.quotas,leaves29.moments+localStats.moments⟩
    else
      n30 := n30+1
      leaves30 := ⟨leaves30.quotas+localStats.quotas,leaves30.moments+localStats.moments⟩
  if mode=="full" && (n29 != 9016 || n30 != 11691) then throw (IO.userError "missing records")
  if mode=="full" then
    let f29 :: f30 :: [] := domains | throw (IO.userError "full mode requires both domain files")
    for (fam, file) in [(29,f29),(30,f30)] do
      for line in (← IO.FS.lines file) do
        let some [e,u,v,t,w] := (line.splitOn " ").mapM String.toNat?
          | throw (IO.userError "malformed axis record")
        if e<14 || e≥30 || t+e≥30 || w+e≥30 then throw (IO.userError "invalid domain span")
        let key := (fam,(u ||| (1 <<< e)) <<< t,(v ||| (1 <<< e)) <<< w)
        if !seen.contains key then throw (IO.userError "absent or duplicated domain axis")
        seen := seen.erase key
    if !seen.isEmpty then throw (IO.userError "extra input axis")
  IO.println s!"29-line records {n29}, quota leaves {leaves29.quotas}, moment leaves {leaves29.moments}"
  IO.println s!"30-line equal-span records {n30}, quota leaves {leaves30.quotas}, moment leaves {leaves30.moments}"
  IO.println s!"PASS elapsed milliseconds {(← IO.monoMsNow)-started}"

end Gardner.LocalCertificates

def main := Gardner.LocalCertificates.run
