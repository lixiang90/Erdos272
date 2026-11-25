module

public meta import Erdos272.Certificates.StaircaseTable

/-! Candidate rows for the 249-step staircase. The local certificate checks
each gcd count and each inequality after these rows expand to numerals. -/
public meta section
namespace JSP233.StaircaseRecurrence
open Lean JSP233.StaircaseTable

private def height : Nat := 250

private def mixRow (r : Nat) : Array Nat := Id.run do
  let mut row := #[0]
  let mut count := 0
  for n in [:height] do
    if 0<n && n != r && n.gcd r==1 then count := count+1
    row := row.push count
  return row

private structure Tables where
  potential : Array (Array Int)
  suffix : Array (Array Int)
  mix : Array (Array Nat)

private def tables : Tables := Id.run do
  let mix := (Array.range height).map mixRow
  let phi := (Array.range (height+1)).map (fun r =>
    ((List.range r).filter (fun n => n.gcd r==1)).length)
  let mut current : Array Int := #[0]
  let mut left := 0
  for h in [:height] do
    if h≥3 then left := left+phi[h]!
    current := current.push ((h-2:Nat)-(left:Int))
  let mut potentials := #[current]
  let mut suffixes := #[]
  for r in [1:height] do
    let mut suffix := current
    for j in [:height] do
      let i := height-1-j
      suffix := suffix.set! i (max current[i]! suffix[i+1]!)
    suffixes := suffixes.push suffix
    let counts := mix[r]!
    current := #[suffix[0]!]
    for h in [:height] do
      let offset : Int := (h+1-(3-r):Nat)
      let score := offset-(counts[h+1]!:Int)-(if r≥3 then (phi[r]!:Int) else 0)
      current := current.push (score+suffix[h+1]!)
    potentials := potentials.push current
  return ⟨potentials,suffixes,mix⟩

private def entries (row : Array Int) : MacroM (Array (TSyntax `staircaseEntry)) := do
  let mut xs := #[]
  for v in row do
    let val ← match v with
      | .ofNat n => `(staircaseEntry| $(Syntax.mkNumLit (toString n)):num)
      | .negSucc n => `(staircaseEntry| - $(Syntax.mkNumLit (toString (n+1))):num)
    xs := xs.push val
  return xs

macro "staircasePotential" i:term:max r:num : term => do
  let some row := tables.potential[r.getNat]? | Macro.throwError "potential row out of range"
  let xs ← entries row
  `(staircaseInt $i [$xs,*])

macro "staircaseSuffix" i:term:max r:num : term => do
  let some row := tables.suffix[r.getNat]? | Macro.throwError "suffix row out of range"
  let xs ← entries row
  `(staircaseInt $i [$xs,*])

macro "staircaseMix" i:term:max r:num : term => do
  let some row := tables.mix[r.getNat]? | Macro.throwError "count row out of range"
  let xs ← entries (row.map Int.ofNat)
  `(staircaseNat $i [$xs,*])

end JSP233.StaircaseRecurrence
