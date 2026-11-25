module

public meta import Lean

/-! Generate the point witnesses for consecutive totative blocks. Each
list is checked by the ordinary validity theorem before the blocks join. -/
public meta section
namespace JSP233.CoprimeBlock
open Lean

private structure Bound where
  id : Ident
  start : Nat
  width : Nat
  count : Nat
  debt : Nat
  deriving Inhabited

private def localId (i : Nat) : Ident := mkIdent (.mkSimple ("h" ++ toString i))

private def statement (m a : Nat) (b : Bound) : MacroM Term := do
  let estimate := mkIdent `JSP233.AffineWitness47.BlockEstimate
  `($estimate $(quote m) $(quote a) $(quote b.start) $(quote b.width) $(quote b.count) $(quote b.debt))

macro "coprimeBlock " m:num a:num start:num width:num leaves:num : term => do
  let m := m.getNat
  let a := a.getNat
  let start := start.getNat
  let width := width.getNat
  let leaves := leaves.getNat
  if leaves==0 then Macro.throwError "expected a nonempty block"
  let valid := mkIdent `JSP233.AffineWitness47.estimate_of_valid
  let join := mkIdent `JSP233.AffineWitness47.estimate_join
  let mut steps : Array (TSyntax `tactic) := #[]
  let mut level : Array Bound := #[]
  for i in [:leaves] do
    let lo := start+i*width
    let mut points : Array Term := #[]
    let mut debt := 0
    for j in [:width] do
      if (lo+j+1).gcd m == 1 then
        debt := max debt (j-a*points.size)
        points := points.push (quote (j+1))
    debt := max debt (width-a*points.size)
    let b : Bound := ⟨localId i,lo,width,points.size,debt⟩
    let goal ← statement m a b
    steps := steps.push (← `(tactic| have $(b.id) : $goal := $valid _ _ _ _ _ [$points,*] (by decide)))
    level := level.push b
  while level.size>1 do
    let mut next := #[]
    for i in [:level.size/2] do
      let l := level[2*i]!
      let r := level[2*i+1]!
      let b : Bound := ⟨localId steps.size,l.start,l.width+r.width,l.count+r.count,
        max l.debt (l.width+r.debt-a*l.count)⟩
      let goal ← statement m a b
      steps := steps.push (← `(tactic| have $(b.id) : $goal := $join $(l.id) $(r.id)))
      next := next.push b
    if level.size%2==1 then next := next.push level.back!
    level := next
  steps := steps.push (← `(tactic| exact $(level[0]!.id)))
  `(by $steps:tactic*)

end JSP233.CoprimeBlock
