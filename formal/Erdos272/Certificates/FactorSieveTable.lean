module

public meta import Lean

/-! Generate the packed least-prime-factor table used by the ordinary
divisibility and primality certificates. All table entries in the resulting
declarations are natural-number literals. -/
public meta section
namespace JSP233.FactorSieveTable
open Lean Elab Command

private def packedWords : Array Nat := Id.run do
  let oddCount := 1670000 / 2
  let mut least := ByteArray.mk (Array.replicate oddCount 0)
  let mut rank := 1
  for p in [3:1293:2] do
    if least[p/2]! == 0 then
      rank := rank+1
      let mut j := p*p/2
      while j < oddCount do
        if least[j]! == 0 then
          least := least.set! j rank.toUInt8
        j := j+p
  let mut words := #[]
  for block in [:16384] do
    let mut word := 0
    for k in [:64] do
      let j := block*64+63-k
      let value := if h : j < least.size then least[j].toNat else 0
      word := word*256+(if value ≤ 6 then 0 else value)
    words := words.push word
  return words

private def nodeName (n : Nat) : Ident := mkIdent (.mkSimple ("packNode_" ++ toString n))

private def tree (i : Term) (entries : Array Term) (first step : Nat) :
    Nat → Nat → CommandElabM Term
  | offset, 0 => pure entries[offset]!
  | offset, depth+1 => do
    let middle := offset+2^depth
    let left ← tree i entries first step offset depth
    let right ← tree i entries first step middle depth
    `(if $i < $(quote (first+middle*step)) then $left else $right)

private def emitNode (i : Ident) (number first step depth : Nat) (entries : Array Term) :
    CommandElabM Term := do
  let name := nodeName number
  let rhs ← tree i entries first step 0 depth
  elabCommand (← `(def $name ($i : Nat) : Nat := $rhs))
  `($name $i)

/-- The older lookup uses four levels of named subtrees, with 4, 16, 16
and 16 branches. Preserve the comparisons and each subtree's external name. -/
elab "factorSieveTable209" : command => do
  let words := packedWords
  let i := mkIdent `i
  let mut quarters := #[]
  for q in [:4] do
    let mut blocks := #[]
    for b in [:16] do
      let mut leaves := #[]
      let parent := 2+273*q+17*b
      let first := 4096*q+256*b
      for g in [:16] do
        let pos := first+16*g
        let entries := (words.extract pos (pos+16)).map (fun n => (quote n : Term))
        leaves := leaves.push (← emitNode i (parent+1+g) pos 1 4 entries)
      blocks := blocks.push (← emitNode i parent first 16 4 leaves)
    quarters := quarters.push (← emitNode i (1+273*q) (4096*q) 256 4 blocks)
  discard <| emitNode i 0 0 4096 2 quarters

end JSP233.FactorSieveTable
