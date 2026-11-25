module

public meta import Lean

/-! The 249-step certificate uses many tables on the same eight-bit index.
Expand their integer entries to the original balanced comparisons during
elaboration. The resulting definitions contain only integer literals and
natural-number comparisons. Trailing zero entries may be omitted. -/
public meta section
namespace JSP233.StaircaseTable
open Lean

declare_syntax_cat staircaseEntry
syntax num : staircaseEntry
syntax "-" num : staircaseEntry

private def value : TSyntax `staircaseEntry → MacroM Int
  | `(staircaseEntry| $n:num) => pure (.ofNat n.getNat)
  | `(staircaseEntry| - $n:num) => pure (-(n.getNat : Int))
  | stx => Macro.throwErrorAt stx "expected a signed integer"

private def literal (signed : Bool) (v : Int) : MacroM Term := do
  match v with
  | .ofNat n => if signed then `(Int.ofNat $(quote n)) else pure (quote n)
  | .negSucc n =>
    if signed then `(Int.negSucc $(quote n)) else Macro.throwError "negative entry in a natural table"

private def tree (i : Term) (entries : Array Int) (signed : Bool) (lo : Nat) : Nat → MacroM Term
  | 0 => literal signed (entries[lo]?.getD 0)
  | depth+1 => do
    let v := entries[lo]?.getD 0
    let half := 2^depth
    if lo ≥ entries.size || (List.range (2*half)).all (fun j => (entries[lo+j]?.getD 0)==v) then
      return ← literal signed v
    let mid := lo+half
    let left ← tree i entries signed lo depth
    let right ← tree i entries signed mid depth
    `(if $i < $(quote mid) then $left else $right)

private def expand (i : Term) (xs : Array (TSyntax `staircaseEntry)) (signed : Bool) : MacroM Term := do
  if xs.size > 256 then Macro.throwError "at most 256 entries fit in a staircase row"
  tree i (← xs.mapM value) signed 0 8

macro "staircaseInt" i:term:max " [" xs:staircaseEntry,* "]" : term =>
  expand i xs.getElems true

macro "staircaseNat" i:term:max " [" xs:staircaseEntry,* "]" : term =>
  expand i xs.getElems false

end JSP233.StaircaseTable
