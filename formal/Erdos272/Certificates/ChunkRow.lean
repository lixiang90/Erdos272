module

public meta import Lean

/-! Consecutive summands provide the inputs for a balanced tree of chunk
proofs. Every internal total is checked by the ordinary append theorem. -/
public meta section
namespace JSP233.ChunkRow
open Lean

private structure Entry where
  name : Ident
  start : Nat
  length : Nat
  totals : Array Nat
  deriving Inhabited

private def numbered (row : Ident) (kind : String) (n : Nat) : Ident :=
  let digits := toString n
  let zeros := String.ofList (List.replicate (3-digits.length) '0')
  mkIdent (.mkSimple (row.getId.toString ++ "_" ++ kind ++ zeros ++ digits))

private def declare (row : Ident) (e : Entry) (body : Term) : MacroM Command := do
  let base := mkIdent (.str `JSP233.CleanupRecipes208 row.getId.toString)
  let fact := mkIdent `JSP233.CleanupEval208.ChunkFacts
  let convert := mkIdent `JSP233.CleanupMachineSound208.toRow
  let a := quote e.totals[0]!
  let b := quote e.totals[1]!
  let c := quote e.totals[2]!
  let d := quote e.totals[3]!
  let f := quote e.totals[4]!
  `(command| theorem $(e.name) : $fact ($convert $base) $(quote e.start) $(quote e.length)
      ⟨$a,$b,$c,$d,$f⟩ := $body)

syntax chunkEntry := "(" num "," num "," num "," num "," num "," num "," term ")"
syntax "chunkRow " ident " [" chunkEntry,+ "]" : command

macro_rules
  | `(command| chunkRow $row:ident [$entries:chunkEntry,*]) => do
    let mut commands := #[]
    let mut level : Array Entry := #[]
    let mut nextStart := 1
    for entry in entries.getElems do
      let `(chunkEntry| ($len:num,$a:num,$b:num,$c:num,$d:num,$f:num,$proof:term)) := entry
        | Macro.throwUnsupported
      let e : Entry := ⟨numbered row "leaf" level.size, nextStart, len.getNat,
        #[a.getNat,b.getNat,c.getNat,d.getNat,f.getNat]⟩
      commands := commands.push (← declare row e proof)
      level := level.push e
      nextStart := nextStart+len.getNat
    let append := mkIdent `JSP233.CleanupSegments208.append_exact
    let mut serial := 0
    while level.size>1 do
      let mut next := #[]
      for i in [:level.size/2] do
        let left := level[2*i]!
        let right := level[2*i+1]!
        let e : Entry := ⟨numbered row "node" serial, left.start, left.length+right.length,
          left.totals.zipWith (·+·) right.totals⟩
        commands := commands.push (← declare row e (← `($append $(left.name) $(right.name) rfl rfl rfl)))
        next := next.push e
        serial := serial+1
      if level.size%2==1 then next := next.push level.back!
      level := next
    return mkNullNode (commands.map (·.raw))
end JSP233.ChunkRow
