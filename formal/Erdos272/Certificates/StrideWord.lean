module

public meta import Lean

/-! Each symbol stores one positive stride from a source-cover row.
The expansion is the original list of natural number literals. -/
public meta section
namespace JSP233.StrideWord
open Lean

macro "strideWord" s:str : term => do
  let mut entries : Array (TSyntax `term) := #[]
  for c in s.getString.toList do
    let value ←
      if 'A' ≤ c && c ≤ 'Z' then pure (c.toNat-'A'.toNat+1)
      else if 'a' ≤ c && c ≤ 'z' then pure (c.toNat-'a'.toNat+27)
      else if '0' ≤ c && c ≤ '9' then pure (c.toNat-'0'.toNat+53)
      else Macro.throwErrorAt s "invalid stride symbol"
    entries := entries.push (quote value)
  `([$entries,*])

end JSP233.StrideWord
