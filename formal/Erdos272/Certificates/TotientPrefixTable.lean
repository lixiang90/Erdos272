module

public meta import Lean

/-! Expand the two cumulative totient tables into ordinary balanced comparisons. -/
public meta section
namespace JSP233.TotientPrefixTable
open Lean

private def words (weighted : Bool) : Array Nat := Id.run do
  let last := 29436
  let mut phi := Array.range last
  for p in [2:last] do
    if phi[p]! == p then
      let mut j := p
      while j < last do
        let v := phi[j]!
        phi := phi.set! j (v-v/p)
        j := j+p
  let bits := if weighted then 48 else 32
  let mut sum := 0
  let mut word := 0
  let mut packed := #[]
  for n in [:920*32] do
    if n ≤ last then
      word := word + (sum <<< (bits*(n%32)))
    if n%32 == 31 then
      packed := packed.push word
      word := 0
    if n < last then
      sum := sum + (if weighted then n*phi[n]! else phi[n]!)
  return packed

private partial def lookup (i : Term) (v : Array Nat) (lo hi : Nat) : MacroM Term := do
  if hi ≤ lo+1 then return quote v[lo]!
  let mid := (lo+hi)/2
  let left ← lookup i v lo mid
  let right ← lookup i v mid hi
  `(if $i < $(quote mid) then $left else $right)

macro "totientPrefix32" i:term:max : term => lookup i (words false) 0 920
macro "totientMoment48" i:term:max : term => lookup i (words true) 0 920

end JSP233.TotientPrefixTable
