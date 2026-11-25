module

public meta import Lean

/-! Generate candidate endpoints from the same integer budget checked by
EndpointGate208. Each block still proves both CheckRows and RowsEnd in the kernel. -/
public meta section
namespace JSP233.EndpointFinite208
open Lean

private def rootAndCount (t : Nat) : Nat × Nat := Id.run do
  let mut d := 1
  let mut sum := 0
  while d*d≤t do
    sum := sum+t/d
    d := d+1
  let r := d-1
  return (r, 2*sum-r*r-t-t/2)

macro "greedyEndpointRows " first:num startingSum:num stop:num : term => do
  let scale := 1000000000000
  let mut a := first.getNat
  let mut h := startingSum.getNat
  let endAt := stop.getNat
  let mut rows : Array Term := #[]
  while a<endAt do
    let budget := 25*a*h+275*scale
    let fits := fun b => 25*scale*(rootAndCount (b-1)).2+48*a*scale≤budget
    if !(decide (fits a)) then Macro.throwError "no valid endpoint at the start of this row"
    let mut low := a
    let mut high := endAt-1
    while low<high do
      let mid := (low+high+1)/2
      if fits mid then low := mid else high := mid-1
    for j in [a+1:low+2] do h := h+scale/j
    let r := (rootAndCount (low-1)).1
    rows := rows.push (← `(⟨$(quote low), $(quote r), $(quote h)⟩))
    a := low+1
  `([$rows,*])

end JSP233.EndpointFinite208
