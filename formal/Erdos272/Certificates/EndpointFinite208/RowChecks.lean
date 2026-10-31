import Erdos272.Counting.EndpointGate208

/-! Assemble row certificates without reducing an entire block at once. -/
namespace JSP233.EndpointFinite208
open EndpointGate208
set_option autoImplicit false

theorem checked_cons {G a h : ℕ} {r : Row} {rs : List Row}
    (hr : RowCondition G a h r)
    (hs : CheckRows G (r.last + 1) r.nextH rs = true) :
    CheckRows G a h (r :: rs) = true := by
  simpa only [CheckRows, Bool.and_eq_true, decide_eq_true_eq] using And.intro hr hs

#print axioms checked_cons
end JSP233.EndpointFinite208
