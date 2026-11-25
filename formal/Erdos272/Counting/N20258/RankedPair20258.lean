module

public import Erdos272.Counting.N20258.TwoTransversals20258

@[expose] public section
namespace JSP233.RankedPair20258
open StarCompletion PrivatePairExistence AnchorCompletion38
open scoped Classical
noncomputable section
set_option autoImplicit false

/-- Avoidance of every earlier site is a reduction of the physical ground
for the entire two-point bucket, including its private third-point witnesses. -/
theorem actual_pair {N : ℕ} {F : Finset (Finset ℤ)} (legal : Legal (Ground N) F)
    {x y : ℤ} (xy : x ≠ y) (prior : Finset ℤ) (sites : prior ⊆ Ground N) :
    ((CrookedMembers F).filter (fun S => x ∈ S ∧ y ∈ S ∧ Disjoint S prior)).card ≤
      N-prior.card-2 := by
  let H := (CrookedMembers F).filter (fun S => x ∈ S ∧ y ∈ S ∧ Disjoint S prior)
  change H.card ≤ _
  by_cases ne : H.Nonempty
  · have mem {S : Finset ℤ} (hS : S ∈ H) : S ∈ F :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
    have facts {S : Finset ℤ} (hS : S ∈ H) : x ∈ S ∧ y ∈ S ∧ Disjoint S prior :=
      (Finset.mem_filter.mp hS).2
    have small : Legal (Ground N \ prior) H := by
      refine ⟨?_, fun S hS T hT => legal.2 S (mem hS) T (mem hT)⟩
      intro S hS z hz
      exact Finset.mem_sdiff.mpr ⟨legal.1 S (mem hS) hz,Finset.disjoint_left.mp (facts hS).2.2 hz⟩
    have bound := actual_two_point_crooked_ground_capacity _ H _ _ xy ne small
      (fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2)
      (fun _ hS => (facts hS).1) (fun _ hS => (facts hS).2.1)
    rw [Finset.card_sdiff_of_subset sites,ground_card] at bound
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp ne]

/-- Sum of the twice-counted first-hit budgets, as a polynomial in the
cardinalities of the transversals and their intersection. -/
theorem first_hit_polynomial (D m s t i : ℤ) :
    i*(2*m*D-m*(m-1))-m*i*(i-1) +
        (s-i)*(t-i)*(2*D-2*i-(s-i-1)-(t-i-1)) =
      (2*D-m-s-t+2)*(s*t+i*(i+m-s-t))+m*s*t := by ring

#print axioms actual_pair
end
end JSP233.RankedPair20258
