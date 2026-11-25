module

public import Erdos272.Retention.N20258.RootProfile20258
public import Erdos272.Arithmetic.N291012.GenericRecovery291012

@[expose] public section
namespace JSP233.RootDimensions20258
open StarCompletion APGeometry DenseDeletion40
noncomputable section
set_option autoImplicit false

/-- The two endpoint dimensions on the very same family and witnesses used
by the original raw profile. -/
theorem actual_axes {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (hc : (c : ℤ) ∈ Ground N)
    (legal : Legal (Ground N) F) (near : B N ≤ F.card)
    (cL : c < L) (lr : L ≤ R) (rn : R ≤ N)
    (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → (c : ℤ) ∈ S)
    (p : P ∈ Retained N 12 F) (pc : (c : ℤ) ∉ P) (pl : ∀ z ∈ P, (L : ℤ) ≤ z)
    (t : T ∈ Retained N 12 F) (tc : (c : ℤ) ∉ T) (tr : ∀ z ∈ T, z ≤ (R : ℤ))
    (outside : ∀ S ∈ Retained N 12 F, (c : ℤ) ∉ S →
      (∃ u ∈ S, u ≤ (L : ℤ)) ∧ ∃ v ∈ S, (R : ℤ) ≤ v) :
    (L : ℝ) < N/6 ∧ (L : ℝ)+((N : ℝ)-R) < N/4 := by
  have raw := GenericRecovery291012.actual_original_raw_profile_local (by omega : 19 ≤ N)
    (by omega : N ≤ 720896) hc legal near cL lr rn root p pc pl t tc tr outside
  exact RootProfile20258.actual_axes_of_profile lo hi hc legal near root (by omega) lr rn raw

#print axioms actual_axes
end
end JSP233.RootDimensions20258
