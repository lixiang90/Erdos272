module

public import Erdos272.Arithmetic.N20258.DyadicWidth20258
public import Erdos272.Capacity.N20258.RootAvoiderCount20258

@[expose] public section
namespace JSP233.RootProfile20258
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29
noncomputable section
set_option autoImplicit false

/-- The unrefined historical profile uses the actual omitted subfamily as
its sole cardinality term. The root count supplies it inside the proof. -/
theorem actual_axes_of_profile {N L R : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (lo : 19227 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N) (legal : Legal (Ground N) F)
    (near : B N ≤ F.card) (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S)
    (pos : 1 ≤ L) (lr : L ≤ R) (rn : R ≤ N)
    (raw : let w := (L : ℝ)+((N : ℝ)-R)
      (114959/80000)*(L : ℝ)^2-(329/200)*L*w+w^2/2 ≤
      ((L : ℝ)*((Real.log L)^2/4+(7/10)*Real.log L+3/5)+850) +
      ((N : ℝ)*Harmonic N+(102/25)*N+(L : ℝ)*(2*Harmonic L+102/25)+w*Harmonic N+22) +
      (N : ℝ)/4+(TerminalDeficit51.OmittedAvoiders N 12 F c).card) :
    (L : ℝ) < N/6 ∧ (L : ℝ)+((N : ℝ)-R) < N/4 := by
  have omitted := RootAvoiderCount20258.actual_omitted (by omega : 9000 ≤ N) hi hc legal near root
  have rn' : (R : ℝ) ≤ N := by exact_mod_cast rn
  apply DyadicWidth20258.axes_of_raw (e := ((TerminalDeficit51.OmittedAvoiders N 12 F c).card : ℝ))
    lo hi pos (lr.trans rn) (add_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr rn'))
    (by exact_mod_cast omitted)
  dsimp only at raw
  unfold DyadicWidth20258.coefficient
  linarith only [raw]

#print axioms actual_axes_of_profile
end
end JSP233.RootProfile20258
