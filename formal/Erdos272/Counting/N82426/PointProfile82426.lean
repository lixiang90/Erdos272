module

public import Erdos272.Counting.N82426.PointArithmetic82426
public import Erdos272.Retention.N82427.RecoveryChain82427

@[expose] public section

set_option Elab.async false

namespace JSP233.PointRecovery82426
open StarCompletion APGeometry DenseDeletion40 HarmonicAbel29 RootModel291012
open RecoveryCaps213 RecoveryProfiles291012 WitnessInterval43
open LocalRecovery82427 RecoveryCertificates82427
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem raw_profile_from_caps {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start N c L R F P T)
    (hlo : 19≤N) (hhi : N≤720896) (hc : Caps (LogLocal 0) (HLocal 0) N)
    (hE : ((Omitted N c F).card : ℝ)≤alpha*N+beta*Width N L R+constant) :
    RawProfile N L (Width N L R) (HLocal 0+433/100+alpha)
      (HLocal 0+beta) (872+constant) := by
  have hr := GenericRecovery291012.actual_original_raw_profile_local hlo hhi
    g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground g.root
    g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids
    g.left_upper g.outside
  have hnpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (Nat.cast_nonneg (α := ℝ) N)
  have hwpaid := mul_le_mul_of_nonneg_right hc.harmonic_le (width_nonnegative g)
  change ((TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)).card : ℝ)≤_ at hE
  dsimp only [RawProfile, Coeff, Width, HLocal, CovarianceFamily214.MiddleCost,
    LocalRecovery208.GeometryCost] at *
  nlinarith only [hr, hE, hnpaid, hwpaid]

theorem raw_profile_lower {c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    {alpha beta constant : ℝ} (g : Start 82426 c L R F P T)
    (hE : ((Omitted 82426 c F).card : ℝ)≤alpha*82426+beta*Width 82426 L R+constant) :
    RawProfile 82426 L (Width 82426 L R) (HLocal 0+433/100+alpha)
      (HLocal 0+beta) (872+constant) := by
  have hc := LocalRecovery82427.actual_caps (k := 0) (by decide)
    (by decide : 10000≤82426) (by decide : 82426≤High 0)
  have hp := raw_profile_from_caps (N := 82426) (alpha := alpha) (beta := beta)
    (constant := constant) g (by decide) (by decide) hc
    (by simpa only [Nat.cast_ofNat] using hE)
  simpa only [Nat.cast_ofNat] using hp

theorem omitted_subset {c : ℕ} {F : Finset (Finset ℤ)} : Omitted 82426 c F⊆F :=
  (Finset.filter_subset _ _).trans (actual_deleted_subset 82426 12 F)

theorem omitted_bad {c : ℕ} {F : Finset (Finset ℤ)} : ∀ S∈Omitted 82426 c F, ¬IsAP S :=
  fun _ hS => (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.1

#print axioms raw_profile_from_caps
#print axioms raw_profile_lower
#print axioms omitted_subset
#print axioms omitted_bad
end
end JSP233.PointRecovery82426
