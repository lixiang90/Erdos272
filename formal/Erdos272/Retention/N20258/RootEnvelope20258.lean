module

public import Erdos272.Retention.N20258.RootDimensions20258
public import Erdos272.Resources.N291012.RetainedStart291012
public import Erdos272.Arithmetic.N20258.RootRecoverySquares20258

@[expose] public section
namespace JSP233.RootEnvelope20258
open StarCompletion DenseDeletion40 HarmonicAbel29
set_option autoImplicit false
noncomputable section

/-- Both endpoint squares can consume the original raw profile directly. -/
theorem actual_profile {N c L R : ℕ} {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (lo : 19227 ≤ N) (hi : N < 2^16) (g : RootModel291012.Start N c L R F P T) :
    RootRecoverySquares20258.profile L ((N : ℝ)-R) ≤
      RootRecoverySquares20258.rate N*(N : ℝ)+71*L+12*((N : ℝ)-R)+872 := by
  have pos : 1 ≤ L := by have h := g.root_left; omega
  have raw := GenericRecovery291012.actual_original_raw_profile_local (by omega : 19 ≤ N)
    (by omega : N ≤ 720896) g.root_mem g.legal g.near_card g.root_left g.left_right g.right_ground
    g.root g.right_member g.right_avoids g.right_lower g.left_member g.left_avoids g.left_upper g.outside
  have axes := RootProfile20258.actual_axes_of_profile lo hi g.root_mem g.legal g.near_card
    g.root pos g.left_right g.right_ground raw
  have left : 6*L < N := by
    exact_mod_cast (show 6*(L : ℝ) < N by linarith only [axes.1])
  have coeff := DyadicWidth20258.coefficient_fringe pos (by omega : L < 2^14)
  have term := mul_le_mul_of_nonneg_left coeff (Nat.cast_nonneg (α := ℝ) L)
  unfold DyadicWidth20258.coefficient at term
  have hN : Harmonic N ≤ 12 := (HarmonicSharp39.actual_harmonic_tight N 16 hi).trans (by norm_num)
  have ground : (R : ℝ) ≤ N := by exact_mod_cast g.right_ground
  have hw := mul_le_mul_of_nonneg_left hN (add_nonneg (Nat.cast_nonneg (α := ℝ) L) (sub_nonneg.mpr ground))
  have hRate : Harmonic N+1233/100 ≤ RootRecoverySquares20258.rate N := by
    by_cases early : N < 20000
    · have earlyR : (N : ℝ) < 20000 := by exact_mod_cast early
      have h := HarmonicSharp39.actual_harmonic_tight N 15 (by omega)
      rw [RootRecoverySquares20258.rate,if_pos earlyR]
      norm_num at h ⊢
      linarith only [h]
    · have laterR : (20000 : ℝ) ≤ N := by exact_mod_cast (Nat.le_of_not_gt early)
      rw [RootRecoverySquares20258.rate,if_neg (not_lt_of_ge laterR)]
      linarith only [hN]
  have hn := mul_le_mul_of_nonneg_right hRate (Nat.cast_nonneg (α := ℝ) N)
  have e := RootAvoiderCount20258.actual_omitted (by omega : 9000 ≤ N) hi g.root_mem g.legal g.near_card g.root
  have eR : ((TerminalDeficit51.OmittedAvoiders N 12 F (c : ℤ)).card : ℝ) ≤ 8*N := by
    exact_mod_cast e
  unfold Recovery208.WidthProfile CovarianceFamily214.MiddleCost CovarianceScalar213.Polynomial
    LocalRecovery208.GeometryCost at raw
  unfold RootRecoverySquares20258.profile
  linarith only [raw,term,eR,hn,hw,Nat.cast_nonneg (α := ℝ) N]

#print axioms actual_profile
end
end JSP233.RootEnvelope20258
