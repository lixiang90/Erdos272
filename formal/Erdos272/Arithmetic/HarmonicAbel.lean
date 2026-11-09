module

public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Actual harmonic sums and finite reverse Abel summation. The totient
specializations take the explicit prefix estimate as input; they prove the
weighted passage rather than assume an Abel inequality. -/
namespace JSP233.HarmonicAbel29
open scoped BigOperators

noncomputable def PrefixSum (b : ℕ → ℝ) (R : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 R, b r
noncomputable def Harmonic (R : ℕ) : ℝ := ∑ r ∈ Finset.Icc 1 R, (1 : ℝ) / r

theorem harmonic_eq_cast (R : ℕ) : Harmonic R = (harmonic R : ℝ) := by
  simp only [Harmonic, harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]

theorem harmonic_nonneg (R : ℕ) : 0 ≤ Harmonic R := by
  apply Finset.sum_nonneg
  intro r hr
  positivity

theorem harmonic_mono {r R : ℕ} (hr : r ≤ R) : Harmonic r ≤ Harmonic R := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1, (Finset.mem_Icc.mp hx).2.trans hr⟩
  · intro x hx hnx
    positivity

theorem harmonic_le_one_add_log (R : ℕ) : Harmonic R ≤ 1 + Real.log (R : ℝ) := by
  rw [harmonic_eq_cast]
  exact _root_.harmonic_le_one_add_log R

theorem reverse_abel_identity (b h : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) :
    (∑ r ∈ Finset.Icc 1 R, h r * b r) =
      h R * PrefixSum b R +
        ∑ r ∈ Finset.Ico 1 R, (h r - h (r+1)) * PrefixSum b r := by
  induction R, hR using Nat.le_induction with
  | base => simp [PrefixSum]
  | succ R hR ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hR]
    have hp : PrefixSum b (R+1) = PrefixSum b R + b (R+1) :=
      Finset.sum_Icc_succ_top (by omega) b
    rw [hp, ih]
    ring

theorem difference_mass (h : ℕ → ℝ) (R : ℕ) (hR : 1 ≤ R) :
    h R + (∑ r ∈ Finset.Ico 1 R, (h r - h (r+1))) = h 1 := by
  induction R, hR using Nat.le_induction with
  | base => simp
  | succ R hR ih =>
    rw [Finset.sum_Ico_succ_top hR]
    linarith

theorem weighted_lower_of_prefix_constant (b h : ℕ → ℝ) (R : ℕ)
    (E L : ℝ) (hR : 1 ≤ R) (hE : 0 ≤ E)
    (hpos : 0 ≤ h R) (hbound : h 1 ≤ L)
    (hstep : ∀ r, 1 ≤ r → r < R → h (r+1) ≤ h r)
    (hprefix : ∀ r ∈ Finset.Icc 1 R, -E ≤ PrefixSum b r) :
    -L * E ≤ ∑ r ∈ Finset.Icc 1 R, h r * b r := by
  have htop : h R * (-E) ≤ h R * PrefixSum b R :=
    mul_le_mul_of_nonneg_left (hprefix R (Finset.mem_Icc.mpr ⟨hR, le_rfl⟩)) hpos
  have hs : (∑ r ∈ Finset.Ico 1 R, (h r - h (r+1)) * (-E)) ≤
      ∑ r ∈ Finset.Ico 1 R, (h r - h (r+1)) * PrefixSum b r := by
    apply Finset.sum_le_sum
    intro r hr
    have hr' := Finset.mem_Ico.mp hr
    exact mul_le_mul_of_nonneg_left
      (hprefix r (Finset.mem_Icc.mpr ⟨hr'.1, hr'.2.le⟩))
      (sub_nonneg.mpr (hstep r hr'.1 hr'.2))
  rw [← Finset.sum_mul] at hs
  have hm := difference_mass h R hR
  have hpay := mul_le_mul_of_nonneg_right hbound hE
  rw [reverse_abel_identity b h R hR]
  nlinarith

theorem prefix_sub_constant (b : ℕ → ℝ) (a : ℝ) (R : ℕ) :
    PrefixSum (fun r => b r - a) R = PrefixSum b R - a * R := by
  simp [PrefixSum, Finset.sum_sub_distrib, nsmul_eq_mul, mul_comm]

theorem weighted_lower_of_prefix_lower (b h : ℕ → ℝ) (R : ℕ)
    (a L : ℝ) (hR : 1 ≤ R) (hpos : 0 ≤ h R) (hbound : h 1 ≤ L)
    (hstep : ∀ r, 1 ≤ r → r < R → h (r+1) ≤ h r)
    (hprefix : ∀ r ∈ Finset.Icc 1 R,
      a * r - 1 - Harmonic r ≤ PrefixSum b r) :
    a * (∑ r ∈ Finset.Icc 1 R, h r) - L * (1 + Harmonic R) ≤
      ∑ r ∈ Finset.Icc 1 R, h r * b r := by
  have hp : ∀ r ∈ Finset.Icc 1 R,
      -(1 + Harmonic R) ≤ PrefixSum (fun r => b r - a) r := by
    intro r hr
    rw [prefix_sub_constant]
    have hh := harmonic_mono (Finset.mem_Icc.mp hr).2
    have ht := hprefix r hr
    linarith
  have hw := weighted_lower_of_prefix_constant (fun r => b r - a) h R
    (1 + Harmonic R) L hR (by linarith [harmonic_nonneg R]) hpos hbound hstep hp
  have heq : (∑ r ∈ Finset.Icc 1 R, h r * (b r - a)) =
      (∑ r ∈ Finset.Icc 1 R, h r * b r) - a * (∑ r ∈ Finset.Icc 1 R, h r) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [heq] at hw
  linarith

theorem actual_totient_weighted_lower (h : ℕ → ℝ) (R : ℕ) (L : ℝ)
    (hR : 1 ≤ R) (hpos : 0 ≤ h R) (hbound : h 1 ≤ L)
    (hstep : ∀ r, 1 ≤ r → r < R → h (r+1) ≤ h r)
    (hprefix : ∀ r ∈ Finset.Icc 1 R,
      (607/1000 : ℝ) * r - 1 - (∑ d ∈ Finset.Icc 1 r, (1:ℝ) / d) ≤
        ∑ d ∈ Finset.Icc 1 r, (Nat.totient d : ℝ) / d) :
    (607/1000 : ℝ) * (∑ r ∈ Finset.Icc 1 R, h r) - L * (1 + Harmonic R) ≤
      ∑ r ∈ Finset.Icc 1 R, h r * ((Nat.totient r : ℝ) / r) := by
  exact weighted_lower_of_prefix_lower (fun r => (Nat.totient r : ℝ) / r)
    h R (607/1000) L hR hpos hbound hstep hprefix

theorem actual_totient_nat_profile_lower (h : ℕ → ℕ) (R L : ℕ)
    (hR : 1 ≤ R) (hbound : h 1 ≤ L)
    (hstep : ∀ r, 1 ≤ r → r < R → h (r+1) ≤ h r)
    (hprefix : ∀ r ∈ Finset.Icc 1 R,
      (607/1000 : ℝ) * r - 1 - (∑ d ∈ Finset.Icc 1 r, (1:ℝ) / d) ≤
        ∑ d ∈ Finset.Icc 1 r, (Nat.totient d : ℝ) / d) :
    (607/1000 : ℝ) * (∑ r ∈ Finset.Icc 1 R, (h r : ℝ)) -
      (L : ℝ) * (1 + Harmonic R) ≤
      ∑ r ∈ Finset.Icc 1 R, (h r : ℝ) * ((Nat.totient r : ℝ) / r) := by
  apply actual_totient_weighted_lower (fun r => (h r : ℝ)) R L hR
    (Nat.cast_nonneg _) (by exact_mod_cast hbound) ?_ hprefix
  intro r hr hrR
  exact_mod_cast hstep r hr hrR

#print axioms harmonic_eq_cast
#print axioms harmonic_nonneg
#print axioms harmonic_mono
#print axioms harmonic_le_one_add_log
#print axioms reverse_abel_identity
#print axioms difference_mass
#print axioms weighted_lower_of_prefix_constant
#print axioms prefix_sub_constant
#print axioms weighted_lower_of_prefix_lower
#print axioms actual_totient_weighted_lower
#print axioms actual_totient_nat_profile_lower
end JSP233.HarmonicAbel29
