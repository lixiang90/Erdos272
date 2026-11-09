module

public import Erdos272.Resources.NoHigh208
public import Erdos272.Arithmetic.TwoSidedMoment62

@[expose] public section

/-! # The one-sided local AP-trace loss

The finite low witness pool from `NoHigh208` is paid with its actual two
distance prefixes. The source sets and their legality remain on `Ground N`.
-/
namespace JSP233.NoHighAPBound208
open StarCompletion RestrictedWitness44 NoHigh208 HarmonicAbel29
open TwoSidedMoment62 SimplexMoment57
open scoped Classical BigOperators
noncomputable section

theorem low_pool_bound {L : ℕ} {c : ℤ} (hc : c ∈ Ground (L - 1)) :
    ((∑ z ∈ Finset.Icc 1 ((L : ℤ) - 1), (Distance c z).divisors.card : ℕ) : ℝ) ≤
      (L : ℝ) * Harmonic L := by
  have hcG := (mem_ground (L - 1) c).mp hc
  have hL : 1 ≤ L := by omega
  have hcast : ((L - 1 : ℕ) : ℤ) = (L : ℤ) - 1 := by omega
  have hLow : Finset.Icc 1 ((L : ℤ) - 1) = Ground (L - 1) := by
    ext z
    simp only [Finset.mem_Icc, mem_ground, hcast]
  have hsplit := actual_distance_sum_split hc
    (fun d => (d.divisors.card : ℝ)) (by simp)
  let a := c.toNat - 1
  let b := L - 1 - c.toNat
  have haL : a ≤ L := by dsimp [a]; omega
  have hbL : b ≤ L := by dsimp [b]; omega
  have habL : a + b ≤ L := by dsimp [a, b]; omega
  have ha := (actual_divisor_first_moment a).trans
    (mul_le_mul_of_nonneg_left (harmonic_mono haL) (Nat.cast_nonneg a))
  have hb := (actual_divisor_first_moment b).trans
    (mul_le_mul_of_nonneg_left (harmonic_mono hbL) (Nat.cast_nonneg b))
  push_cast
  rw [hLow, hsplit]
  calc
    (∑ d ∈ Finset.Icc 1 (c.toNat - 1), (d.divisors.card : ℝ)) +
        (∑ d ∈ Finset.Icc 1 (L - 1 - c.toNat), (d.divisors.card : ℝ)) ≤
      (a : ℝ) * Harmonic L + (b : ℝ) * Harmonic L := add_le_add ha hb
    _ = ((a + b : ℕ) : ℝ) * Harmonic L := by push_cast; ring
    _ ≤ (L : ℝ) * Harmonic L := mul_le_mul_of_nonneg_right
      (by exact_mod_cast habL) (harmonic_nonneg L)

theorem actual_failure_local_real {N L : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hc : c ∈ Ground (L - 1)) :
    ((Failure F c L).card : ℝ) ≤
      (TerminalCodes ((L : ℤ) - c).toNat).card + (L : ℝ) * Harmonic L := by
  have hcG := (mem_ground (L - 1) c).mp hc
  have hcL : c < (L : ℤ) := by omega
  have hnat := actual_failure_local_count hF hroot hP hcP hLP hcL
  have hreal : ((Failure F c L).card : ℝ) ≤
      (TerminalCodes ((L : ℤ) - c).toNat).card +
        ((∑ z ∈ Finset.Icc 1 ((L : ℤ) - 1), (Distance c z).divisors.card : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith only [hreal, low_pool_bound hc]

#print axioms low_pool_bound
#print axioms actual_failure_local_real
end
end JSP233.NoHighAPBound208
