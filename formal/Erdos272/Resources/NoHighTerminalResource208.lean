import Erdos272.Resources.NoHighAPBound208
import Erdos272.Arithmetic.TerminalLattice208
import Erdos272.Arithmetic.TerminalGcd208

/-! The actual NoHigh loss is local in the cutoff, with the original ground
and the original legal family retained throughout the proof. -/
namespace JSP233.NoHighTerminalResource208
open StarCompletion RestrictedWitness44 NoHigh208 NoHighAPBound208
open TerminalLattice208 HarmonicAbel29
open scoped Classical BigOperators
noncomputable section

theorem actual_failure_of_terminal_bound {N L : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c : ℤ} {B : ℝ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hc : c ∈ Ground (L - 1)) (hB : 0 ≤ B)
    (hterminal : ((TerminalCodes ((L : ℤ) - c).toNat).card : ℝ) ≤
      B * ((L : ℤ) - c).toNat) :
    ((Failure F c L).card : ℝ) ≤ (L : ℝ) * (Harmonic L + B) := by
  have hlocal := actual_failure_local_real hF hroot hP hcP hLP hc
  have hcG := (mem_ground (L - 1) c).mp hc
  have hAL : ((L : ℤ) - c).toNat ≤ L := by omega
  have hmul : B * (((L : ℤ) - c).toNat : ℝ) ≤ B * L :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hAL) hB
  nlinarith only [hlocal, hterminal, hmul]

theorem actual_terminal_five (A : ℕ) :
    ((TerminalCodes A).card : ℝ) ≤ 5 * A := by
  apply terminal_count_five _ A
  intro H hH
  exact TerminalGcd208.coefficient_bound hH

theorem actual_failure_five_local
    {N L : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hc : c ∈ Ground (L - 1)) :
    ((Failure F c L).card : ℝ) ≤ (L : ℝ) * (Harmonic L + 5) := by
  exact actual_failure_of_terminal_bound hF hroot hP hcP hLP hc (by norm_num)
    (actual_terminal_five _)

theorem actual_failure_log_local
    {N L : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ} {c : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀ S ∈ F, ¬IsAP S → c ∈ S)
    (hP : P ∈ F) (hcP : c ∉ P) (hLP : ∀ z ∈ P, (L : ℤ) ≤ z)
    (hc : c ∈ Ground (L - 1)) :
    ((Failure F c L).card : ℝ) ≤ (L : ℝ) * (Real.log L + 6) := by
  apply (actual_failure_five_local hF hroot hP hcP hLP hc).trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg L)
  linarith only [HarmonicAbel29.harmonic_le_one_add_log L]

#print axioms actual_failure_of_terminal_bound
#print axioms actual_terminal_five
#print axioms actual_failure_five_local
#print axioms actual_failure_log_local
end
end JSP233.NoHighTerminalResource208
