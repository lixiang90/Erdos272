import Erdos272.Arithmetic.TerminalCounting208
import Erdos272.Arithmetic.TerminalDivisors208
import Mathlib.Tactic

/-! Spacing bounds for the actual gcd lattice fibres of terminal codes. -/
namespace JSP233.TerminalLattice208
open NoHigh208 TerminalCounting208 TerminalDivisors208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem multiples_span {S : Finset ℕ} (hS : S.Nonempty) {k : ℕ} (hk : 0 < k)
    (hdiv : ∀ d ∈ S, k ∣ d) :
    (S.card : ℝ) * k ≤ (S.max' hS : ℝ) - (S.min' hS : ℝ) + k := by
  let a := S.min' hS
  let b := S.max' hS
  have ha : a ∈ S := Finset.min'_mem S hS
  have hb : b ∈ S := Finset.max'_mem S hS
  have hab : a ≤ b := Finset.min'_le _ _ hb
  have hm : Set.MapsTo (fun d => d / k) S (Finset.Icc (a / k) (b / k)) := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.div_le_div_right (Finset.min'_le _ _ hd),
      Nat.div_le_div_right (Finset.le_max' _ _ hd)⟩
  have hi : Set.InjOn (fun d => d / k) S := by
    intro d hd e he heq
    have hdprod := Nat.mul_div_cancel' (hdiv d hd)
    have heprod := Nat.mul_div_cancel' (hdiv e he)
    dsimp only at heq
    rw [heq] at hdprod
    exact hdprod.symm.trans heprod
  have hc := Finset.card_le_card_of_injOn (fun d => d / k) hm hi
  rw [Nat.card_Icc] at hc
  have hquot : a / k ≤ b / k := Nat.div_le_div_right hab
  have hcadd : S.card + a / k ≤ b / k + 1 := by omega
  have hcmul := Nat.mul_le_mul_left k hcadd
  have haprod := Nat.mul_div_cancel' (hdiv a ha)
  have hbprod := Nat.mul_div_cancel' (hdiv b hb)
  have hnat : S.card * k + a ≤ b + k := by nlinarith only [hcmul, haprod, hbprod]
  have hreal : (S.card : ℝ) * k + a ≤ (b : ℝ) + k := by exact_mod_cast hnat
  change (S.card : ℝ) * k ≤ (b : ℝ) - a + k
  linarith

theorem fibre_count_bound {A q r : ℕ} (hq : 3 ≤ q) (hr : 2 ≤ r) :
    (((Finset.Icc 1 A).filter fun d =>
      A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d).card : ℝ) ≤
      (A : ℝ) * q.gcd r / ((q : ℝ) * (q - 1) * r) + 1 := by
  let S := (Finset.Icc 1 A).filter fun d =>
    A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d
  let g := q.gcd r
  let k := r / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_right q (by omega)
  have hgdiv : g ∣ r := Nat.gcd_dvd_right q r
  have hk : 0 < k := Nat.div_pos (Nat.le_of_dvd (by omega) hgdiv) hg
  have hkg : k * g = r := Nat.div_mul_cancel hgdiv
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1R : (0 : ℝ) < (q : ℝ) - 1 := by
    have hh : (3 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  by_cases hS : S.Nonempty
  · let a := S.min' hS
    let b := S.max' hS
    have ha := Finset.mem_filter.mp (Finset.min'_mem S hS)
    have hb := Finset.mem_filter.mp (Finset.max'_mem S hS)
    have has : A ≤ q * a := ha.2.1
    have hbs : q * b < A + b := hb.2.2.1
    have hasR : (A : ℝ) ≤ q * (a : ℝ) := by exact_mod_cast has
    have hbsR : (q : ℝ) * b < (A : ℝ) + b := by exact_mod_cast hbs
    have ham : (A : ℝ) / q ≤ a := (div_le_iff₀ hqR).mpr (by nlinarith only [hasR])
    have hbm : (b : ℝ) ≤ (A : ℝ) / ((q : ℝ) - 1) :=
      (le_div_iff₀ hq1R).mpr (by nlinarith only [hbsR])
    have hwidth : (b : ℝ) - a ≤ (A : ℝ) / ((q : ℝ) * (q - 1)) := by
      calc
        (b : ℝ) - a ≤ (A : ℝ) / ((q : ℝ) - 1) - (A : ℝ) / q :=
          sub_le_sub hbm ham
        _ = (A : ℝ) / ((q : ℝ) * (q - 1)) := by field_simp; ring
    have hspan := multiples_span hS hk (fun d hd => (Finset.mem_filter.mp hd).2.2.2)
    have hcount : (S.card : ℝ) ≤ (A : ℝ) / ((q : ℝ) * (q - 1) * k) + 1 := by
      apply (mul_le_mul_iff_of_pos_right hkR).mp
      have heq : ((A : ℝ) / ((q : ℝ) * (q - 1) * k) + 1) * k =
          (A : ℝ) / ((q : ℝ) * (q - 1)) + k := by
        field_simp
      rw [heq]
      linarith only [hspan, hwidth]
    change (S.card : ℝ) ≤ _
    convert hcount using 1
    have hkgR : (k : ℝ) * g = r := by exact_mod_cast hkg
    field_simp
    nlinarith only [hkgR]
  · have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

theorem quotient_index_count (T : ℕ) :
    (∑ q ∈ Finset.Icc 3 (T + 1), ∑ _r ∈ Finset.Icc 2 (q - 1), (1 : ℝ)) =
      (T : ℝ) * ((T : ℝ) - 1) / 2 := by
  induction T with
  | zero => norm_num
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      norm_num
    · rw [Finset.sum_Icc_succ_top (by omega : 3 ≤ T + 1 + 1)]
      rw [ih]
      have hcard : (Finset.Icc 2 (T + 1 + 1 - 1)).card = T := by
        rw [Nat.card_Icc]
        omega
      simp only [Finset.sum_const, smul_eq_mul, mul_one, hcard, Nat.cast_add, Nat.cast_one]
      ring

theorem large_step_real_bound {A T : ℕ} (hAsq : A < (T + 1)^2) :
    (((TerminalCodes A).filter (fun u => T < u.2.1)).card : ℝ) ≤
      (A : ℝ) * (∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        (q.gcd r : ℝ) / ((q : ℝ) * (q - 1) * r)) +
      (T : ℝ) * ((T : ℝ) - 1) / 2 := by
  have hc := large_step_count hAsq
  have hcR : (((TerminalCodes A).filter (fun u => T < u.2.1)).card : ℝ) ≤
      ∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        (((Finset.Icc 1 A).filter fun d =>
          A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d).card : ℝ) := by
    exact_mod_cast hc
  calc
    _ ≤ ∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        ((A : ℝ) * ((q.gcd r : ℝ) / ((q : ℝ) * (q - 1) * r)) + 1) := by
      apply hcR.trans
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      simpa only [mul_div_assoc] using
        fibre_count_bound (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hr).1
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [quotient_index_count]

theorem terminal_count_real {A T : ℕ} (hA : 1 ≤ A) (hAsq : A < (T + 1)^2) :
    ((TerminalCodes A).card : ℝ) ≤
      2 * (T : ℝ) * (T + 1) +
      (A : ℝ) * (∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        (q.gcd r : ℝ) / ((q : ℝ) * (q - 1) * r)) +
      (T : ℝ) * ((T : ℝ) - 1) / 2 := by
  have hs := small_step_bound (T := T) hA hAsq
  have hsR : (((TerminalCodes A).filter (fun u => u.2.1 ≤ T)).card : ℝ) ≤
      2 * (T : ℝ) * (T + 1) := by exact_mod_cast hs
  have hl := large_step_real_bound hAsq
  have hp := Finset.card_filter_add_card_filter_not (s := TerminalCodes A)
    (fun u => u.2.1 ≤ T)
  simp only [Nat.not_le] at hp
  have hpR : (((TerminalCodes A).filter (fun u => u.2.1 ≤ T)).card : ℝ) +
      (((TerminalCodes A).filter (fun u => T < u.2.1)).card : ℝ) =
      (TerminalCodes A).card := by exact_mod_cast hp
  linarith only [hsR, hl, hpR]

theorem terminal_count_five_of_coefficient {A T : ℕ} (hT : 4 ≤ T)
    (hsq : T^2 ≤ A) (hAsq : A < (T + 1)^2)
    (hcoeff : (∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
      (q.gcd r : ℝ) / ((q : ℝ) * (q - 1) * r)) ≤
      (16 : ℝ) / 9 + 1 / ((T : ℝ) + 1)) :
    ((TerminalCodes A).card : ℝ) ≤ 5 * A := by
  have hA : 1 ≤ A := by nlinarith
  have hc := terminal_count_real hA hAsq
  have hm := mul_le_mul_of_nonneg_left hcoeff (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
  have hTR : (4 : ℝ) ≤ T := by exact_mod_cast hT
  have hsqR : (T : ℝ)^2 ≤ A := by exact_mod_cast hsq
  have hAsqR : (A : ℝ) < ((T : ℝ) + 1)^2 := by exact_mod_cast hAsq
  have hden : (0 : ℝ) < (T : ℝ) + 1 := by positivity
  have hfrac : (A : ℝ) / ((T : ℝ) + 1) ≤ (T : ℝ) + 1 :=
    (div_le_iff₀ hden).mpr (by nlinarith only [hAsqR])
  have heq : (A : ℝ) * (16 / 9 + 1 / ((T : ℝ) + 1)) =
      (16 / 9 : ℝ) * A + (A : ℝ) / ((T : ℝ) + 1) := by ring
  rw [heq] at hm
  nlinarith only [hc, hm, hsqR, hfrac, hTR, sq_nonneg ((T : ℝ) - 4)]

theorem terminal_count_small {A : ℕ} (hA : A < 16) :
    (TerminalCodes A).card ≤ 5 * A := by
  interval_cases A <;> decide

theorem terminal_count_five
    (hcoeff : ∀ H : ℕ, 1 ≤ H →
      (∑ q ∈ Finset.Icc 3 H, ∑ r ∈ Finset.Icc 2 (q - 1),
        (q.gcd r : ℝ) / ((q : ℝ) * (q - 1) * r)) ≤
        (16 : ℝ) / 9 + 1 / (H : ℝ)) (A : ℕ) :
    ((TerminalCodes A).card : ℝ) ≤ 5 * A := by
  by_cases hA : A < 16
  · exact_mod_cast terminal_count_small hA
  · have hT : 4 ≤ A.sqrt := Nat.le_sqrt'.mpr (by omega)
    apply terminal_count_five_of_coefficient hT (Nat.sqrt_le' A) (Nat.lt_succ_sqrt' A)
    simpa only [Nat.cast_add, Nat.cast_one] using hcoeff (A.sqrt + 1) (by omega)

#print axioms multiples_span
#print axioms fibre_count_bound
#print axioms large_step_real_bound
#print axioms terminal_count_real
#print axioms terminal_count_five_of_coefficient
#print axioms terminal_count_small
#print axioms terminal_count_five
end
end JSP233.TerminalLattice208
