import Erdos272.Arithmetic.TerminalCounting208
import Mathlib.Tactic

/-! Elementary uniform bounds for the small-step part of terminal codes. -/
namespace JSP233.TerminalDivisors208
open NoHigh208 TerminalCounting208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem divisor_count_le_twice {n B : ℕ} (hn : n < (B + 1)^2) :
    n.divisors.card ≤ 2 * B := by
  have hs : (n.divisors.filter (fun d => d ≤ B)).card ≤ B := by
    have hsub : n.divisors.filter (fun d => d ≤ B) ⊆ Finset.Icc 1 B := by
      intro d hd
      obtain ⟨hd, hB⟩ := Finset.mem_filter.mp hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, hB⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hsub
  have hl : (n.divisors.filter (fun d => ¬ d ≤ B)).card ≤ B := by
    have hm : Set.MapsTo (fun d => n / d)
        (n.divisors.filter (fun d => ¬ d ≤ B)) (Finset.Icc 1 B) := by
      intro d hd
      obtain ⟨hd, hB⟩ := Finset.mem_filter.mp hd
      have hdpos := Nat.pos_of_mem_divisors hd
      have hprod : d * (n / d) = n := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
      have hnpos : 0 < n := Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_divisors hd)
      have hqpos : 0 < n / d := by
        exact Nat.div_pos (Nat.le_of_dvd hnpos (Nat.dvd_of_mem_divisors hd)) hdpos
      have hqB : n / d ≤ B := by
        by_contra h
        have hm := Nat.mul_le_mul (by omega : B + 1 ≤ d) (by omega : B + 1 ≤ n / d)
        nlinarith only [hm, hprod, hn]
      exact Finset.mem_Icc.mpr ⟨hqpos, hqB⟩
    have hi : Set.InjOn (fun d => n / d) (n.divisors.filter (fun d => ¬ d ≤ B)) := by
      intro d hd e he heq
      have hdn := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
      have hen := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp he).1
      have hdprod := Nat.mul_div_cancel' hdn
      have heprod := Nat.mul_div_cancel' hen
      have hqpos : 0 < n / e := (Finset.mem_Icc.mp (hm he)).1
      dsimp only at heq
      rw [heq] at hdprod
      exact Nat.eq_of_mul_eq_mul_right hqpos (hdprod.trans heprod.symm)
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
      Finset.card_le_card_of_injOn (fun d => n / d) hm hi
  have hp := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun d => d ≤ B)
  omega

theorem small_sum_bound {A T : ℕ} (hA : 1 ≤ A) (hAsq : A < (T + 1)^2) :
    ∑ d ∈ Finset.Icc 1 T, (Anchor A d).divisors.card ≤ 2 * T * (T + 1) := by
  have hh : ∀ d ∈ Finset.Icc 1 T, (Anchor A d).divisors.card ≤ 2 * (T + 1) := by
    intro d hd
    obtain ⟨hdpos, hdT⟩ := Finset.mem_Icc.mp hd
    have hw := anchor_window hA hdpos
    apply divisor_count_le_twice
    nlinarith
  have hsum := Finset.sum_le_sum hh
  simpa only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, smul_eq_mul,
    mul_assoc, mul_left_comm, mul_comm] using hsum

theorem small_step_bound {A T : ℕ} (hA : 1 ≤ A) (hAsq : A < (T + 1)^2) :
    ((TerminalCodes A).filter (fun u => u.2.1 ≤ T)).card ≤ 2 * T * (T + 1) :=
  (small_step_count hA).trans (small_sum_bound hA hAsq)

#print axioms divisor_count_le_twice
#print axioms small_step_bound
end
end JSP233.TerminalDivisors208
