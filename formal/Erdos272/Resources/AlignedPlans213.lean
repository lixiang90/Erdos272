module

public import Erdos272.Resources.AlignedPlans212
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.AlignedPlans213
open StarCompletion APGeometry Aligned208 AlignedPlans212
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem preparation_endpoint {r d : ℕ}
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hd1 : 1 ≤ d) (hd10 : d ≤ 10) :
    d < PreparationPlan r d ∧
      0 < GateCoefficient 11 (PreparationWidth r) d (PreparationPlan r d) ∧
      GateConstant d (PreparationPlan r d) <
        640000 * GateCoefficient 11 (PreparationWidth r) d (PreparationPlan r d) := by
  interval_cases r <;> interval_cases d <;>
    norm_num [PreparationPlan, PreparationWidth, GateCoefficient, GateConstant]

theorem terminal_endpoint {k d : ℕ}
    (hk2 : 2 ≤ k) (hk11 : k ≤ 11) (hd1 : 1 ≤ d) (hdk : d < k) :
    d < TerminalPlan k d ∧
      0 < GateCoefficient k (2951 / 100) d (TerminalPlan k d) ∧
      GateConstant d (TerminalPlan k d) <
        640000 * GateCoefficient k (2951 / 100) d (TerminalPlan k d) := by
  have hd10 : d ≤ 10 := by omega
  interval_cases k <;> interval_cases d <;>
    norm_num [TerminalPlan, GateCoefficient, GateConstant] at *

theorem gate_above_endpoint {n c b : ℝ}
    (hn : 640000 ≤ n) (hc : 0 ≤ c) (hb : b < 640000 * c) : b < n * c :=
  hb.trans_le (mul_le_mul_of_nonneg_right hn hc)

/-- Each preparation applies its own full physical step plan to the actual
aligned subfamily supplied by the original-family restoration. -/
theorem actual_preparation_count {N L R r : ℕ} {E : Finset (Finset ℤ)}
    (d : Finset ℤ → ℕ) (a : Finset ℤ → ℤ)
    (hN : 640000 ≤ N) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (htrace : ∀ S ∈ E, APAt (d S : ℤ) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀ S ∈ E, ∀ y ∈ S, (d S : ℤ) ∣ y - a S)
    (hdense : ∀ S ∈ E, (N : ℝ) < 11 * S.card)
    (hwidth : (L : ℝ) + (N : ℝ) - R < (N : ℝ) / PreparationWidth r) :
    (E.card : ℝ) ≤ PreparationA r * ((L : ℝ) + (N : ℝ) - R) + PreparationB r := by
  have hsteps : ∀ S ∈ E, d S ∈ Finset.Icc 1 10 := by
    intro S hS
    have hd : 0 < d S := by exact_mod_cast (htrace S hS).1
    have hlt := actual_aligned_modulus_lt hd (hlegal.1 S hS) (hbad S hS)
      (hdense S hS) (halign S hS)
    have hltN : d S < 11 := by exact_mod_cast hlt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hD : ∀ e ∈ Finset.Icc 1 10, 0 < e := by
    intro e he
    have hh := Finset.mem_Icc.mp he
    omega
  have hp : ∀ e ∈ Finset.Icc 1 10, e < PreparationPlan r e := by
    intro e he
    exact (preparation_endpoint hr1 hr3 (Finset.mem_Icc.mp he).1
      (Finset.mem_Icc.mp he).2).1
  have hNreal : (640000 : ℝ) ≤ N := by exact_mod_cast hN
  have hgate : ∀ e ∈ Finset.Icc 1 10,
      GateConstant e (PreparationPlan r e) <
        (N : ℝ) * GateCoefficient 11 (PreparationWidth r) e (PreparationPlan r e) := by
    intro e he
    have hh := preparation_endpoint hr1 hr3 (Finset.mem_Icc.mp he).1
      (Finset.mem_Icc.mp he).2
    exact gate_above_endpoint hNreal hh.2.1.le hh.2.2
  have hc := actual_count_from_gates (Finset.Icc 1 10) (PreparationPlan r) d a
    hL hLR hRN (by norm_num : (0 : ℝ) < 11) hlegal hbad hD hp hsteps htrace halign
    hdense hwidth hgate
  rw [sum_cost_linear, (preparation_coefficients hr1 hr3).1,
    (preparation_coefficients hr1 hr3).2] at hc
  exact hc

/-- The terminal table covers every actual integer density rank two to eleven. -/
theorem actual_terminal_count {N L R k : ℕ} {E : Finset (Finset ℤ)}
    (d : Finset ℤ → ℕ) (a : Finset ℤ → ℤ)
    (hN : 640000 ≤ N) (hk2 : 2 ≤ k) (hk11 : k ≤ 11)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (htrace : ∀ S ∈ E, APAt (d S : ℤ) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀ S ∈ E, ∀ y ∈ S, (d S : ℤ) ∣ y - a S)
    (hdense : ∀ S ∈ E, (N : ℝ) < (k : ℝ) * S.card)
    (hwidth : (L : ℝ) + (N : ℝ) - R < (N : ℝ) / (2951 / 100)) :
    (E.card : ℝ) ≤ TerminalA k * ((L : ℝ) + (N : ℝ) - R) + TerminalB k := by
  have hsteps : ∀ S ∈ E, d S ∈ Finset.Icc 1 (k - 1) := by
    intro S hS
    have hd : 0 < d S := by exact_mod_cast (htrace S hS).1
    have hlt := actual_aligned_modulus_lt hd (hlegal.1 S hS) (hbad S hS)
      (hdense S hS) (halign S hS)
    have hltN : d S < k := by exact_mod_cast hlt
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hD : ∀ e ∈ Finset.Icc 1 (k - 1), 0 < e := by
    intro e he
    have hh := Finset.mem_Icc.mp he
    omega
  have hp : ∀ e ∈ Finset.Icc 1 (k - 1), e < TerminalPlan k e := by
    intro e he
    exact (terminal_endpoint hk2 hk11 (Finset.mem_Icc.mp he).1
      (by have hh := (Finset.mem_Icc.mp he).2; omega)).1
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hNreal : (640000 : ℝ) ≤ N := by exact_mod_cast hN
  have hgate : ∀ e ∈ Finset.Icc 1 (k - 1),
      GateConstant e (TerminalPlan k e) <
        (N : ℝ) * GateCoefficient k (2951 / 100) e (TerminalPlan k e) := by
    intro e he
    have hh := terminal_endpoint hk2 hk11 (Finset.mem_Icc.mp he).1
      (by have hh := (Finset.mem_Icc.mp he).2; omega)
    exact gate_above_endpoint hNreal hh.2.1.le hh.2.2
  have hc := actual_count_from_gates (Finset.Icc 1 (k - 1)) (TerminalPlan k) d a
    hL hLR hRN hkR hlegal hbad hD hp hsteps htrace halign hdense hwidth hgate
  rw [sum_cost_linear, (terminal_coefficients hk2 hk11).1,
    (terminal_coefficients hk2 hk11).2] at hc
  exact hc


#print axioms preparation_endpoint
#print axioms terminal_endpoint
#print axioms gate_above_endpoint
#print axioms actual_preparation_count
#print axioms actual_terminal_count
end
end JSP233.AlignedPlans213
