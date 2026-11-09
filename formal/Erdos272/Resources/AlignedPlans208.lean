module

public import Erdos272.Resources.Aligned208
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! Kernel-checked step-dependent plans for the three preparations and all
ten terminal integer density ranks.  The tables are finite arithmetic;
their use below is through the actual-family gate theorem. -/
namespace JSP233.AlignedPlans208
open StarCompletion APGeometry Aligned208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def Slope (D : Finset ℕ) (p : ℕ → ℕ) : ℝ :=
  ∑ d ∈ D, (((p d - 1) / d : ℕ) : ℝ) / d

def Constant (D : Finset ℕ) (p : ℕ → ℕ) : ℝ :=
  ∑ d ∈ D, (((p d - 1) / d : ℕ) : ℝ) * (2 - 3 / (d : ℝ))

theorem sum_cost_linear (D : Finset ℕ) (p : ℕ → ℕ) (w : ℝ) :
    (∑ d ∈ D, (((p d - 1) / d : ℕ) : ℝ) * (w / d + 2 - 3 / d)) =
      Slope D p * w + Constant D p := by
  dsimp only [Slope, Constant]
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

def PreparationPlan (r d : ℕ) : ℕ :=
  match r, d with
  | 1, 1 => 251
  | 1, 2 => 20
  | 1, 3 => 15
  | 1, 4 => 14
  | 1, 5 => 13
  | 1, _ => 12
  | 2, 1 => 24
  | 2, 2 => 15
  | 2, 3 => 13
  | 2, 4 => 13
  | 2, _ => 12
  | _, 1 => 18
  | _, 2 => 14
  | _, 3 => 13
  | _, _ => 12

def PreparationWidth (r : ℕ) : ℝ :=
  match r with
  | 1 => 573 / 50
  | 2 => 401 / 20
  | _ => 117 / 4

def PreparationA (r : ℕ) : ℝ :=
  match r with
  | 1 => 129845 / 504
  | 2 => 14933 / 504
  | _ => 11531 / 504

def PreparationB (r : ℕ) : ℝ :=
  match r with
  | 1 => -(38117 / 168)
  | 2 => -(149 / 168)
  | _ => 565 / 168

def TerminalPlan (k d : ℕ) : ℕ :=
  match k, d with
  | 2, _ => 3
  | 3, _ => 4
  | 4, _ => 5
  | 5, _ => 6
  | 6, 1 => 8
  | 6, _ => 7
  | 7, 1 => 9
  | 7, _ => 8
  | 8, 1 => 11
  | 8, _ => 9
  | 9, 1 => 13
  | 9, 2 => 11
  | 9, _ => 10
  | 10, 1 => 15
  | 10, 2 => 12
  | 10, _ => 11
  | _, 1 => 17
  | _, 2 => 14
  | _, 3 => 13
  | _, _ => 12

def TerminalA (k : ℕ) : ℝ :=
  match k with
  | 2 => 2
  | 3 => 7 / 2
  | 4 => 16 / 3
  | 5 => 79 / 12
  | 6 => 577 / 60
  | 7 => 647 / 60
  | 8 => 1436 / 105
  | 9 => 13973 / 840
  | 10 => 47743 / 2520
  | _ => 11027 / 504

def TerminalB (k : ℕ) : ℝ :=
  match k with
  | 2 => -2
  | 3 => -(5 / 2)
  | 4 => -2
  | 5 => -(7 / 4)
  | 6 => -(17 / 20)
  | 7 => -(7 / 20)
  | 8 => 34 / 35
  | 9 => 587 / 280
  | 10 => 2657 / 840
  | _ => 733 / 168

def GateCoefficient (k u : ℝ) (d p : ℕ) : ℝ :=
  1 / k - 1 / (p : ℝ) - (1 / (d : ℝ) - 1 / (p : ℝ)) / u

def GateConstant (d p : ℕ) : ℝ := 3 - 3 / (d : ℝ) + 1 / (p : ℝ)

theorem preparation_coefficients {r : ℕ} (hr1 : 1 ≤ r) (hr3 : r ≤ 3) :
    Slope (Finset.Icc 1 10) (PreparationPlan r) = PreparationA r ∧
      Constant (Finset.Icc 1 10) (PreparationPlan r) = PreparationB r := by
  interval_cases r <;>
    norm_num [Slope, Constant, PreparationPlan, PreparationA, PreparationB,
      Finset.sum_Icc_succ_top]

theorem terminal_coefficients {k : ℕ} (hk2 : 2 ≤ k) (hk11 : k ≤ 11) :
    Slope (Finset.Icc 1 (k - 1)) (TerminalPlan k) = TerminalA k ∧
      Constant (Finset.Icc 1 (k - 1)) (TerminalPlan k) = TerminalB k := by
  interval_cases k <;>
    norm_num [Slope, Constant, TerminalPlan, TerminalA, TerminalB,
      Finset.sum_Icc_succ_top]

theorem preparation_endpoint {r d : ℕ}
    (hr1 : 1 ≤ r) (hr3 : r ≤ 3) (hd1 : 1 ≤ d) (hd10 : d ≤ 10) :
    d < PreparationPlan r d ∧
      0 < GateCoefficient 11 (PreparationWidth r) d (PreparationPlan r d) ∧
      GateConstant d (PreparationPlan r d) <
        659912 * GateCoefficient 11 (PreparationWidth r) d (PreparationPlan r d) := by
  interval_cases r <;> interval_cases d <;>
    norm_num [PreparationPlan, PreparationWidth, GateCoefficient, GateConstant]

theorem terminal_endpoint {k d : ℕ}
    (hk2 : 2 ≤ k) (hk11 : k ≤ 11) (hd1 : 1 ≤ d) (hdk : d < k) :
    d < TerminalPlan k d ∧
      0 < GateCoefficient k (148 / 5) d (TerminalPlan k d) ∧
      GateConstant d (TerminalPlan k d) <
        659912 * GateCoefficient k (148 / 5) d (TerminalPlan k d) := by
  have hd10 : d ≤ 10 := by omega
  interval_cases k <;> interval_cases d <;>
    norm_num [TerminalPlan, GateCoefficient, GateConstant] at *

theorem gate_above_endpoint {n c b : ℝ}
    (hn : 659912 ≤ n) (hc : 0 ≤ c) (hb : b < 659912 * c) : b < n * c :=
  hb.trans_le (mul_le_mul_of_nonneg_right hn hc)

/-- Each preparation applies its own full physical step plan to the actual
aligned subfamily supplied by the original-family restoration. -/
theorem actual_preparation_count {N L R r : ℕ} {E : Finset (Finset ℤ)}
    (d : Finset ℤ → ℕ) (a : Finset ℤ → ℤ)
    (hN : 659912 ≤ N) (hr1 : 1 ≤ r) (hr3 : r ≤ 3)
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
  have hNreal : (659912 : ℝ) ≤ N := by exact_mod_cast hN
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
    (hN : 659912 ≤ N) (hk2 : 2 ≤ k) (hk11 : k ≤ 11)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) E) (hbad : ∀ S ∈ E, ¬ IsAP S)
    (htrace : ∀ S ∈ E, APAt (d S : ℤ) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (halign : ∀ S ∈ E, ∀ y ∈ S, (d S : ℤ) ∣ y - a S)
    (hdense : ∀ S ∈ E, (N : ℝ) < (k : ℝ) * S.card)
    (hwidth : (L : ℝ) + (N : ℝ) - R < (N : ℝ) / (148 / 5)) :
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
  have hNreal : (659912 : ℝ) ≤ N := by exact_mod_cast hN
  have hgate : ∀ e ∈ Finset.Icc 1 (k - 1),
      GateConstant e (TerminalPlan k e) <
        (N : ℝ) * GateCoefficient k (148 / 5) e (TerminalPlan k e) := by
    intro e he
    have hh := terminal_endpoint hk2 hk11 (Finset.mem_Icc.mp he).1
      (by have hh := (Finset.mem_Icc.mp he).2; omega)
    exact gate_above_endpoint hNreal hh.2.1.le hh.2.2
  have hc := actual_count_from_gates (Finset.Icc 1 (k - 1)) (TerminalPlan k) d a
    hL hLR hRN hkR hlegal hbad hD hp hsteps htrace halign hdense hwidth hgate
  rw [sum_cost_linear, (terminal_coefficients hk2 hk11).1,
    (terminal_coefficients hk2 hk11).2] at hc
  exact hc

#print axioms preparation_coefficients
#print axioms terminal_coefficients
#print axioms preparation_endpoint
#print axioms terminal_endpoint
#print axioms actual_preparation_count
#print axioms actual_terminal_count
end
end JSP233.AlignedPlans208
