import Erdos272.Resources.NoHigh208
import Mathlib.Tactic

/-! # Arithmetic coordinates of the local terminal code pool

The fixed-step anchor and the quotient/gcd changes of variables are exact.
These bounds are on the actual finite code pool obtained in `NoHigh208`.
No numerical linear estimate is assumed.
-/
namespace JSP233.TerminalCounting208
open NoHigh208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Anchor (A d : ℕ) : ℕ := d * ((A - 1) / d + 1)

theorem anchor_window {A d : ℕ} (hA : 1 ≤ A) (hd : 0 < d) :
    A ≤ Anchor A d ∧ Anchor A d < A + d := by
  have hlo := Nat.mul_div_le (A - 1) d
  have hhi := Nat.lt_mul_div_succ (A - 1) hd
  have hAeq : A - 1 + 1 = A := Nat.sub_add_cancel hA
  unfold Anchor
  constructor <;> nlinarith

theorem anchor_eq {A d n : ℕ} (hA : 1 ≤ A) (hd : 0 < d)
    (hdn : d ∣ n) (hAn : A ≤ n) (hn : n < A + d) : Anchor A d = n := by
  have hw := anchor_window hA hd
  apply terminal_anchor_unique hd (dvd_mul_right d _) hdn hw.1 hAn hw.2 hn

theorem mem_terminal {A : ℕ} {u : Σ _ : ℕ, ℕ × ℕ} :
    u ∈ TerminalCodes A ↔ 1 ≤ u.1 ∧ u.1 ≤ 2 * A ∧
      u.2.1 ∈ u.1.divisors ∧ u.2.2 ∈ u.1.divisors ∧
      0 < u.2.1 ∧ u.2.1 < u.2.2 ∧ ¬u.2.1 ∣ u.2.2 ∧
      A ≤ u.1 ∧ u.1 < A + u.2.1 ∧ 3 * u.2.1 ≤ u.1 ∧ 2 * u.1 < 3 * A := by
  simp only [TerminalCodes, Finset.mem_sigma, Finset.mem_filter,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, and_assoc]

def StepCode (u : Σ _ : ℕ, ℕ × ℕ) : Σ _ : ℕ, ℕ := ⟨u.2.1, u.2.2⟩

theorem stepCode_injective_on (A : ℕ) : Set.InjOn StepCode (TerminalCodes A) := by
  intro u hu v hv heq
  obtain ⟨_, _, hud, hue, hd, _, _, hAu, hwu, _, _⟩ := mem_terminal.mp hu
  obtain ⟨_, _, hvd, hve, _, _, _, hAv, hwv, _, _⟩ := mem_terminal.mp hv
  have hdEq : u.2.1 = v.2.1 := congrArg Sigma.fst heq
  have heEq : u.2.2 = v.2.2 := congrArg (fun q : Σ _ : ℕ, ℕ => q.2) heq
  have hnd := Nat.dvd_of_mem_divisors hud
  have hmd : u.2.1 ∣ v.1 := by rw [hdEq]; exact Nat.dvd_of_mem_divisors hvd
  have hwv' : v.1 < A + u.2.1 := by simpa only [hdEq] using hwv
  have hnEq := terminal_anchor_unique hd hnd hmd hAu hAv hwu hwv'
  exact Sigma.ext hnEq (heq_of_eq (Prod.ext hdEq heEq))

def Fibres (A T : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 T).sigma fun d => (Anchor A d).divisors

theorem count_of_step_bound {A T : ℕ} (hA : 1 ≤ A)
    (C : Finset (Σ _ : ℕ, ℕ × ℕ)) (hC : C ⊆ TerminalCodes A)
    (hT : ∀ u ∈ C, u.2.1 ≤ T) :
    C.card ≤ ∑ d ∈ Finset.Icc 1 T, (Anchor A d).divisors.card := by
  have hm : Set.MapsTo StepCode C (Fibres A T) := by
    intro u hu
    obtain ⟨_, _, hud, hue, hd, _, _, hAu, hwu, _, _⟩ := mem_terminal.mp (hC hu)
    have han := anchor_eq hA hd (Nat.dvd_of_mem_divisors hud) hAu hwu
    have hdup : u.2.1 ≤ T := hT u hu
    have hed : u.2.2 ∈ (Anchor A u.2.1).divisors := by rw [han]; exact hue
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdup⟩, hed⟩
  have hh := Finset.card_le_card_of_injOn StepCode hm
    ((stepCode_injective_on A).mono hC)
  simpa only [Fibres, Finset.card_sigma] using hh

theorem small_step_count {A T : ℕ} (hA : 1 ≤ A) :
    ((TerminalCodes A).filter (fun u => u.2.1 ≤ T)).card ≤
      ∑ d ∈ Finset.Icc 1 T, (Anchor A d).divisors.card := by
  apply count_of_step_bound hA _ (Finset.filter_subset _ _)
  exact fun u hu => (Finset.mem_filter.mp hu).2

theorem full_step_count {A : ℕ} (hA : 1 ≤ A) :
    (TerminalCodes A).card ≤ ∑ d ∈ Finset.Icc 1 A, (Anchor A d).divisors.card := by
  apply count_of_step_bound hA _ (Finset.Subset.refl _)
  intro u hu
  obtain ⟨_, _, _, _, _, _, _, _, hw, h3, _⟩ := mem_terminal.mp hu
  have hh := terminal_step_small hw h3
  omega

theorem reduced_gcd_dvd_iff {q r d : ℕ} (hr : 0 < r) :
    r ∣ q * d ↔ r / q.gcd r ∣ d := by
  let g := q.gcd r
  have hg : 0 < g := Nat.gcd_pos_of_pos_right q hr
  have hq : g * (q / g) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hr' : g * (r / g) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have hcop : (r / g).Coprime (q / g) := (Nat.coprime_div_gcd_div_gcd hg).symm
  constructor
  · intro h
    have hh : g * (r / g) ∣ g * ((q / g) * d) := by
      rw [← Nat.mul_assoc, hq, hr']
      exact h
    exact hcop.dvd_of_dvd_mul_left ((Nat.mul_dvd_mul_iff_left hg).mp hh)
  · intro h
    have hh : r / g ∣ (q / g) * d := dvd_mul_of_dvd_right h _
    have hm := Nat.mul_dvd_mul_left g hh
    rw [← Nat.mul_assoc, hq, hr'] at hm
    exact hm

theorem large_quotient_data {A T : ℕ} {u : Σ _ : ℕ, ℕ × ℕ}
    (hu : u ∈ TerminalCodes A) (hT : T < u.2.1) (hAsq : A < (T + 1)^2) :
    let q := u.1 / u.2.1
    let r := u.1 / u.2.2
    3 ≤ q ∧ q ≤ T + 1 ∧ 2 ≤ r ∧ r < q ∧
      A ≤ q * u.2.1 ∧ q * u.2.1 < A + u.2.1 ∧
      r / q.gcd r ∣ u.2.1 := by
  obtain ⟨hn, _, hud, hue, hd, hde, hnot, hAn, hwin, h3, _⟩ := mem_terminal.mp hu
  let q := u.1 / u.2.1
  let r := u.1 / u.2.2
  have hqd : u.2.1 * q = u.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hud)
  have her : u.2.2 * r = u.1 := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hue)
  have hq3 : 3 ≤ q := by
    by_contra h
    have hh := Nat.mul_le_mul_left u.2.1 (show q ≤ 2 by omega)
    nlinarith only [hh, hqd, h3, hd]
  have hr2 : 2 ≤ r := by
    by_contra h
    have hrnonneg : 0 ≤ r := Nat.zero_le r
    have hcases : r = 0 ∨ r = 1 := by omega
    rcases hcases with hr0 | hr1
    · rw [hr0, Nat.mul_zero] at her
      omega
    · rw [hr1, Nat.mul_one] at her
      exact hnot (by rw [her]; exact Nat.dvd_of_mem_divisors hud)
  have hrq : r < q := by
    by_contra h
    have hh := Nat.mul_le_mul_left u.2.1 (show q ≤ r by omega)
    have hl := Nat.mul_lt_mul_of_pos_right hde (by omega : 0 < r)
    nlinarith only [hh, hl, hqd, her]
  have hqT : q ≤ T + 1 := by
    by_contra h
    have hh := Nat.mul_le_mul_left u.2.1 (show T + 2 ≤ q by omega)
    have hs := Nat.mul_le_mul_left (T + 1) (show T + 1 ≤ u.2.1 by omega)
    nlinarith only [hh, hs, hqd, hwin, hAsq]
  have hrn : r ∣ u.1 := by rw [← her]; exact dvd_mul_left r u.2.2
  have hnorm : r / q.gcd r ∣ u.2.1 := by
    apply (reduced_gcd_dvd_iff (by omega : 0 < r)).mp
    rw [Nat.mul_comm q, hqd]
    exact hrn
  refine ⟨hq3, hqT, hr2, hrq, ?_, ?_, hnorm⟩
  · rwa [Nat.mul_comm, hqd]
  · rwa [Nat.mul_comm, hqd]

def QuotientCode (u : Σ _ : ℕ, ℕ × ℕ) : Σ _ : ℕ, Σ _ : ℕ, ℕ :=
  ⟨u.1 / u.2.1, u.1 / u.2.2, u.2.1⟩

def LargeFibres (A T : ℕ) : Finset (Σ _ : ℕ, Σ _ : ℕ, ℕ) :=
  (Finset.Icc 3 (T + 1)).sigma fun q =>
    (Finset.Icc 2 (q - 1)).sigma fun r =>
      (Finset.Icc 1 A).filter fun d =>
        A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d

theorem large_step_count {A T : ℕ} (hAsq : A < (T + 1)^2) :
    ((TerminalCodes A).filter (fun u => T < u.2.1)).card ≤
      ∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        ((Finset.Icc 1 A).filter fun d =>
          A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d).card := by
  let C := (TerminalCodes A).filter fun u => T < u.2.1
  have hm : Set.MapsTo QuotientCode C (LargeFibres A T) := by
    intro u hu
    obtain ⟨hu, hTu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hq3, hqT, hr2, hrq, hAqd, hqdA, hdiv⟩ := large_quotient_data hu hTu hAsq
    obtain ⟨_, _, _, _, hd, _, _, _, hw, h3, _⟩ := mem_terminal.mp hu
    have hdA : u.2.1 ≤ A := by have hh := terminal_step_small hw h3; omega
    have hrup : u.1 / u.2.2 ≤ u.1 / u.2.1 - 1 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hq3, hqT⟩,
      Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hr2, hrup⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hd, hdA⟩, hAqd, hqdA, hdiv⟩⟩⟩
  have hi : Set.InjOn QuotientCode C := by
    intro u hu v hv heq
    obtain ⟨hu, hTu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hv, hTv⟩ := Finset.mem_filter.mp hv
    obtain ⟨_, _, hud, hue, _, _, _, _, _, _, _⟩ := mem_terminal.mp hu
    obtain ⟨_, _, hvd, hve, _, _, _, _, _, _, _⟩ := mem_terminal.mp hv
    have hNu := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hud)
    have hNv := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hvd)
    have hn := congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ, ℕ => z.2.2 * z.1) heq
    dsimp only [QuotientCode] at hn
    rw [hNu, hNv] at hn
    have hdEq : u.2.1 = v.2.1 := congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ, ℕ => z.2.2) heq
    have hrEq : u.1 / u.2.2 = v.1 / v.2.2 :=
      congrArg (fun z : Σ _ : ℕ, Σ _ : ℕ, ℕ => z.2.1) heq
    have hEu := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hue)
    have hEv := Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hve)
    rw [hrEq] at hEu
    have heProd : u.2.2 * (v.1 / v.2.2) = v.2.2 * (v.1 / v.2.2) :=
      hEu.trans (hn.trans hEv.symm)
    have hrpos : 0 < v.1 / v.2.2 := by
      have hh := (large_quotient_data hv hTv hAsq).2.2.1
      omega
    have heEq : u.2.2 = v.2.2 := Nat.eq_of_mul_eq_mul_right hrpos heProd
    exact Sigma.ext hn (heq_of_eq (Prod.ext hdEq heEq))
  have hh := Finset.card_le_card_of_injOn QuotientCode hm hi
  simpa only [C, LargeFibres, Finset.card_sigma] using hh

theorem terminal_split_count {A T : ℕ} (hA : 1 ≤ A) (hAsq : A < (T + 1)^2) :
    (TerminalCodes A).card ≤
      (∑ d ∈ Finset.Icc 1 T, (Anchor A d).divisors.card) +
      ∑ q ∈ Finset.Icc 3 (T + 1), ∑ r ∈ Finset.Icc 2 (q - 1),
        ((Finset.Icc 1 A).filter fun d =>
          A ≤ q * d ∧ q * d < A + d ∧ r / q.gcd r ∣ d).card := by
  have hs := small_step_count (T := T) hA
  have hl := large_step_count hAsq
  have hp := Finset.card_filter_add_card_filter_not (s := TerminalCodes A)
    (fun u => u.2.1 ≤ T)
  simp only [Nat.not_le] at hp
  omega

#print axioms anchor_eq
#print axioms stepCode_injective_on
#print axioms small_step_count
#print axioms reduced_gcd_dvd_iff
#print axioms large_quotient_data
#print axioms large_step_count
#print axioms terminal_split_count
end
end JSP233.TerminalCounting208
