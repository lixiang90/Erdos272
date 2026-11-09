module

public import Erdos272.Arithmetic.TotientFloor
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! The actual mixed primitive supply, from a finite Moebius sieve.
The endpoint a=r is excluded by the original geometric definition and costs
at most one, including when r=1. -/
namespace JSP233.MixedFloor29
open scoped BigOperators ArithmeticFunction.zeta
open ArithmeticFunction StaircaseCertificate TotientFloor29
noncomputable section

def CoprimeCount (h r : ℕ) : ℕ :=
  ((Finset.Icc 1 h).filter (fun a => Nat.gcd a r = 1)).card

theorem moebius_divisor_indicator (n : ℕ) :
    (∑ d ∈ n.divisors, (moebius d : ℝ)) = if n=1 then 1 else 0 := by
  have he := congrArg (fun f : ArithmeticFunction ℤ => f n) moebius_mul_coe_zeta
  rw [coe_mul_zeta_apply, ArithmeticFunction.one_apply] at he
  exact_mod_cast he

theorem gcd_divisors_eq_filter (a r : ℕ) (hr : 0 < r) :
    (Nat.gcd a r).divisors = r.divisors.filter (fun d => d ∣ a) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
  have hg : Nat.gcd a r ≠ 0 := by
    intro hz
    have hd := Nat.gcd_dvd_right a r
    rw [hz] at hd
    have : r = 0 := by simpa using hd
    omega
  simp [hg, ne_of_gt hr, and_comm]

theorem coprime_indicator (a r : ℕ) (hr : 0 < r) :
    (if Nat.gcd a r = 1 then (1:ℝ) else 0) =
      ∑ d ∈ r.divisors, if d ∣ a then (moebius d : ℝ) else 0 := by
  rw [← moebius_divisor_indicator, gcd_divisors_eq_filter a r hr, Finset.sum_filter]

theorem coprimeCount_floor (h r : ℕ) (hr : 0 < r) :
    (CoprimeCount h r : ℝ) =
      ∑ d ∈ r.divisors, (moebius d : ℝ) * ((h/d : ℕ) : ℝ) := by
  calc
    _ = ∑ a ∈ Finset.Icc 1 h, if Nat.gcd a r = 1 then (1:ℝ) else 0 := by
      simp [CoprimeCount]
    _ = ∑ a ∈ Finset.Icc 1 h,
        ∑ d ∈ r.divisors, if d ∣ a then (moebius d : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      exact coprime_indicator a r hr
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      have hdpos := Nat.pos_of_mem_divisors hd
      have hm := sum_multiples_reindex h d hdpos (fun _ => (moebius d : ℝ))
      simpa [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_comm] using hm

theorem coprimeCount_le_mixedSupply_add_one (h r : ℕ) :
    CoprimeCount h r ≤ MixedSupply h r + 1 := by
  classical
  unfold CoprimeCount MixedSupply
  calc
    _ ≤ (insert r ((Finset.range (h+1)).filter
        (fun a => 0<a ∧ Nat.gcd a r=1 ∧ a≠r))).card := by
      apply Finset.card_le_card
      intro a ha
      obtain ⟨ha, hg⟩ := Finset.mem_filter.mp ha
      by_cases he : a=r
      · simp [he]
      · apply Finset.mem_insert_of_mem
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_range.mpr (by have := Finset.mem_Icc.mp ha; omega),
          (Finset.mem_Icc.mp ha).1, hg, he⟩
    _ ≤ _ := Finset.card_insert_le _ _

theorem coprimeCount_lower (h r : ℕ) (hr : 0 < r) :
    (h : ℝ) * ((Nat.totient r : ℝ) / r) - divisorError r ≤ (CoprimeCount h r : ℝ) := by
  rw [coprimeCount_floor h r hr]
  have hs : (∑ d ∈ r.divisors,
      ((moebius d : ℝ) * ((h : ℝ)/d) - |(moebius d : ℝ)|)) ≤
      ∑ d ∈ r.divisors, (moebius d : ℝ) * ((h/d : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro d hd
    exact signed_floor_lower h d (Nat.pos_of_mem_divisors hd) _
  have he : (h : ℝ) * ((Nat.totient r : ℝ)/r) - divisorError r =
      ∑ d ∈ r.divisors, ((moebius d : ℝ)*((h : ℝ)/d)-|(moebius d : ℝ)|) := by
    rw [normalized_totient_identity r hr, Finset.mul_sum, Finset.sum_sub_distrib]
    unfold divisorError
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact hs

theorem mixedSupply_lower (h r : ℕ) (hr : 0 < r) :
    (h : ℝ) * ((Nat.totient r : ℝ)/r) - divisorError r - 1 ≤
      (MixedSupply h r : ℝ) := by
  have hl := coprimeCount_lower h r hr
  have hc : (CoprimeCount h r : ℝ) ≤ (MixedSupply h r : ℝ)+1 := by
    exact_mod_cast coprimeCount_le_mixedSupply_add_one h r
  linarith

#print axioms moebius_divisor_indicator
#print axioms gcd_divisors_eq_filter
#print axioms coprime_indicator
#print axioms coprimeCount_floor
#print axioms coprimeCount_le_mixedSupply_add_one
#print axioms coprimeCount_lower
#print axioms mixedSupply_lower
end
end JSP233.MixedFloor29
