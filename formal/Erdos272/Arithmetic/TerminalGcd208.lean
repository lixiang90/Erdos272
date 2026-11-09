module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! Finite reciprocal-square and triangular sums for the terminal gcd bound.
All quantities are finite; no numerical or asymptotic oracle is assumed. -/
namespace JSP233.TerminalGcd208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def SquareSum (H : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 H, 1 / (n : ℝ)^2
def Harmonic (H : ℕ) : ℝ := ∑ n ∈ Finset.Icc 1 H, 1 / (n : ℝ)
def Triangle (H : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 H, ∑ r ∈ Finset.Icc 1 (q - 1),
    1 / ((q : ℝ) * (q - 1) * r)

theorem icc_step (f : ℕ → ℝ) {a H : ℕ} (h : a ≤ H + 1) :
    (∑ n ∈ Finset.Icc a (H + 1), f n) = (∑ n ∈ Finset.Icc a H, f n) + f (H + 1) := by
  have hi : Finset.Icc a (H + 1) = insert (H + 1) (Finset.Icc a H) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  rw [hi, Finset.sum_insert (by simp)]
  ring

theorem square_step {H : ℕ} :
    SquareSum (H + 1) = SquareSum H + 1 / ((H : ℝ) + 1)^2 := by
  simp only [SquareSum, icc_step _ (show 1 ≤ H + 1 by omega), Nat.cast_add, Nat.cast_one]

theorem harmonic_step {H : ℕ} :
    Harmonic (H + 1) = Harmonic H + 1 / ((H : ℝ) + 1) := by
  simp only [Harmonic, icc_step _ (show 1 ≤ H + 1 by omega), Nat.cast_add, Nat.cast_one]

theorem square_tail {H : ℕ} (hH : 5 ≤ H) : SquareSum H + 1 / (H : ℝ) ≤ 5 / 3 := by
  induction H, hH using Nat.le_induction with
  | base => norm_num [SquareSum, Finset.sum_Icc_succ_top]
  | succ H hH ih =>
    have hpos : (0 : ℝ) < H := by exact_mod_cast (show 0 < H by omega)
    have hp : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    have hs : 1 / ((H : ℝ) + 1)^2 + 1 / ((H : ℝ) + 1) ≤ 1 / (H : ℝ) := by
      apply (le_div_iff₀ hpos).mpr
      field_simp
      nlinarith
    rw [square_step, Nat.cast_add, Nat.cast_one]
    linarith only [ih, hs]

theorem square_bound (H : ℕ) : SquareSum H ≤ 5 / 3 := by
  by_cases hH : 5 ≤ H
  · have hh := square_tail hH
    have hp : 0 ≤ 1 / (H : ℝ) := by positivity
    linarith
  · interval_cases H <;> norm_num [SquareSum, Finset.sum_Icc_succ_top]

theorem triangle_identity {H : ℕ} (hH : 1 ≤ H) :
    Triangle H = SquareSum H - Harmonic H / H := by
  induction H, hH using Nat.le_induction with
  | base => norm_num [Triangle, SquareSum, Harmonic]
  | succ H hH ih =>
    have hpos : (0 : ℝ) < H := by exact_mod_cast hH
    have hp : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    have ht : Triangle (H + 1) = Triangle H + Harmonic H / (((H : ℝ) + 1) * H) := by
      rw [Triangle, icc_step _ (show 2 ≤ H + 1 by omega)]
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
      change Triangle H + _ = Triangle H + _
      congr 1
      unfold Harmonic
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r hr
      field_simp
    rw [ht, ih, square_step, harmonic_step, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

theorem triangle_bound (H : ℕ) : Triangle H ≤ 5 / 3 := by
  by_cases hH : 1 ≤ H
  · rw [triangle_identity hH]
    have hh : 0 ≤ Harmonic H / H := by
      apply div_nonneg
      · unfold Harmonic
        exact Finset.sum_nonneg (fun n _ => by positivity)
      · positivity
    linarith only [square_bound H, hh]
  · have : H = 0 := by omega
    subst H
    norm_num [Triangle]

def Pairs (H : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 2 H).sigma fun q => Finset.Icc 1 (q - 1)

def GcdCode (p : Σ _ : ℕ, ℕ) : ℕ × (Σ _ : ℕ, ℕ) :=
  let d := p.1.gcd p.2
  (d, ⟨p.1 / d, p.2 / d⟩)

def Weight (p : Σ _ : ℕ, ℕ) : ℝ :=
  (p.1.gcd p.2 : ℕ) / ((p.1 : ℝ) * (p.1 - 1) * p.2)

def ProductWeight (c : ℕ × (Σ _ : ℕ, ℕ)) : ℝ :=
  (1 / (c.1 : ℝ)^2) * (1 / ((c.2.1 : ℝ) * (c.2.1 - 1) * c.2.2))

theorem gcd_code_mem {H : ℕ} {p : Σ _ : ℕ, ℕ} (hp : p ∈ Pairs H) :
    GcdCode p ∈ (Finset.Icc 1 H).product (Pairs H) := by
  obtain ⟨hq, hr⟩ := Finset.mem_sigma.mp hp
  obtain ⟨hq2, hqH⟩ := Finset.mem_Icc.mp hq
  obtain ⟨hr1, hrq⟩ := Finset.mem_Icc.mp hr
  let d := p.1.gcd p.2
  have hd : 0 < d := Nat.gcd_pos_of_pos_right _ (by omega)
  have hdq : d ≤ p.1 := Nat.gcd_le_left _ (by omega)
  have hdr : d ≤ p.2 := Nat.gcd_le_right _ (by omega)
  have hqa : d * (p.1 / d) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hrb : d * (p.2 / d) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have hb : 1 ≤ p.2 / d := Nat.div_pos hdr hd
  have hlt : p.2 < p.1 := by omega
  have hab : p.2 / d < p.1 / d :=
    Nat.lt_of_mul_lt_mul_left (show d * (p.2 / d) < d * (p.1 / d) by omega)
  change (d, ⟨p.1 / d, p.2 / d⟩) ∈ (Finset.Icc 1 H).product (Pairs H)
  apply Finset.mem_product.mpr
  refine ⟨Finset.mem_Icc.mpr ⟨by omega, hdq.trans hqH⟩, ?_⟩
  apply Finset.mem_sigma.mpr
  exact ⟨Finset.mem_Icc.mpr ⟨by change 2 ≤ p.1 / d; omega, (Nat.div_le_self _ _).trans hqH⟩,
    Finset.mem_Icc.mpr ⟨hb, by change p.2 / d ≤ p.1 / d - 1; omega⟩⟩

theorem gcd_code_injective {H : ℕ} : Set.InjOn GcdCode (Pairs H) := by
  intro p hp v hv he
  have hq := congrArg (fun c : ℕ × (Σ _ : ℕ, ℕ) => c.1 * c.2.1) he
  have hr := congrArg (fun c : ℕ × (Σ _ : ℕ, ℕ) => c.1 * c.2.2) he
  dsimp only [GcdCode] at hq hr
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)] at hq
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _),
    Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)] at hr
  exact Sigma.ext hq (heq_of_eq hr)

theorem gcd_weight_le {H : ℕ} {p : Σ _ : ℕ, ℕ} (hp : p ∈ Pairs H) :
    Weight p ≤ ProductWeight (GcdCode p) := by
  have hc := gcd_code_mem hp
  obtain ⟨hd, hab⟩ := Finset.mem_product.mp hc
  obtain ⟨ha, hb⟩ := Finset.mem_sigma.mp hab
  obtain ⟨hd1, hdH⟩ := Finset.mem_Icc.mp hd
  obtain ⟨ha2, haH⟩ := Finset.mem_Icc.mp ha
  obtain ⟨hb1, hba⟩ := Finset.mem_Icc.mp hb
  let d := p.1.gcd p.2
  let a := p.1 / d
  let b := p.2 / d
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  have hqa : (p.1 : ℝ) = (d : ℝ) * a := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
  have hrb : (p.2 : ℝ) = (d : ℝ) * b := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
  have hfac : (d : ℝ) * (a - 1) ≤ d * a - 1 := by nlinarith only [hdR]
  have hden : (d : ℝ)^2 * a * (a - 1) * b ≤ d * a * b * (d * a - 1) := by
    convert mul_le_mul_of_nonneg_left hfac (show (0 : ℝ) ≤ d * a * b by positivity) using 1 <;> first | rfl | ring
  have hdpos : (0 : ℝ) < d := by linarith only [hdR]
  have hapos : (0 : ℝ) < a := by linarith only [haR]
  have hbpos : (0 : ℝ) < b := by linarith only [hbR]
  have hampos : (0 : ℝ) < a - 1 := by linarith only [haR]
  have hbase := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < d^2 * a * (a - 1) * b) hden
  change (d : ℝ) / ((p.1 : ℝ) * (p.1 - 1) * p.2) ≤
    (1 / (d : ℝ)^2) * (1 / ((a : ℝ) * (a - 1) * b))
  rw [hqa, hrb]
  convert hbase using 1 <;> first | rfl | field_simp

theorem full_gcd_bound (H : ℕ) : (∑ p ∈ Pairs H, Weight p) ≤ 25 / 9 := by
  have himage : (Pairs H).image GcdCode ⊆ (Finset.Icc 1 H).product (Pairs H) := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
    exact gcd_code_mem hp
  have hprod : (∑ c ∈ (Finset.Icc 1 H).product (Pairs H), ProductWeight c) =
      SquareSum H * Triangle H := by
    simp only [Finset.product_eq_sprod, Finset.sum_product, ProductWeight, Pairs,
      Finset.sum_sigma, SquareSum, Triangle, Finset.sum_mul]
    congr 1
    ext d
    rw [Finset.mul_sum]
    congr 1
    ext q
    rw [Finset.mul_sum]
  calc
    _ ≤ ∑ p ∈ Pairs H, ProductWeight (GcdCode p) := Finset.sum_le_sum (fun p hp => gcd_weight_le hp)
    _ = ∑ c ∈ (Pairs H).image GcdCode, ProductWeight c := (Finset.sum_image gcd_code_injective).symm
    _ ≤ ∑ c ∈ (Finset.Icc 1 H).product (Pairs H), ProductWeight c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg himage
      intro c hc hnot
      unfold ProductWeight
      have hm : 0 ≤ (c.2.1 : ℝ) - 1 := by
        have hh := (Finset.mem_Icc.mp (Finset.mem_sigma.mp (Finset.mem_product.mp hc).2).1).1
        have : (2 : ℝ) ≤ c.2.1 := by exact_mod_cast hh
        linarith
      positivity
    _ = SquareSum H * Triangle H := hprod
    _ ≤ (5 / 3 : ℝ) * (5 / 3) := by
      apply mul_le_mul (square_bound H) (triangle_bound H)
      · unfold Triangle
        apply Finset.sum_nonneg
        intro q hq
        apply Finset.sum_nonneg
        intro r hr
        have hh : (2 : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Icc.mp hq).1
        have hm : (0 : ℝ) ≤ q - 1 := by linarith
        positivity
      · norm_num
    _ = 25 / 9 := by norm_num

def Coefficient (H : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 3 H, ∑ r ∈ Finset.Icc 2 (q - 1),
    (q.gcd r : ℕ) / ((q : ℝ) * (q - 1) * r)

def Boundary (H : ℕ) : ℝ := ∑ q ∈ Finset.Icc 2 H, 1 / ((q : ℝ) * (q - 1))

theorem boundary_identity {H : ℕ} (hH : 1 ≤ H) : Boundary H = 1 - 1 / (H : ℝ) := by
  induction H, hH using Nat.le_induction with
  | base => norm_num [Boundary]
  | succ H hH ih =>
    have ht : Boundary (H + 1) = Boundary H + 1 / (((H : ℝ) + 1) * H) := by
      simp only [Boundary, icc_step _ (show 2 ≤ H + 1 by omega),
        Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    have hp : (0 : ℝ) < H := by exact_mod_cast hH
    rw [ht, ih, Nat.cast_add, Nat.cast_one]
    field_simp
    ring

theorem full_gcd_split {H : ℕ} (hH : 1 ≤ H) :
    (∑ p ∈ Pairs H, Weight p) = Coefficient H + Boundary H := by
  have hrow : ∀ q ∈ Finset.Icc 2 H,
      (∑ r ∈ Finset.Icc 1 (q - 1), Weight ⟨q, r⟩) =
        1 / ((q : ℝ) * (q - 1)) + ∑ r ∈ Finset.Icc 2 (q - 1), Weight ⟨q, r⟩ := by
    intro q hq
    have hq2 := (Finset.mem_Icc.mp hq).1
    have hi : Finset.Icc 1 (q - 1) = insert 1 (Finset.Icc 2 (q - 1)) := by
      ext r
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hi, Finset.sum_insert (by simp)]
    simp only [Weight, Nat.gcd_one_right, Nat.cast_one, mul_one]
  have hinner : (∑ q ∈ Finset.Icc 2 H, ∑ r ∈ Finset.Icc 2 (q - 1), Weight ⟨q, r⟩) = Coefficient H := by
    by_cases hH2 : 2 ≤ H
    · have hi : Finset.Icc 2 H = insert 2 (Finset.Icc 3 H) := by
        ext q
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hi, Finset.sum_insert (by simp)]
      simp only [Nat.reduceSub, Finset.Icc_eq_empty_of_lt (by omega : 1 < 2),
        Finset.sum_empty, zero_add, Coefficient, Weight]
    · have hH1 : H = 1 := by omega
      subst H
      norm_num [Coefficient]
  simp only [Pairs, Finset.sum_sigma]
  calc
    _ = ∑ q ∈ Finset.Icc 2 H, (1 / ((q : ℝ) * (q - 1)) +
        ∑ r ∈ Finset.Icc 2 (q - 1), Weight ⟨q, r⟩) := Finset.sum_congr rfl hrow
    _ = Coefficient H + Boundary H := by
      rw [Finset.sum_add_distrib, hinner]
      exact add_comm _ _

theorem coefficient_bound {H : ℕ} (hH : 1 ≤ H) :
    Coefficient H ≤ 16 / 9 + 1 / (H : ℝ) := by
  have hf := full_gcd_bound H
  rw [full_gcd_split hH, boundary_identity hH] at hf
  linarith only [hf]

#print axioms square_bound
#print axioms triangle_bound
#print axioms full_gcd_bound
#print axioms coefficient_bound
end
end JSP233.TerminalGcd208
