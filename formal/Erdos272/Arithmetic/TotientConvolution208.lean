module

public import Erdos272.Arithmetic.APInterval208
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! # The exact totient convolution underlying the unit source

All sums are finite. The change of variables `(q,d) ↦ (qd,q)` is proved
as a bijection, after discarding the zero positive-part terms.
-/
namespace JSP233.TotientConvolution208
open PureSource208 APInterval208
open scoped BigOperators

def Products (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 s).product (Finset.Icc 1 s)).filter fun p => p.1 * p.2 ≤ s

def Divisors (s : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 s).product (Finset.Icc 1 s)).filter fun p => p.2 ∣ p.1

theorem mem_products {s q d : ℕ} :
    (q, d) ∈ Products s ↔ 1 ≤ q ∧ q ≤ s ∧ 1 ≤ d ∧ d ≤ s ∧ q * d ≤ s := by
  simp only [Products, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, and_assoc]

theorem mem_divisors {s n q : ℕ} :
    (n, q) ∈ Divisors s ↔ 1 ≤ n ∧ n ≤ s ∧ 1 ≤ q ∧ q ≤ s ∧ q ∣ n := by
  simp only [Divisors, Finset.mem_filter, Finset.product_eq_sprod, Finset.mem_product,
    Finset.mem_Icc, and_assoc]

theorem change_variables (s : ℕ) :
    (∑ p ∈ Products s, Nat.totient p.1 * (s - p.1 * p.2)) =
      ∑ p ∈ Divisors s, Nat.totient p.2 * (s - p.1) := by
  apply Finset.sum_bij (fun p _ => (p.1 * p.2, p.1))
  · rintro ⟨q, d⟩ hp
    obtain ⟨hq, hqs, hd, hds, hprod⟩ := mem_products.mp hp
    apply mem_divisors.mpr
    exact ⟨by nlinarith, hprod, hq, hqs, dvd_mul_right q d⟩
  · rintro ⟨q, d⟩ hp ⟨r, e⟩ hr he
    have hqr : q = r := congrArg Prod.snd he
    have hprod : q * d = r * e := congrArg Prod.fst he
    have hq : 0 < q := by have hh := (mem_products.mp hp).1; omega
    apply Prod.ext
    · exact hqr
    · rw [← hqr] at hprod
      exact Nat.eq_of_mul_eq_mul_left hq hprod
  · rintro ⟨n, q⟩ hp
    obtain ⟨hn, hns, hq, hqs, hdiv⟩ := mem_divisors.mp hp
    have hqn : q ≤ n := Nat.le_of_dvd hn hdiv
    have hqd : q * (n / q) = n := Nat.mul_div_cancel' hdiv
    refine ⟨(q, n / q), ?_, ?_⟩
    · apply mem_products.mpr
      exact ⟨hq, hqs, Nat.div_pos hqn hq, (Nat.div_le_self n q).trans hns, by omega⟩
    · exact Prod.ext hqd rfl
  · intro p hp
    rfl

theorem divisor_row {s n : ℕ} (hn : n ∈ Finset.Icc 1 s) :
    (Finset.Icc 1 s).filter (· ∣ n) = n.divisors := by
  obtain ⟨hn, hns⟩ := Finset.mem_Icc.mp hn
  ext q
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hq, hqs⟩, hd⟩
    exact ⟨hd, by omega⟩
  · rintro ⟨hd, hn0⟩
    have hq : 0 < q := Nat.pos_of_dvd_of_pos hd hn
    have hqn : q ≤ n := Nat.le_of_dvd hn hd
    exact ⟨⟨hq, hqn.trans hns⟩, hd⟩

theorem full_convolution (s : ℕ) :
    (∑ q ∈ Finset.Icc 1 s, Nat.totient q * intervalMultiplicity s q) =
      ∑ n ∈ Finset.Icc 1 s, n * (s - n) := by
  have hprod : (∑ q ∈ Finset.Icc 1 s, Nat.totient q * intervalMultiplicity s q) =
      ∑ p ∈ Products s, Nat.totient p.1 * (s - p.1 * p.2) := by
    unfold intervalMultiplicity Products
    rw [Finset.sum_filter]
    simp only [Finset.product_eq_sprod, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hqd : q * d ≤ s
    · simp only [if_pos hqd, Nat.mul_comm d q]
    · simp only [if_neg hqd, Nat.mul_comm d q, Nat.sub_eq_zero_of_le (by omega : s ≤ q * d),
        Nat.mul_zero]
  rw [hprod, change_variables]
  unfold Divisors
  rw [Finset.sum_filter]
  simp only [Finset.product_eq_sprod, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    (∑ q ∈ Finset.Icc 1 s, if q ∣ n then Nat.totient q * (s - n) else 0) =
        ∑ q ∈ (Finset.Icc 1 s).filter (· ∣ n), Nat.totient q * (s - n) :=
      (Finset.sum_filter _ _).symm
    _ = ∑ q ∈ n.divisors, Nat.totient q * (s - n) := by rw [divisor_row hn]
    _ = n * (s - n) := by rw [← Finset.sum_mul, Nat.sum_totient]

theorem sum_Icc_eq_choose_two (s : ℕ) :
    (∑ n ∈ Finset.Icc 1 s, n) = (s + 1).choose 2 := by
  have hsum := sum_Icc_twice s
  have hc := choose_two_twice (s + 1)
  nlinarith only [hsum, hc]

theorem weighted_sum_eq_choose_three (s : ℕ) :
    (∑ n ∈ Finset.Icc 1 s, n * (s - n)) = (s + 1).choose 3 := by
  induction s with
  | zero => norm_num [Nat.choose]
  | succ s ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
    have he : (∑ n ∈ Finset.Icc 1 s, n * (s + 1 - n)) =
        (∑ n ∈ Finset.Icc 1 s, n * (s - n)) + ∑ n ∈ Finset.Icc 1 s, n := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n hn
      have hns := (Finset.mem_Icc.mp hn).2
      have hsub : s + 1 - n = s - n + 1 := by omega
      rw [hsub]
      ring
    rw [he, ih, sum_Icc_eq_choose_two]
    have hc := Nat.choose_succ_succ (s + 1) 2
    simp only [Nat.succ_eq_add_one] at hc
    norm_num at hc
    omega

theorem full_source_sum (s : ℕ) :
    (∑ q ∈ Finset.Icc 1 s, Nat.totient q * intervalMultiplicity s q) =
      (s + 1).choose 3 := by
  rw [full_convolution, weighted_sum_eq_choose_three]

theorem intervalMultiplicity_self (s : ℕ) : intervalMultiplicity s s = 0 := by
  unfold intervalMultiplicity
  apply Finset.sum_eq_zero
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  apply Nat.sub_eq_zero_of_le
  nlinarith

theorem intervalMultiplicity_one (s : ℕ) : intervalMultiplicity s 1 = s.choose 2 := by
  rw [← bound_eq_intervalMultiplicity (by decide : 1 ≤ 1)]
  rfl

/-- The complete primitive three-point source has exactly `choose s 3`
elements after the one-dimensional pair contribution is removed. -/
theorem full_triple_source {s : ℕ} (hs : 2 ≤ s) :
    (∑ q ∈ Finset.Ico 2 s, Nat.totient q * intervalMultiplicity s q) = s.choose 3 := by
  let f : ℕ → ℕ := fun q => Nat.totient q * intervalMultiplicity s q
  have hmem : 1 ∈ Finset.Icc 1 s := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Finset.Icc 1 s).erase 1 = Finset.Ico 2 (s + 1) := by
    ext q
    simp only [Finset.mem_erase, Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hsplit := Finset.sum_erase_add (Finset.Icc 1 s) f hmem
  rw [he, Finset.sum_Ico_succ_top hs] at hsplit
  have hz : f s = 0 := by simp [f, intervalMultiplicity_self]
  have hone : f 1 = s.choose 2 := by simp [f, intervalMultiplicity_one]
  rw [hz, hone, Nat.add_zero] at hsplit
  have hfull := full_source_sum s
  have hc := Nat.choose_succ_succ s 2
  simp only [Nat.succ_eq_add_one] at hc
  norm_num at hc
  dsimp only [f] at hsplit
  omega

theorem source_prefix_add_tail {s e : ℕ} (he : 2 ≤ s - e) :
    (∑ q ∈ Finset.Ico 2 (s - e), Nat.totient q * intervalMultiplicity s q) +
      physicalK s e = s.choose 3 := by
  have hle : s - e ≤ s := Nat.sub_le s e
  have hsplit := Finset.sum_Ico_consecutive
    (fun q => Nat.totient q * intervalMultiplicity s q) he hle
  rw [full_triple_source (by omega : 2 ≤ s)] at hsplit
  exact hsplit

#print axioms change_variables
#print axioms full_convolution
#print axioms full_source_sum
#print axioms full_triple_source
#print axioms source_prefix_add_tail
end JSP233.TotientConvolution208
