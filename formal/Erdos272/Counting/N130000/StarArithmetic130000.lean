module

public import Erdos272.Counting.N158375.StarArithmetic158375

@[expose] public section

namespace JSP233.StarArithmetic130000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Bonus (Q : Finset ℕ) (a : ℕ) : ℕ :=
  ∑ q ∈ Q, (a/(2*q)).choose 2

theorem divided_choose_scaled_step (n k : ℕ) (hk : 0 < k) :
    k*((n+1)/k).choose 2 ≤ k*(n/k).choose 2+n := by
  have h₁ : n/k ≤ (n+1)/k := Nat.div_le_div_right (by omega)
  have h₂ : (n+1)/k ≤ n/k+1 := by
    apply (Nat.div_le_iff_le_mul hk).mpr
    have hm := Nat.mod_lt n hk
    have he := Nat.mod_add_div n k
    have hb : n+1 ≤ (n/k+1)*k := by nlinarith only [hm, he]
    omega
  by_cases he : (n+1)/k = n/k
  · rw [he]; omega
  · have he' : (n+1)/k = n/k+1 := by omega
    rw [he', StarArithmetic158375.choose_succ_two]
    have hm := Nat.mul_div_le n k
    nlinarith only [hm]

theorem divided_choose_real_step (n k : ℕ) (hk : 0 < k) :
    (((n+1)/k).choose 2 : ℝ) ≤ ((n/k).choose 2 : ℝ)+(n : ℝ)/k := by
  have hr : (k : ℝ)*(((n+1)/k).choose 2 : ℝ) ≤
      (k : ℝ)*((n/k).choose 2 : ℝ)+n := by
    exact_mod_cast divided_choose_scaled_step n k hk
  have hkR : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hh : (((n+1)/k).choose 2 : ℝ)-((n/k).choose 2 : ℝ) ≤ (n : ℝ)/k := by
    apply (le_div_iff₀ hkR).mpr
    nlinarith only [hr]
  linarith only [hh]

theorem reciprocal_subset {A Q : Finset ℕ} (hAQ : A ⊆ Q)
    (hrec : (∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) ≤ 1) :
    (∑ q ∈ A, (1 : ℝ)/(q : ℝ)) ≤ 1 := by
  apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg hAQ ?_) hrec
  intro q _ _
  positivity

theorem divided_choose_sum_step (Q : Finset ℕ) (n : ℕ)
    (hpos : ∀ q ∈ Q, 0 < q) (hrec : (∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) ≤ 1) :
    (∑ q ∈ Q, ((n+1)/q).choose 2) ≤ (∑ q ∈ Q, (n/q).choose 2)+n := by
  have hs := Finset.sum_le_sum (s := Q) (fun q hq => divided_choose_real_step n q (hpos q hq))
  have hdiv : (∑ q ∈ Q, (n : ℝ)/(q : ℝ)) =
      (n : ℝ)*(∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    rw [mul_one_div]
  rw [Finset.sum_add_distrib, hdiv] at hs
  have hr := mul_le_mul_of_nonneg_left hrec (Nat.cast_nonneg (α := ℝ) n)
  have hh : (∑ q ∈ Q, (((n+1)/q).choose 2 : ℝ)) ≤
      (∑ q ∈ Q, ((n/q).choose 2 : ℝ))+n := by nlinarith only [hs, hr]
  exact_mod_cast hh

theorem divided_choose_sum_contract {Q : Finset ℕ} {b c : ℕ}
    (hpos : ∀ q ∈ Q, 0 < q) (hrec : (∑ q ∈ Q, (1 : ℝ)/(q : ℝ)) ≤ 1)
    (hbc : b ≤ c) :
    b.choose 2+(∑ q ∈ Q, (c/q).choose 2) ≤
      c.choose 2+(∑ q ∈ Q, (b/q).choose 2) := by
  induction c, hbc using Nat.le_induction with
  | base => omega
  | succ c hbc ih =>
      have hs := divided_choose_sum_step Q c hpos hrec
      rw [StarArithmetic158375.choose_succ_two]
      omega

theorem bonus_mono {Q : Finset ℕ} {a b : ℕ} (hab : a ≤ b) : Bonus Q a ≤ Bonus Q b := by
  exact Finset.sum_le_sum (fun q _ => Nat.choose_le_choose 2 (Nat.div_le_div_right hab))

theorem bonus_filter {Q : Finset ℕ} {a : ℕ} (hpos : ∀ q ∈ Q, 0 < q) :
    Bonus (Q.filter (fun q => q < a)) a = Bonus Q a := by
  unfold Bonus
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hqa : q < a
  · simp only [if_pos hqa]
  · have hz : a/(2*q) = 0 := Nat.div_eq_of_lt (by have := hpos q hq; omega)
    simp only [if_neg hqa, hz, Nat.choose_zero_succ]

#print axioms divided_choose_scaled_step
#print axioms divided_choose_real_step
#print axioms reciprocal_subset
#print axioms divided_choose_sum_step
#print axioms divided_choose_sum_contract
#print axioms bonus_mono
#print axioms bonus_filter
end
end JSP233.StarArithmetic130000
