module

public import Erdos272.Arithmetic.N190000.PrimeHead190000

@[expose] public section

namespace JSP233.PrimeReciprocal180000
open CoreUnionSource200000 PrimeQuadratic200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem range_dyadic (k : ℕ) :
    (∑ j ∈ Finset.range (2^k), (1 : ℝ)/((j : ℝ)+1)) ≤ (k : ℝ)+1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have hp : 0 < (2 : ℕ)^k := pow_pos (by decide) k
    have hpr : (0 : ℝ) < ((2 : ℕ)^k : ℝ) := by exact_mod_cast hp
    have ht : (2 : ℕ)^(k+1) = 2^k+2^k := by rw [pow_succ]; omega
    rw [ht, Finset.sum_range_add]
    have hb : (∑ j ∈ Finset.range (2^k), (1 : ℝ)/(((2^k+j : ℕ) : ℝ)+1)) ≤ 1 := by
      calc
        _ ≤ ∑ _j ∈ Finset.range (2^k), (1 : ℝ)/((2 : ℕ)^k : ℝ) := by
          apply Finset.sum_le_sum
          intro j _
          apply one_div_le_one_div_of_le hpr
          push_cast
          have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith only [hj]
        _ = 1 := by simp [one_div]
    push_cast at hb
    push_cast
    linarith only [ih, hb]

theorem prime_reciprocal_half {a k : ℕ} (ha : a ≤ 2^k) (hk : 1 ≤ k) :
    (∑ q ∈ AllPrimes a, (1 : ℝ)/(q : ℝ)) ≤ ((k : ℝ)+1)/2 := by
  let m := 2^(k-1)
  have ht : (2 : ℕ)^k = 2*m := by
    dsimp only [m]
    have he : k-1+1 = k := by omega
    have hh := pow_succ (2 : ℕ) (k-1)
    rw [he] at hh
    omega
  have hsub : AllPrimes a ⊆ insert 2 (OddSet m) := by
    intro q hq
    obtain ⟨hr, hp⟩ := Finset.mem_filter.mp hq
    by_cases htwo : q = 2
    · exact Finset.mem_insert.mpr (Or.inl htwo)
    · have hodd : q%2 = 1 := hp.eq_two_or_odd.resolve_left htwo
      let j := (q-3)/2
      have he : 2*j+3 = q := by have := hp.two_le; dsimp only [j]; omega
      have hj : j < m := by
        have hlt := (Finset.mem_range.mp hr).trans_le ha
        dsimp only [j]
        omega
      exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, he⟩))
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => by positivity : ∀ q ∈ insert 2 (OddSet m), q ∉ AllPrimes a → (0 : ℝ) ≤ 1/q)
  have hnot : 2 ∉ OddSet m := by
    intro hh
    obtain ⟨j, _, he⟩ := Finset.mem_image.mp hh
    omega
  have hinj : Function.Injective (fun j : ℕ => 2*j+3) := by
    intro i j he
    dsimp only at he
    omega
  have he : (∑ q ∈ OddSet m, (1 : ℝ)/(q : ℝ)) =
      ∑ j ∈ Finset.range m, (1 : ℝ)/(2*(j : ℝ)+3) := by
    rw [OddSet, Finset.sum_image hinj.injOn]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  rw [Finset.sum_insert hnot, he] at hs
  have hb : (∑ j ∈ Finset.range m, (1 : ℝ)/(2*(j : ℝ)+3)) ≤
      (1/2 : ℝ)*(∑ j ∈ Finset.range m, (1 : ℝ)/((j : ℝ)+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hh := one_div_le_one_div_of_le (show (0 : ℝ) < 2*((j : ℝ)+1) by positivity)
      (show 2*((j : ℝ)+1) ≤ 2*(j : ℝ)+3 by linarith)
    have hi : (1 : ℝ)/(2*((j : ℝ)+1)) = (1/2 : ℝ)*(1/((j : ℝ)+1)) := by
      field_simp
    exact hh.trans_eq hi
  have hd := range_dyadic (k-1)
  have hcast : ((k-1 : ℕ) : ℝ)+1 = (k : ℝ) := by rw [Nat.cast_sub hk]; norm_num
  rw [hcast] at hd
  change (∑ j ∈ Finset.range m, (1 : ℝ)/((j : ℝ)+1)) ≤ (k : ℝ) at hd
  norm_num only [Nat.cast_ofNat] at hs
  linarith only [hs, hb, hd]

#print axioms range_dyadic
#print axioms prime_reciprocal_half
end
end JSP233.PrimeReciprocal180000
