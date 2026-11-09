module

public import Erdos272.Arithmetic.ThreePool124
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
namespace JSP233.CompletePool126
open ThreePool124 ParityPool123 DivisorMoment45 SimplexMoment57
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem small_odd_pool_full (q : ℕ) : SmallOddPool q q=
    (QuadPool q).filter (fun z=>¬(2∣z.2.1 ∧ 2∣z.2.2.1)) := by
  ext z
  rcases z with ⟨g,r,s,t⟩
  simp only [SmallOddPool,QuadPool,Finset.mem_filter,Finset.mem_sigma]
  tauto

theorem actual_odd_pair_cube_full (q : ℕ) :
    OddPairCube q q+DivCount 3 (q/4)=DivCount 3 q := by
  have h := Finset.card_filter_add_card_filter_not
    (s:=QuadPool q) (p:=fun z=>2∣z.2.1 ∧ 2∣z.2.2.1)
  rw [←small_odd_pool_full,←EvenPool,small_odd_pool_card,even_pool_card,
    quad_pool_eq_div_count,quad_pool_eq_div_count] at h
  omega

theorem actual_divisor_second_moment_full_two_three_nat (N : ℕ) :
    (∑n∈Finset.Icc 1 N,n.divisors.card^2)+DivCount 3 (N/4)+DivCount 3 (N/9)≤
      DivCount 3 N+DivCount 3 (N/36) := by
  have h := actual_divisor_second_moment_three_nat N (N/9)
  have he := actual_odd_pair_cube_full (N/9)
  have hd : N/9/4=N/36 := by rw [Nat.div_div_eq_div_mul]
  rw [hd] at he
  omega

theorem actual_divisor_second_moment_full_two_three (N : ℕ) :
    (∑n∈Finset.Icc 1 N,(n.divisors.card:ℝ)^2)+(DivCount 3 (N/4):ℝ)+(DivCount 3 (N/9):ℝ)≤
      (DivCount 3 N:ℝ)+(DivCount 3 (N/36):ℝ) := by
  exact_mod_cast actual_divisor_second_moment_full_two_three_nat N

#print axioms small_odd_pool_full
#print axioms actual_odd_pair_cube_full
#print axioms actual_divisor_second_moment_full_two_three_nat
#print axioms actual_divisor_second_moment_full_two_three
end
end JSP233.CompletePool126
