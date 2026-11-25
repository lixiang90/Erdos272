module

public import Erdos272.Capacity.N20258.VariablePrice20258

@[expose] public section
namespace JSP233.PriceChord20258
set_option autoImplicit false

def target {K : Type*} [Field K] (n : K) := n*(n+1)/2+n/4

def allowance {K : Type*} [Field K] (n x : K) :=
  target n*x-VariablePrice20258.bound n x

/-- Keep the triple price fixed over a block. After removing the selected
progressions, the budget available for the remaining terms lies above its
chord whenever the third-degree coefficient dominates the quadratic one. -/
theorem between {a n b x K : ℝ} (lo : a≤n) (hi : n≤b)
    (bend : 387679*x≤138655*(a+n+b)+99000)
    (left : K≤allowance a x) (right : K≤allowance b x) : K≤allowance n x := by
  by_cases same : a=b
  · have eqn : a=n := by linarith only [lo,hi,same]
    simpa only [←eqn] using left
  have length : 0<b-a := by linarith only [lt_of_le_of_ne (lo.trans hi) same]
  have w := add_le_add (mul_le_mul_of_nonneg_left left (sub_nonneg.mpr hi))
    (mul_le_mul_of_nonneg_left right (sub_nonneg.mpr lo))
  have curve := mul_nonneg (mul_nonneg (sub_nonneg.mpr lo) (sub_nonneg.mpr hi))
    (sub_nonneg.mpr bend)
  have chord : (b-n)*allowance a x+(n-a)*allowance b x≤(b-a)*allowance n x := by
    unfold allowance target VariablePrice20258.bound
    nlinarith only [mul_nonneg length.le curve]
  have final : (b-a)*K≤(b-a)*allowance n x := by linarith only [w,chord]
  exact le_of_mul_le_mul_left final length

theorem target_le {N : ℕ} (pos : 1≤N) :
    target (((N-1:ℕ):ℝ))≤(B N:ℝ) := by
  have n : ((N-1:ℕ):ℝ)+1=N := by exact_mod_cast (show N-1+1=N by omega)
  have rem : ((N-1:ℕ):ℝ)≤4*((((N-1)/4:ℕ):ℝ))+3 := by
    exact_mod_cast (show N-1≤4*((N-1)/4)+3 by omega)
  unfold target B
  push_cast
  rw [Nat.cast_choose_two]
  nlinarith only [n,rem,congrArg (fun t : ℝ => t*(t-1)) n]

#print axioms between
#print axioms target_le
end JSP233.PriceChord20258
