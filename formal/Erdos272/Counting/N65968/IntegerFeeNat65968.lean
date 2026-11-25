module

public import Erdos272.Counting.N65968.IntegerFee65968
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace JSP233.IntegerFeeNat65968
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Upper (N a b c : ℕ) : ℝ :=
  (N : ℝ)^2*a/1000000000000+(253/35 : ℝ)*N+
    (c : ℝ)+(N : ℝ)*((b : ℝ)/1000000000000)

theorem upper_cast (N a b c : ℕ) : Upper N a b c=
    IntegerFee65968.Upper N 1000000000000 (253/35) a b c := by
  simp only [Upper,IntegerFee65968.Upper,Int.cast_natCast]

theorem zero_head (p : ℕ → ℕ) (f : ℕ → ℝ) (R : ℕ) :
    (∑ i∈Finset.range (R+1), ((p (i+1) : ℝ)-p i)*
      (if i=0 then 0 else f (i-1)))=
    ∑ i∈Finset.range R, (((p (i+2) : ℤ)-(p (i+1) : ℤ) : ℤ) : ℝ)*f i := by
  rw [Nat.add_comm R 1,Finset.sum_range_add]
  simp only [Finset.sum_range_one,ite_true,mul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i _hi
  have hn : 1+i≠0 := by omega
  have hs : 1+i-1=i := by omega
  have ht : 1+i+1=i+2 := by omega
  rw [if_neg hn,hs,ht]
  simp only [Int.cast_sub,Int.cast_natCast,Nat.add_comm]

#print axioms upper_cast
#print axioms zero_head
end
end JSP233.IntegerFeeNat65968
