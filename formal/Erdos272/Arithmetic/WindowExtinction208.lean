module

public import Erdos272.Arithmetic.WindowSums208
public import Erdos272.Arithmetic.CombinedCounts208
public import Erdos272.Arithmetic.LightPrice208

@[expose] public section

namespace JSP233.WindowExtinction208
open LightClosed208 WindowCounts208 WindowSums208 CombinedCounts208
set_option maxHeartbeats 0

theorem count_zero {q A B : ℕ} (h : q<A) : Count q A B=0 := by
  simp only [Count,if_neg (Nat.not_le.mpr h)]

theorem maximum_zero {A J B lo hi : ℕ} (hlh : lo≤hi) (hhi : hi<A) : maximum A J B lo hi=0 := by
  have hl : lo<A := hlh.trans_lt hhi
  have hj : ¬(A≤hi ∧ lo≤Last A B hi) := by omega
  simp only [maximum,rightIndexCount,count_zero hl,if_neg hj,Nat.zero_sub,max_self]

theorem maximum_sum_zero {A J B lo hi : ℕ} (hB : 0<B) (hAJ : A≤J) (hhi : hi<A) :
    maximum_sum A J B lo hi=0 := by
  have hl : RightLeft hi J B=0 := Nat.eq_zero_of_le_zero ((rightLeft_le hB).mpr
    (by simp only [Nat.zero_mul,Nat.add_zero];omega))
  have hw : rightWeight hi A J B=0 := by
    simp only [rightWeight,rightIndexCount,count_zero hhi,hl,Nat.zero_sub,Nat.zero_mul]
  have hj : ¬(J≤hi ∧ lo≤Last J B hi) := by omega
  simp only [maximum_sum,hw,if_neg hj,max_self]

theorem combined_zero {A K B h lo hi : ℕ} (hAK : A≤K) (hlh : lo≤hi) (hhi : hi<A) :
    maximum_combined A K B h lo hi=0 := by
  have hs : K≤Switch K B h := by unfold Switch;omega
  have hb : lo<Switch K B h := by omega
  have ha : ¬Switch K B h≤hi := by omega
  have he : min hi (Switch K B h-1)<A := (min_le_left _ _).trans_lt hhi
  simp only [maximum_combined,if_pos hb,if_neg ha,count_zero he,max_self]

theorem closed_zero {N d T E B V : ℕ} (hTV : T≤V) (hhi : N/d<T-E) :
    LightPrice208.Closed N d T E B V=0 := by
  have hK : N/d<V-E := by have :=Nat.sub_le_sub_right hTV E;omega
  have hw : WeightSum (N/d) T E B V=0 := by
    simp only [WeightSum,count_zero hhi,count_zero hK,Nat.zero_mul,Nat.zero_sub,Nat.mul_zero,add_zero]
  have hg : ¬(T-E≤N/d ∧ (N/d-(T-E))%B=0) := by omega
  simp only [LightPrice208.Closed,hw,Nat.mul_zero,LightPrice208.Correction,if_neg hg,Nat.sub_zero]

#print axioms maximum_zero
#print axioms maximum_sum_zero
#print axioms combined_zero
#print axioms closed_zero
end JSP233.WindowExtinction208
