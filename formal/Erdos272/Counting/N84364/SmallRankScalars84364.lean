module

public import Mathlib.Data.Nat.Dist
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.SmallRankScalars84364
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

def rankExcess (a i : ℕ) : ℕ := Nat.dist i (a-1-i)-1

theorem rank_excess_inner {a i : ℕ} (hi : i<a) :
    rankExcess (a+2) (i+1)=rankExcess a i := by
  have he : a+2-1-(i+1)=(a-1-i)+1 := by omega
  unfold rankExcess
  rw [he, Nat.dist_add_add_right]

theorem rank_excess_step (a : ℕ) :
    (∑ i ∈ Finset.range (a+2), rankExcess (a+2) i)=
      (∑ i ∈ Finset.range a, rankExcess a i)+2*a := by
  have hfirst : rankExcess (a+2) 0=a := by
    unfold rankExcess Nat.dist
    omega
  have hlast : rankExcess (a+2) (a+1)=a := by
    unfold rankExcess Nat.dist
    omega
  have hsum : (∑ i ∈ Finset.range a, rankExcess (a+2) (i+1))=
      ∑ i ∈ Finset.range a, rankExcess a i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact rank_excess_inner (Finset.mem_range.mp hi)
  rw [Finset.sum_range_succ', Finset.sum_range_succ, hsum, hfirst, hlast]
  omega

theorem floor_square_step (a : ℕ) :
    (a+1)^2/4=(a-1)^2/4+a := by
  cases a with
  | zero => norm_num
  | succ b =>
    change (b+2)^2/4=b^2/4+(b+1)
    have he : (b+2)^2=b^2+(b+1)*4 := by ring
    rw [he]
    omega

theorem rank_excess_sum (a : ℕ) :
    (∑ i ∈ Finset.range a, rankExcess a i)=2*((a-1)^2/4) := by
  induction a using Nat.twoStepInduction with
  | zero => norm_num [rankExcess]
  | one => norm_num [rankExcess]
  | more a ha _ha1 =>
    have he : a+2-1=a+1 := by omega
    rw [rank_excess_step, ha, he, floor_square_step]
    omega

def rankCapacity (N i k : ℕ) : ℝ :=
  (k : ℝ)*(2*(N : ℝ)-2*(i : ℝ)-(k : ℝ)-3)

theorem capacity_mono {N L i x y : ℕ}
    (hN : 2*L+1≤N) (hi : i+1≤L) (hxy : x≤y) (hy : y≤L) :
    rankCapacity N i x≤rankCapacity N i y := by
  have hn : 2*(L : ℝ)+1≤N := by exact_mod_cast hN
  have hir : (i : ℝ)+1≤L := by exact_mod_cast hi
  have hxyr : (x : ℝ)≤y := by exact_mod_cast hxy
  have hyr : (y : ℝ)≤L := by exact_mod_cast hy
  have hcoef : 0≤2*(N : ℝ)-2*(i : ℝ)-(x : ℝ)-(y : ℝ)-3 := by
    linarith only [hn, hir, hxyr, hyr]
  have hp := mul_nonneg (sub_nonneg.mpr hxyr) hcoef
  dsimp only [rankCapacity]
  nlinarith only [hp]

theorem distance_excess_bounds (i j : ℕ) :
    (i : ℝ)-j-1≤((Nat.dist i j-1 : ℕ) : ℝ) ∧
    (j : ℝ)-i-1≤((Nat.dist i j-1 : ℕ) : ℝ) := by
  have hi : i≤j+1+(Nat.dist i j-1) := by unfold Nat.dist; omega
  have hj : j ≤ i+1+(Nat.dist i j-1) := by unfold Nat.dist; omega
  have hir : (i : ℝ)≤(j : ℝ)+1+((Nat.dist i j-1 : ℕ) : ℝ) := by exact_mod_cast hi
  have hjr : (j : ℝ)≤(i : ℝ)+1+((Nat.dist i j-1 : ℕ) : ℝ) := by exact_mod_cast hj
  constructor <;> linarith only [hir, hjr]

theorem two_direction_cost {N L a i j k l : ℕ}
    (hL : 2≤L) (hN : 2*L+1≤N) (ha : 1≤a) (haL : a≤L)
    (hij : i+j+1=a) (hk : k≤L) (hl : l≤L) (hkl : k+l≤2*(L-1)) :
    let m : ℝ := ((L-1 : ℕ) : ℝ)
    (k : ℝ)*(2*N-2*i-k-3)+(l : ℝ)*(2*N-2*j-l-3)+2*m*(a+m+2)≤
      4*m*N+2*(rankExcess a i : ℝ) := by
  have hi : i+1≤L := by omega
  have hj : j+1≤L := by omega
  have hji : a-1-i=j := by omega
  have haR : (a : ℝ)=(i : ℝ)+j+1 := by exact_mod_cast hij.symm
  have hL1 : ((L-1 : ℕ) : ℝ)=(L : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤L)]
    norm_num
  have hL2 : ((L-2 : ℕ) : ℝ)=(L : ℝ)-2 := by
    rw [Nat.cast_sub hL]
    norm_num
  have hb := distance_excess_bounds i j
  have heq : rankExcess a i=Nat.dist i j-1 := by simp only [rankExcess, hji]
  rw [← heq] at hb
  dsimp only
  by_cases hk2 : k≤L-2
  · have hki := capacity_mono hN hi hk2 (by omega : L-2≤L)
    have hlj := capacity_mono hN hj hl (le_refl L)
    have hbound : rankCapacity N i (L-2)+rankCapacity N j L+
        2*((L-1 : ℕ) : ℝ)*(a+((L-1 : ℕ) : ℝ)+2)≤
        4*((L-1 : ℕ) : ℝ)*N+2*(rankExcess a i : ℝ) := by
      dsimp only [rankCapacity]
      rw [hL1, hL2, haR]
      nlinarith only [hb.1]
    dsimp only [rankCapacity] at hki hlj hbound
    linarith only [hki, hlj, hbound]
  by_cases hkm : k=L-1
  · have hlm : l≤L-1 := by omega
    have hlj := capacity_mono hN hj hlm (by omega : L-1≤L)
    have hbound : rankCapacity N i (L-1)+rankCapacity N j (L-1)+
        2*((L-1 : ℕ) : ℝ)*(a+((L-1 : ℕ) : ℝ)+2)≤
        4*((L-1 : ℕ) : ℝ)*N+2*(rankExcess a i : ℝ) := by
      dsimp only [rankCapacity]
      rw [hL1, haR]
      nlinarith only [Nat.cast_nonneg (α := ℝ) (rankExcess a i)]
    rw [hkm]
    dsimp only [rankCapacity] at hlj hbound
    linarith only [hlj, hbound]
  · have hkL : k=L := by omega
    have hl2 : l≤L-2 := by omega
    have hlj := capacity_mono hN hj hl2 (by omega : L-2≤L)
    have hbound : rankCapacity N i L+rankCapacity N j (L-2)+
        2*((L-1 : ℕ) : ℝ)*(a+((L-1 : ℕ) : ℝ)+2)≤
        4*((L-1 : ℕ) : ℝ)*N+2*(rankExcess a i : ℝ) := by
      dsimp only [rankCapacity]
      rw [hL1, hL2, haR]
      nlinarith only [hb.2]
    rw [hkL]
    dsimp only [rankCapacity] at hlj hbound
    linarith only [hlj, hbound]

#print axioms rank_excess_inner
#print axioms rank_excess_step
#print axioms floor_square_step
#print axioms rank_excess_sum
#print axioms capacity_mono
#print axioms distance_excess_bounds
#print axioms two_direction_cost
end JSP233.SmallRankScalars84364
