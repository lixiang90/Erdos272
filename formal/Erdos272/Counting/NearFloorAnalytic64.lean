module

public import Erdos272.Core.NearFloor63
public import Erdos272.Counting.EndpointDensity54
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.NearFloorAnalytic64
open NearFloor63 HarmonicAbel29 CoprimeDensity52 StarCompletion APGeometry NearAP36
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem reciprocal_square_tail_two (X : ℕ) :
    (∑ j ∈ Finset.Icc 2 X, ((j:ℝ)^2)⁻¹) ≤ 129/200 := by
  by_cases hX : 1≤X
  · have hs := EndpointDensity54.reciprocal_square_upper X
    have he : reciprocalSquareSum X = 1+∑j∈Finset.Icc 2 X,((j:ℝ)^2)⁻¹ := by
      unfold reciprocalSquareSum
      have hset : Finset.Icc 1 X=insert 1 (Finset.Icc 2 X) := by
        ext j
        simp only [Finset.mem_Icc,Finset.mem_insert]
        omega
      rw [hset,Finset.sum_insert (by norm_num)]
      norm_num
    linarith only [hs,he]
  · have he : Finset.Icc 2 X=∅ := by apply Finset.Icc_eq_empty_of_lt;omega
    rw [he]
    norm_num

theorem reciprocal_tail_two_le_harmonic (N K : ℕ) :
    (∑j∈Finset.Icc 2 (N/K),(1:ℝ)/j)≤Harmonic N := by
  unfold Harmonic
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro j hj
    obtain ⟨hj1,hj2⟩:=Finset.mem_Icc.mp hj
    exact Finset.mem_Icc.mpr ⟨by omega,hj2.trans (Nat.div_le_self _ _)⟩
  · intro j _ _
    positivity

theorem floor_triangle_pointwise {N K j : ℕ} (hK : 0<K) (hj : 0<j) :
    (K:ℝ)*((N/(K*j):ℕ):ℝ)*(((N/(K*j):ℕ):ℝ)+1)≤
      (N:ℝ)^2/K*((j:ℝ)^2)⁻¹+(N:ℝ)*((1:ℝ)/j) := by
  have hkR : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hjR : (0:ℝ)<j := Nat.cast_pos.mpr hj
  have hq := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=K*j)
  push_cast at hq
  have hy : (0:ℝ)≤(N:ℝ)/((K:ℝ)*j) := by positivity
  have hnon : (0:ℝ)≤((N/(K*j):ℕ):ℝ) := Nat.cast_nonneg _
  have hsq : ((N/(K*j):ℕ):ℝ)*(((N/(K*j):ℕ):ℝ)+1)≤
      ((N:ℝ)/((K:ℝ)*j))^2+(N:ℝ)/((K:ℝ)*j) := by
    nlinarith only [hq,hy,hnon,sq_nonneg ((N:ℝ)/((K:ℝ)*j)-((N/(K*j):ℕ):ℝ))]
  have hh := mul_le_mul_of_nonneg_left hsq hkR.le
  calc
    _≤(K:ℝ)*(((N:ℝ)/((K:ℝ)*j))^2+(N:ℝ)/((K:ℝ)*j)) := by nlinarith only [hh]
    _=_ := by field_simp

theorem floor_triangle_sum_analytic {N K : ℕ} (hK : 0<K) :
    (K:ℝ)*(∑j∈Finset.Icc 2 (N/K),
      ((N/(K*j):ℕ):ℝ)*(((N/(K*j):ℕ):ℝ)+1))≤
      (129/200:ℝ)*(N:ℝ)^2/K+(N:ℝ)*Harmonic N := by
  have hp : (K:ℝ)*(∑j∈Finset.Icc 2 (N/K),
      ((N/(K*j):ℕ):ℝ)*(((N/(K*j):ℕ):ℝ)+1))≤
      ∑j∈Finset.Icc 2 (N/K),((N:ℝ)^2/K*((j:ℝ)^2)⁻¹+(N:ℝ)*((1:ℝ)/j)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hjp : 0<j := by have hh:=Finset.mem_Icc.mp hj;omega
    simpa only [mul_assoc] using floor_triangle_pointwise hK hjp
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum] at hp
  have hs := mul_le_mul_of_nonneg_left (reciprocal_square_tail_two (N/K))
    (by positivity : (0:ℝ)≤(N:ℝ)^2/K)
  have hh := mul_le_mul_of_nonneg_left (reciprocal_tail_two_le_harmonic N K)
    (Nat.cast_nonneg N : (0:ℝ)≤N)
  calc
    _≤(N:ℝ)^2/K*(∑j∈Finset.Icc 2 (N/K),((j:ℝ)^2)⁻¹)+
      (N:ℝ)*(∑j∈Finset.Icc 2 (N/K),(1:ℝ)/j) := hp
    _≤(N:ℝ)^2/K*(129/200)+(N:ℝ)*Harmonic N := add_le_add hs hh
    _=_ := by ring

theorem actual_floor_quadratic_budget {N K : ℕ} (hK : 0<K) :
    ((N/(2*K):ℕ):ℝ)*N+(K:ℝ)*
      ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)≤
      (329/400:ℝ)*(N:ℝ)^2/K+(1/2:ℝ)*N*Harmonic N := by
  have hswap := actual_near_floor_swap N K 2 (by decide)
  have hswapR : 2*((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)=
      ∑j∈Finset.Icc 2 (N/K),((N/(K*j):ℕ):ℝ)*(((N/(K*j):ℕ):ℝ)+1) := by
    exact_mod_cast hswap
  have hs := floor_triangle_sum_analytic (N:=N) hK
  have hd := Nat.cast_div_le (α:=ℝ) (m:=N) (n:=2*K)
  push_cast at hd
  have hmul:=mul_le_mul_of_nonneg_right hd (Nat.cast_nonneg N : (0:ℝ)≤N)
  have he : (N:ℝ)/(2*K)*N=(1/2:ℝ)*(N:ℝ)^2/K := by ring
  rw [he] at hmul
  rw [←hswapR] at hs
  have hhalf : (K:ℝ)*
      ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)≤
      (129/400:ℝ)*(N:ℝ)^2/K+(1/2:ℝ)*N*Harmonic N := by
    linear_combination hs/2
  calc
    _≤(1/2:ℝ)*(N:ℝ)^2/K+
      ((129/400:ℝ)*(N:ℝ)^2/K+(1/2:ℝ)*N*Harmonic N) := add_le_add hmul hhalf
    _=_ := by ring

theorem actual_near_members_quadratic_budget {N K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hbad : ∀S∈F,¬IsAP S) (hlow : ∀S∈F,3*K+1≤S.card)
    (hhigh : ∀S∈F,S.card≤6*K) :
    ((NearMembers K F).card:ℝ)≤
      (2303/400:ℝ)*(N:ℝ)^2/K+(7/2:ℝ)*N*Harmonic N := by
  have hf := actual_near_members_floor_budget (A:=2) (b:=6) hlegal hK (by decide)
    hbad (by simpa using hlow) hhigh
  have hfR : ((NearMembers K F).card:ℝ)≤7*
      (((N/(2*K):ℕ):ℝ)*N+(K:ℝ)*
        ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)) := by exact_mod_cast hf
  have hq := actual_floor_quadratic_budget (N:=N) hK
  calc
    _≤7*(((N/(2*K):ℕ):ℝ)*N+(K:ℝ)*
        ((∑d∈Finset.Icc 1 (N/(2*K)),d*(N/(K*d)+1-2):ℕ):ℝ)) := hfR
    _≤7*((329/400:ℝ)*(N:ℝ)^2/K+(1/2:ℝ)*N*Harmonic N) :=
      mul_le_mul_of_nonneg_left hq (by norm_num)
    _=_ := by ring

#print axioms reciprocal_square_tail_two
#print axioms reciprocal_tail_two_le_harmonic
#print axioms floor_triangle_pointwise
#print axioms floor_triangle_sum_analytic
#print axioms actual_floor_quadratic_budget
#print axioms actual_near_members_quadratic_budget
end
end JSP233.NearFloorAnalytic64
