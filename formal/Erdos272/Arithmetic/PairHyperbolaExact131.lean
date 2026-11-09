module

public import Erdos272.Arithmetic.PairHyperbola131
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.Order.Floor.Semifield

@[expose] public section

namespace JSP233.PairHyperbolaExact131
open SimplexMoment57 DivisorMoment45 ParityPool123 PairHyperbola131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem pair_union_eq_strict {N M : ℕ} (hN : N<(M+1)^2) :
    PairLeft N M∪PairRight N M=QuadPool N := by
  ext z
  simp only [PairLeft,PairRight,Finset.mem_union,Finset.mem_filter]
  constructor
  · tauto
  · intro hz
    by_cases hL : firstProduct z≤M
    · exact Or.inl ⟨hz,hL⟩
    · refine Or.inr ⟨hz,?_⟩
      by_contra hR
      have h1 : M+1≤firstProduct z := by omega
      have h2 : M+1≤secondProduct z := by omega
      have hmul := Nat.mul_le_mul h1 h2
      have hprod := (mem_quad_pool.mp hz).2.2.2.2
      dsimp only [firstProduct,secondProduct] at hmul
      nlinarith only [hN,hmul,hprod]

theorem actual_pair_hyperbola_upper_strict {N M K : ℕ}
    (hKM : K≤M) (hK : K^2≤N) (hN : N<(M+1)^2) :
    DivCount 3 N+T K^2≤2*Z N M := by
  have he := Finset.card_union_add_card_inter (PairLeft N M) (PairRight N M)
  have hi := pair_inter_card_lower hKM hK
  rw [pair_union_eq_strict hN,quad_pool_eq_div_count,pair_left_card,pair_right_card] at he
  omega

theorem actual_pair_hyperbola_exact_nat {N M : ℕ}
    (hM : M^2≤N) (hN : N<(M+1)^2) :
    DivCount 3 N+T M^2=2*Z N M := by
  have hl := actual_pair_hyperbola_lower N M
  have hu := actual_pair_hyperbola_upper_strict (le_refl M) hM hN
  omega

theorem actual_pair_hyperbola_exact_sqrt (N : ℕ) :
    DivCount 3 N+T (Nat.sqrt N)^2=2*Z N (Nat.sqrt N) := by
  exact actual_pair_hyperbola_exact_nat (Nat.sqrt_le' N) (by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' N)

theorem actual_pair_hyperbola_upper_strict_real {N M K : ℕ}
    (hKM : K≤M) (hK : K^2≤N) (hN : N<(M+1)^2) :
    (DivCount 3 N:ℝ)≤
      2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (N/a):ℝ))-
        (DivCount 1 K:ℝ)^2 := by
  have h : (DivCount 3 N:ℝ)+(T K:ℝ)^2≤2*(Z N M:ℝ) := by
    exact_mod_cast actual_pair_hyperbola_upper_strict hKM hK hN
  dsimp only [Z,T] at h
  push_cast at h
  linarith only [h]

theorem actual_pair_hyperbola_lower_floor (x : ℝ) (M : ℕ) :
    2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ))-
      (DivCount 1 M:ℝ)^2≤(DivCount 3 (Nat.floor x):ℝ) := by
  simpa only [Nat.floor_div_natCast] using actual_pair_hyperbola_lower_real (Nat.floor x) M

theorem actual_pair_hyperbola_upper_floor {x : ℝ} (hx : 0≤x) {M K : ℕ}
    (hKM : K≤M) (hK : (K:ℝ)^2≤x) (hN : x≤(M:ℝ)^2) :
    (DivCount 3 (Nat.floor x):ℝ)≤
      2*(∑a∈Finset.Icc 1 M,(a.divisors.card:ℝ)*(DivCount 1 (Nat.floor (x/(a:ℝ))):ℝ))-
        (DivCount 1 K:ℝ)^2 := by
  have hKNat : K^2≤Nat.floor x := (Nat.le_floor_iff hx).mpr (by exact_mod_cast hK)
  have hNNat : Nat.floor x≤M^2 := Nat.floor_le_of_le (by exact_mod_cast hN)
  simpa only [Nat.floor_div_natCast] using actual_pair_hyperbola_upper_real hKM hKNat hNNat

#print axioms pair_union_eq_strict
#print axioms actual_pair_hyperbola_upper_strict
#print axioms actual_pair_hyperbola_exact_nat
#print axioms actual_pair_hyperbola_exact_sqrt
#print axioms actual_pair_hyperbola_upper_strict_real
#print axioms actual_pair_hyperbola_lower_floor
#print axioms actual_pair_hyperbola_upper_floor
end
end JSP233.PairHyperbolaExact131
