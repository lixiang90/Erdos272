module

public import Erdos272.Resources.N80470.WitnessActualLayer80470
public import Erdos272.Resources.SevenFamily208

@[expose] public section

namespace JSP233.WitnessSourcePayment80470
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208 SevenFamily208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Weighted (g : ℝ) (psi : ℕ → ℝ) (cap : ℕ) (cost : ℕ → ℝ) : ℝ :=
  6*g*(∑ i ∈ Finset.range cap, (psi (i+1)-psi i)*cost i)

theorem actual_source_of_obligation {N W : ℕ} {A F : Finset (Finset ℤ)}
    {A₀ : Finset ℤ} {g a b c : ℝ}
    (hlegal : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F)
    (hW : A₀.card ≤ W) (hg : 0 ≤ g)
    (hfee : Legal (Ground N) F → A ⊆ F → A₀ ∈ F → A₀.card ≤ W →
      UnitNearObligation N A g a b c) :
    (A.card : ℝ) ≤ 6*g*(∑ S ∈ F, ((Pool S).card : ℝ))+a*(N : ℝ)^2+b*N+c := by
  exact SevenFamily208.actual_unit_source hAF hg (hfee hlegal hAF hA₀ hW)

theorem actual_source_of_levels {N W cap : ℕ} {A F : Finset (Finset ℤ)}
    {A₀ : Finset ℤ} {g : ℝ} {psi : ℕ → ℝ} {cost : ℕ → ℝ}
    (hlegal : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F)
    (hW : A₀.card ≤ W) (hg : 0 ≤ g) (hmono : Monotone psi) (hzero : psi 0=0)
    (hreciprocal : 6*g*psi cap=1)
    (hlevels : Legal (Ground N) F → A ⊆ F → A₀ ∈ F → A₀.card ≤ W →
      ∀ i ∈ Finset.range cap, ((PoolNear A psi i).card : ℝ) ≤ cost i) :
    (A.card : ℝ) ≤ 6*g*(∑ S ∈ F, ((Pool S).card : ℝ))+Weighted g psi cap cost := by
  have hs : (∑ i ∈ Finset.range cap,
      (psi (i+1)-psi i)*((PoolNear A psi i).card : ℝ)) ≤
      ∑ i ∈ Finset.range cap, (psi (i+1)-psi i)*cost i := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hlevels hlegal hAF hA₀ hW i hi)
      (sub_nonneg.mpr (hmono (Nat.le_succ i)))
  have ho : UnitNearObligation N A g 0 0 (Weighted g psi cap cost) := by
    refine ⟨psi,cap,hmono,hzero,hreciprocal,?_⟩
    simpa only [zero_mul,zero_add,Weighted] using
      mul_le_mul_of_nonneg_left hs (show 0 ≤ 6*g by positivity)
  simpa only [zero_mul,add_zero,zero_add] using SevenFamily208.actual_unit_source hAF hg ho

theorem actual_source_of_fee {N W cap : ℕ} {A F : Finset (Finset ℤ)}
    {A₀ : Finset ℤ} {g : ℝ} {psi : ℕ → ℝ} {cost : ℕ → ℝ} {a b c : ℝ}
    (hlegal : Legal (Ground N) F) (hAF : A ⊆ F) (hA₀ : A₀ ∈ F)
    (hW : A₀.card ≤ W) (hg : 0 ≤ g) (hmono : Monotone psi) (hzero : psi 0=0)
    (hreciprocal : 6*g*psi cap=1)
    (hlevels : Legal (Ground N) F → A ⊆ F → A₀ ∈ F → A₀.card ≤ W →
      ∀ i ∈ Finset.range cap, ((PoolNear A psi i).card : ℝ) ≤ cost i)
    (hfee : Weighted g psi cap cost=a*(N : ℝ)^2+b*N+c) :
    (A.card : ℝ) ≤ 6*g*(∑ S ∈ F, ((Pool S).card : ℝ))+a*(N : ℝ)^2+b*N+c := by
  have hh := actual_source_of_levels hlegal hAF hA₀ hW hg hmono hzero hreciprocal hlevels
  rw [hfee] at hh
  simpa only [add_assoc] using hh

#print axioms actual_source_of_obligation
#print axioms actual_source_of_levels
#print axioms actual_source_of_fee
end
end JSP233.WitnessSourcePayment80470
