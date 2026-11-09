module

public import Erdos272.Resources.IntrinsicTriples208
public import Erdos272.Arithmetic.TriangularWeights208
public import Erdos272.Foundation.JSP233
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! The actual weighted physical slot pool is shared by all rank distances.
No per-source supply estimate is assumed in this global capacity theorem. -/
namespace JSP233.NeighborSlots208
open StarCompletion IntrinsicTriples208 TriangularWeights208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Slots (N : ℕ) (S : Finset ℤ) : Finset (Σ _ : ℕ, ℤ × ℤ) :=
  (Finset.Icc 1 (N - 1)).sigma fun d => (S.product S).filter fun p =>
    p.1 + (d : ℤ) ∈ S ∧ ({p.1, p.1 + (d : ℤ), p.2} : Finset ℤ) ∈ Pool S

def Physical (N : ℕ) : Finset (Σ _ : ℕ, ℤ × ℤ) :=
  (Finset.Icc 1 (N - 1)).sigma fun _ => (Ground N).product (Ground N)

def Mass (N : ℕ) (u : ℝ) (S : Finset ℤ) : ℝ :=
  ∑ p ∈ Slots N S, Weight u p.1

theorem slots_pairwise_disjoint {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) : (F : Set (Finset ℤ)).PairwiseDisjoint (Slots N) := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro p hpS hpT
  have hs := (Finset.mem_filter.mp (Finset.mem_sigma.mp hpS).2).2.2
  have ht := (Finset.mem_filter.mp (Finset.mem_sigma.mp hpT).2).2.2
  exact hne (pool_private hF hS hT hs (mem_pool.mp ht).1)

theorem slots_subset_physical {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) : F.biUnion (Slots N) ⊆ Physical N := by
  intro p hp
  obtain ⟨S, hS, hpS⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hd, hpair⟩ := Finset.mem_sigma.mp hpS
  obtain ⟨hpair, _⟩ := Finset.mem_filter.mp hpair
  obtain ⟨ha, hx⟩ := Finset.mem_product.mp hpair
  exact Finset.mem_sigma.mpr ⟨hd, Finset.mem_product.mpr ⟨hF.1 S hS ha, hF.1 S hS hx⟩⟩

theorem physical_weight (N : ℕ) (u : ℝ) :
    (∑ p ∈ Physical N, Weight u p.1) =
      (N : ℝ)^2 * ∑ d ∈ Finset.Icc 1 (N - 1), Weight u d := by
  simp only [Physical, Finset.sum_sigma, Finset.sum_const, nsmul_eq_mul,
    Finset.product_eq_sprod, Finset.card_product, ground_card, Nat.cast_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem actual_capacity_raw {N : ℕ} {F : Finset (Finset ℤ)} (u : ℝ)
    (hF : Legal (Ground N) F) :
    (∑ S ∈ F, Mass N u S) ≤ (N : ℝ)^2 * ∑ d ∈ Finset.Icc 1 (N - 1), Weight u d := by
  have hsub := slots_subset_physical hF
  calc
    _ = ∑ p ∈ F.biUnion (Slots N), Weight u p.1 :=
      (Finset.sum_biUnion (slots_pairwise_disjoint hF)).symm
    _ ≤ ∑ p ∈ Physical N, Weight u p.1 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp hnot
      exact weight_nonneg _ _
    _ = _ := physical_weight N u

theorem actual_capacity {N : ℕ} {F : Finset (Finset ℤ)} {t : ℝ}
    (hN : 2 ≤ N) (ht : 0 < t) (hF : Legal (Ground N) F) :
    (∑ S ∈ F, Mass N (t / ((N : ℝ) - 1)) S) ≤
      (N : ℝ)^2 * (N - 1) / (2 * t) := by
  have hNp : (0 : ℝ) < (N : ℝ) - 1 := by
    have hh : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith only [hh]
  have hu : 0 < t / ((N : ℝ) - 1) := div_pos ht hNp
  have hw := mul_le_mul_of_nonneg_left (weight_sum_bound hu (N - 1)) (sq_nonneg (N : ℝ))
  apply (actual_capacity_raw _ hF).trans
  convert hw using 1
  field_simp

#print axioms slots_pairwise_disjoint
#print axioms actual_capacity_raw
#print axioms actual_capacity
end
end JSP233.NeighborSlots208
