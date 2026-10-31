import Erdos272.Resources.SourceCertified208

/-! The selected unit-source layers pay the original family's actual pool.
This interface deliberately retains that sum so APJoint208 can reserve AP
triples and combine the two terms for the same original family. -/
namespace JSP233.SourceFees208
open StarCompletion IntrinsicTriples208 SourceBridge208 SourceCertified208
open SourcePrefixSpecs208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_selected_resource (i : Fin 14) (nodes : ℕ → ℕ)
    (hnodes : Monotone nodes) (hzero : nodes 0 = 0) (n : ℕ)
    (A : Finset (Finset ℤ)) (fee : ℕ → ℝ)
    (hs : ∀ S ∈ A, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range n, ((selectedNear A nodes j).card : ℝ) ≤ fee j) :
    potential i (nodes n) * A.card ≤ (∑ S ∈ A, ((Pool S).card : ℝ)) +
      ∑ j ∈ Finset.range n,
        (potential i (nodes (j+1)) - potential i (nodes j)) * fee j := by
  have h := LayerPayment208.fractional_cover A (Finset.range n) (selectedNear A nodes)
    (fun S => ((Pool S).card : ℝ))
    (fun j => potential i (nodes (j+1)) - potential i (nodes j))
    (potential i (nodes n))
    (fun j _ => Finset.filter_subset _ A)
    (fun S hS => by
      simpa only [selectedNear, Finset.mem_filter, hS, true_and] using
        actual_selected_cover i nodes hnodes hzero n (hs S hS).1 (hs S hS).2)
  have hf : (∑ j ∈ Finset.range n,
      (potential i (nodes (j+1)) - potential i (nodes j)) *
        ((selectedNear A nodes j).card : ℝ)) ≤
      ∑ j ∈ Finset.range n,
        (potential i (nodes (j+1)) - potential i (nodes j)) * fee j := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (hfee j hj)
      (sub_nonneg.mpr (potential_monotone i (hnodes (Nat.le_succ j))))
  linarith only [h, hf]

theorem pool_sum_subset {A F : Finset (Finset ℤ)} (hAF : A ⊆ F) :
    (∑ S ∈ A, ((Pool S).card : ℝ)) ≤ ∑ S ∈ F, ((Pool S).card : ℝ) := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hAF
  intro S _ _
  positivity

/-- The scalar relation is exact: the source coefficient is the reciprocal
of the terminal checked potential, with the convention used by APJoint208. -/
theorem actual_selected_original_pool (i : Fin 14) (nodes : ℕ → ℕ)
    (hnodes : Monotone nodes) (hzero : nodes 0 = 0) (n : ℕ)
    {A F : Finset (Finset ℤ)} (fee : ℕ → ℝ) (g : ℝ)
    (hAF : A ⊆ F) (hg : 0 ≤ g) (hgp : 6*g*potential i (nodes n) = 1)
    (hs : ∀ S ∈ A, rowStart i ≤ S.card ∧ S.card < 2^50)
    (hfee : ∀ j ∈ Finset.range n, ((selectedNear A nodes j).card : ℝ) ≤ fee j) :
    (A.card : ℝ) ≤ 6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) +
      6*g*∑ j ∈ Finset.range n,
        (potential i (nodes (j+1)) - potential i (nodes j)) * fee j := by
  have h := actual_selected_resource i nodes hnodes hzero n A fee hs hfee
  have hm := pool_sum_subset hAF
  have hscaled := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 6*g)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 6*g)
  rw [← mul_assoc, hgp, one_mul, mul_add] at hscaled
  linarith only [hscaled, hm']

#print axioms actual_selected_resource
#print axioms actual_selected_original_pool
end
end JSP233.SourceFees208
