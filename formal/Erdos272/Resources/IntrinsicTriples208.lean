import Erdos272.Foundation.StarCompletion
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! # The actual intrinsic triple resource

The resource is a finite set of three element subsets of the actual source.
A triple is intrinsic precisely when no arithmetic progression contained in
that source covers it. Legal intersections make every such triple private.
Consequently all sources share one pool of size `choose |Ω| 3`.

The number theoretic lower bound on each source is deliberately separate
from this geometric capacity statement.
-/
namespace JSP233.IntrinsicTriples208
open StarCompletion
open scoped Classical BigOperators
noncomputable section

def Pool (S : Finset ℤ) : Finset (Finset ℤ) :=
  (S.powersetCard 3).filter fun Q =>
    ¬ ∃ P : Finset ℤ, IsAP P ∧ Q ⊆ P ∧ P ⊆ S

theorem mem_pool {S Q : Finset ℤ} :
    Q ∈ Pool S ↔ Q ⊆ S ∧ Q.card = 3 ∧
      ¬ ∃ P : Finset ℤ, IsAP P ∧ Q ⊆ P ∧ P ⊆ S := by
  simp only [Pool, Finset.mem_filter, Finset.mem_powersetCard, and_assoc]

theorem pool_private {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {S T Q : Finset ℤ} (hS : S ∈ F) (hT : T ∈ F)
    (hQ : Q ∈ Pool S) (hQT : Q ⊆ T) : S = T := by
  by_contra hne
  obtain ⟨hQS, _, hno⟩ := mem_pool.mp hQ
  apply hno
  exact ⟨S ∩ T, hF.2 S hS T hT hne,
    Finset.subset_inter hQS hQT, Finset.inter_subset_left⟩

theorem pools_pairwise_disjoint {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) : (F : Set (Finset ℤ)).PairwiseDisjoint Pool := by
  intro S hS T hT hne
  apply Finset.disjoint_left.mpr
  intro Q hQS hQT
  exact hne (pool_private hF hS hT hQS (mem_pool.mp hQT).1)

theorem union_subset_triples {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : ∀ S ∈ F, S ⊆ Ω) : F.biUnion Pool ⊆ Ω.powersetCard 3 := by
  intro Q hQ
  obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
  obtain ⟨hsub, hcard, _⟩ := mem_pool.mp hQS
  exact Finset.mem_powersetCard.mpr ⟨hsub.trans (hF S hS), hcard⟩

/-- Every actual intrinsic triple is paid at most once across the family. -/
theorem actual_capacity {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) : (∑ S ∈ F, (Pool S).card) ≤ Ω.card.choose 3 := by
  calc
    (∑ S ∈ F, (Pool S).card) = (F.biUnion Pool).card :=
      (Finset.card_biUnion (pools_pairwise_disjoint hF)).symm
    _ ≤ (Ω.powersetCard 3).card := Finset.card_le_card (union_subset_triples hF.1)
    _ = Ω.card.choose 3 := Finset.card_powersetCard 3 Ω

/-- An actual AP member reserves all of its internal triples from the same
global resource, including against sources other than itself. -/
theorem disjoint_actual_AP {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {P : Finset ℤ} (hP : P ∈ F) (hAP : IsAP P) :
    Disjoint (F.biUnion Pool) (P.powersetCard 3) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hQP
  obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
  have hsub : Q ⊆ P := (Finset.mem_powersetCard.mp hQP).1
  have hSP : S = P := pool_private hF hS hP hQS hsub
  exact (mem_pool.mp hQS).2.2 ⟨P, hAP, hsub, by rw [hSP]⟩

/-- The AP reservation and all intrinsic source pools are paid jointly. -/
theorem actual_capacity_with_AP {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {P : Finset ℤ} (hP : P ∈ F) (hAP : IsAP P) :
    (∑ S ∈ F, (Pool S).card) + P.card.choose 3 ≤ Ω.card.choose 3 := by
  have hPsub : P.powersetCard 3 ⊆ Ω.powersetCard 3 := by
    intro Q hQ
    obtain ⟨hQP, hcard⟩ := Finset.mem_powersetCard.mp hQ
    exact Finset.mem_powersetCard.mpr ⟨hQP.trans (hF.1 P hP), hcard⟩
  have hsub : F.biUnion Pool ∪ P.powersetCard 3 ⊆ Ω.powersetCard 3 :=
    Finset.union_subset (union_subset_triples hF.1) hPsub
  calc
    (∑ S ∈ F, (Pool S).card) + P.card.choose 3 =
        (F.biUnion Pool).card + (P.powersetCard 3).card := by
      rw [Finset.card_biUnion (pools_pairwise_disjoint hF), Finset.card_powersetCard]
    _ = (F.biUnion Pool ∪ P.powersetCard 3).card :=
      (Finset.card_union_of_disjoint (disjoint_actual_AP hF hP hAP)).symm
    _ ≤ (Ω.powersetCard 3).card := Finset.card_le_card hsub
    _ = Ω.card.choose 3 := Finset.card_powersetCard 3 Ω

theorem actual_residual_capacity {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {P : Finset ℤ} (hP : P ∈ F) (hAP : IsAP P) :
    (∑ S ∈ F, (Pool S).card) ≤ Ω.card.choose 3 - P.card.choose 3 := by
  have h := actual_capacity_with_AP hF hP hAP
  omega

/-- A uniform lower mass gives an actual source count, without introducing
an independent copy of the triple pool for each source. -/
theorem actual_count_of_mass {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {b : ℕ} (hb : ∀ S ∈ F, b ≤ (Pool S).card) :
    b * F.card ≤ Ω.card.choose 3 := by
  calc
    b * F.card = ∑ _S ∈ F, b := by simp [Nat.mul_comm]
    _ ≤ ∑ S ∈ F, (Pool S).card := Finset.sum_le_sum hb
    _ ≤ Ω.card.choose 3 := actual_capacity hF

/-- The same global pool supports distinct lower masses for different
physical source sizes and defects. -/
theorem actual_variable_mass {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) (b : Finset ℤ → ℕ)
    (hb : ∀ S ∈ F, b S ≤ (Pool S).card) :
    (∑ S ∈ F, b S) ≤ Ω.card.choose 3 :=
  (Finset.sum_le_sum hb).trans (actual_capacity hF)

#print axioms pool_private
#print axioms pools_pairwise_disjoint
#print axioms actual_capacity
#print axioms disjoint_actual_AP
#print axioms actual_capacity_with_AP
#print axioms actual_residual_capacity
#print axioms actual_count_of_mass
#print axioms actual_variable_mass
end
end JSP233.IntrinsicTriples208
