module

public import Erdos272.Resources.N84364.FirstHitBudget84364
public import Erdos272.Counting.N84364.KeysOrder84364

@[expose] public section

namespace JSP233.KeysRankBudget84364
open StarCompletion SparseSmall39 SharpSmall212 KeysOrder84364 FirstHitBudget84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_keys_bucket_budget {N : ℕ} {F : Finset (Finset ℤ)} {A T : Finset ℤ}
    {x : ℤ} (hlegal : Legal (Ground N) F) (hbad : ∀ S ∈ F, ¬IsAP S)
    (hA : A∈F) (hT : T∈F) (hxA : x∈A) (hxT : x∉T) (upper : Bool) :
    (Bucket F A x upper).card+(Keys A T x upper).card*((Before A x upper).card+2)+
      (Keys A T x upper).card.choose 2≤(Keys A T x upper).card*N := by
  let C := Bucket F A x upper
  let K := Keys A T x upper
  let D := Before A x upper
  have hCF : C⊆F := Finset.filter_subset _ _
  have hLC : Legal (Ground N) C := ⟨fun S hS => hlegal.1 S (hCF hS),
    fun S hS U hU hne => hlegal.2 S (hCF hS) U (hCF hU) hne⟩
  have hDsub : D⊆Ground N := (Finset.filter_subset _ _).trans (hlegal.1 A hA)
  have hKsub : K⊆Ground N := (Finset.filter_subset _ _).trans (hlegal.1 T hT)
  have hself : Order upper x x := by cases upper <;> simp [Order]
  have hxD : x∉D := fun hh => (Finset.mem_filter.mp hh).2 hself
  have hxK : x∉K := fun hh => hxT (Finset.mem_filter.mp hh).1
  have hDK : Disjoint D K := by
    apply Finset.disjoint_left.mpr
    intro y hyD hyK
    obtain ⟨hyA, hyNot⟩ := Finset.mem_filter.mp hyD
    obtain ⟨hyT, hyKey⟩ := Finset.mem_filter.mp hyK
    rcases hyKey with hyOut | hyOrder
    · exact hyOut hyA
    · exact hyNot hyOrder
  have hroot : ∀ S ∈ C, x∈S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have havoid : ∀ S ∈ C, Disjoint S D := by
    intro S hS
    have hmin := (Finset.mem_filter.mp hS).2.2
    apply Finset.disjoint_left.mpr
    intro y hyS hyD
    obtain ⟨hyA, hyNot⟩ := Finset.mem_filter.mp hyD
    exact hyNot (hmin y hyS hyA)
  have hhit : ∀ S ∈ C, (S∩K).Nonempty := by
    intro S hS
    obtain ⟨hSF, hxS, hmin⟩ := Finset.mem_filter.mp hS
    have hne : S≠T := by intro he; exact hxT (he ▸ hxS)
    obtain ⟨y, hy⟩ := isAP_nonempty (hlegal.2 S hSF T hT hne)
    obtain ⟨hyS, hyT⟩ := Finset.mem_inter.mp hy
    refine ⟨y, Finset.mem_inter.mpr ⟨hyS, ?_⟩⟩
    apply Finset.mem_filter.mpr
    refine ⟨hyT, ?_⟩
    by_cases hyA : y∈A
    · exact Or.inr (hmin y hyS hyA)
    · exact Or.inl hyA
  have hh := actual_root_hit_budget hLC (fun S hS => hbad S (hCF hS))
    (hlegal.1 A hA hxA) hDsub hKsub hxD hxK hDK hroot havoid hhit
  simpa only [ground_card] using hh

#print axioms actual_keys_bucket_budget
end
end JSP233.KeysRankBudget84364
