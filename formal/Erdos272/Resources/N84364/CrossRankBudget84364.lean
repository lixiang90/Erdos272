module

public import Erdos272.Resources.N84364.FirstHitBudget84364

@[expose] public section

namespace JSP233.CrossRankBudget84364
open StarCompletion SparseSmall39 FirstHitCapacity84364 FirstHitBudget84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_cross_hit_budget {Ω D A B : Finset ℤ} {H : Finset (Finset ℤ)}
    (hlegal : Legal Ω H) (hbad : ∀ S ∈ H, ¬IsAP S)
    (hD : D⊆Ω) (hA : A⊆Ω) (hB : B⊆Ω)
    (hAB : Disjoint A B) (hDA : Disjoint D A) (hDB : Disjoint D B)
    (havoid : ∀ S ∈ H, Disjoint S D)
    (hhitA : ∀ S ∈ H, (S∩A).Nonempty) (hhitB : ∀ S ∈ H, (S∩B).Nonempty) :
    H.card+A.card*B.card*(D.card+2)+B.card*A.card.choose 2+A.card*B.card.choose 2
      ≤A.card*B.card*Ω.card := by
  have hb : ∀ x ∈ A, (HitBucket H A x).card+
      B.card*(D.card+(Earlier A x).card+2)+B.card.choose 2≤B.card*Ω.card := by
    intro x hx
    let C := HitBucket H A x
    let R := D∪Earlier A x
    have hCF : C⊆H := Finset.filter_subset _ _
    have hLC : Legal Ω C := ⟨fun S hS => hlegal.1 S (hCF hS),
      fun S hS T hT hne => hlegal.2 S (hCF hS) T (hCF hT) hne⟩
    have hER : Earlier A x⊆A := Finset.filter_subset _ _
    have hRsub : R⊆Ω := Finset.union_subset hD (hER.trans hA)
    have hxR : x∉R := by
      intro hh
      rcases Finset.mem_union.mp hh with hxD | hxE
      · exact Finset.disjoint_left.mp hDA hxD hx
      · have hxx := (Finset.mem_filter.mp hxE).2
        omega
    have hxB : x∉B := fun hh => Finset.disjoint_left.mp hAB hx hh
    have hRB : Disjoint R B := by
      apply Finset.disjoint_left.mpr
      intro y hyR hyB
      rcases Finset.mem_union.mp hyR with hyD | hyE
      · exact Finset.disjoint_left.mp hDB hyD hyB
      · exact Finset.disjoint_left.mp hAB (hER hyE) hyB
    have hroot : ∀ S ∈ C, x∈S := fun S hS =>
      (Finset.mem_inter.mp (hit_bucket_spec hhitA hS).1).1
    have havoidR : ∀ S ∈ C, Disjoint S R := by
      intro S hS
      exact Finset.disjoint_union_right.mpr
        ⟨havoid S (hCF hS), (hit_bucket_spec hhitA hS).2⟩
    have hRc : R.card=D.card+(Earlier A x).card :=
      Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hER hDA)
    have hh := actual_root_hit_budget hLC (fun S hS => hbad S (hCF hS))
      (hA hx) hRsub hB hxR hxB hRB hroot havoidR (fun S hS => hhitB S (hCF hS))
    simpa only [hRc] using hh
  have hmaps : ∀ S ∈ H, Hit A S∈A := by
    intro S hS
    exact (Finset.mem_inter.mp (hit_spec (hhitA S hS)).1).2
  have hf : H.card=∑ x ∈ A, (HitBucket H A x).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hr : (∑ x ∈ A, (Earlier A x).card)=A.card.choose 2 := by
    rw [sum_earlier_function A (fun i => i), Finset.sum_range_id, ← Nat.choose_two_right]
  have hs := Finset.sum_le_sum hb
  simp only [Nat.mul_add, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  rw [← hf, ← Finset.mul_sum, hr] at hs
  nlinarith only [hs]

#print axioms actual_cross_hit_budget
end
end JSP233.CrossRankBudget84364
