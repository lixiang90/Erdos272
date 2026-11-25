module

public import Erdos272.Capacity.N84364.FirstHitCapacity84364

@[expose] public section

namespace JSP233.FirstHitBudget84364
open StarCompletion SparseSmall39 FirstHitCapacity84364
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_root_hit_budget {Ω D T : Finset ℤ} {H : Finset (Finset ℤ)} {u : ℤ}
    (hlegal : Legal Ω H) (hbad : ∀ S ∈ H, ¬IsAP S)
    (hu : u∈Ω) (hD : D⊆Ω) (hT : T⊆Ω)
    (huD : u∉D) (huT : u∉T) (hDT : Disjoint D T)
    (hroot : ∀ S ∈ H, u∈S) (havoid : ∀ S ∈ H, Disjoint S D)
    (hhit : ∀ S ∈ H, (S∩T).Nonempty) :
    H.card+T.card*(D.card+2)+T.card.choose 2≤T.card*Ω.card := by
  have hmaps : ∀ S ∈ H, Hit T S∈T := by
    intro S hS
    exact (Finset.mem_inter.mp (hit_spec (hhit S hS)).1).2
  have hf : H.card=∑ x ∈ T, (HitBucket H T x).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hr : (∑ x ∈ T, (Earlier T x).card)=T.card.choose 2 := by
    rw [sum_earlier_function T (fun i => i), Finset.sum_range_id, ← Nat.choose_two_right]
  have hb := Finset.sum_le_sum (fun x hx => actual_bucket_capacity
    hlegal hbad hu hD hT huD huT hDT hroot havoid hhit hx)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hb
  rw [← hf, hr] at hb
  nlinarith only [hb]

#print axioms actual_root_hit_budget
end
end JSP233.FirstHitBudget84364
