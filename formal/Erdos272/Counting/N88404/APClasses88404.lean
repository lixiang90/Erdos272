module

public import Erdos272.Counting.APCount41
public import Erdos272.Counting.UnitCount218

@[expose] public section

namespace JSP233.APClasses88404
open StarCompletion APGeometry APCount41
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def StepAP (F : Finset (Finset ℤ)) (d : ℕ) : Finset (Finset ℤ) :=
  F.filter fun S => IsAP S ∧ 2 ≤ S.card ∧ Step S = d

theorem subset (F : Finset (Finset ℤ)) (d : ℕ) : StepAP F d ⊆ F :=
  Finset.filter_subset _ _

theorem legal {N d : ℕ} {F : Finset (Finset ℤ)} (hF : Legal (Ground N) F) :
    Legal (Ground N) (StepAP F d) :=
  ⟨fun S hS => hF.1 S (subset F d hS),
    fun S hS T hT hST => hF.2 S (subset F d hS) T (subset F d hT) hST⟩

theorem is_ap {F : Finset (Finset ℤ)} {d : ℕ} {S : Finset ℤ} (hS : S ∈ StepAP F d) :
    IsAP S := (Finset.mem_filter.mp hS).2.1

theorem card_two {F : Finset (Finset ℤ)} {d : ℕ} {S : Finset ℤ} (hS : S ∈ StepAP F d) :
    2 ≤ S.card := (Finset.mem_filter.mp hS).2.2.1

theorem ap_at {F : Finset (Finset ℤ)} {d : ℕ} {S : Finset ℤ} (hS : S ∈ StepAP F d) :
    ∃ p : ℤ, APAt (d : ℤ) p S := by
  obtain ⟨hd, p, hp⟩ := actual_step (is_ap hS)
  exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2.2.2] using hp⟩

theorem common_root {N d : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hne : (StepAP F d).Nonempty) :
    ∃ c ∈ Ground N, ∀ S ∈ StepAP F d, c ∈ S := by
  exact actual_same_step_common_root hne (legal hF)
    (fun S hS => Finset.card_pos.mp (by have ht := card_two hS; omega))
    (fun S hS => ap_at hS)

#print axioms subset
#print axioms legal
#print axioms is_ap
#print axioms card_two
#print axioms ap_at
#print axioms common_root
end
end JSP233.APClasses88404
