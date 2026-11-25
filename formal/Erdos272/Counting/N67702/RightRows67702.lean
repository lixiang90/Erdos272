module

public import Erdos272.Counting.RightJoint50

@[expose] public section

namespace JSP233.RightRows67702
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem active_sum_plus_one (A : Finset ℤ) (H J : ℤ → ℕ) (X : ℕ) :
    (∀ i ∈ A, J i ≤ X) →
    (∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1) →
    ∀ t ∈ A, (∀ i ∈ A, i ≤ t) →
      (∑ i ∈ A, (H i+J i))+1 ≤ A.card*(X+1)+H t := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | @insert a A hmax ih =>
    intro hJ hcross t ht htop
    have haA : a ∉ A := by
      intro ha
      exact (lt_irrefl a) (hmax a ha)
    have hat : a ≤ t := htop a (Finset.mem_insert_self _ _)
    have hta : t=a := by
      rcases Finset.mem_insert.mp ht with heq | htA
      · exact heq
      · have hlt := hmax t htA
        omega
    subst t
    by_cases hne : A.Nonempty
    · let m := A.max' hne
      have hmA : m ∈ A := Finset.max'_mem A hne
      have hih := ih (fun i hi => hJ i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij) m hmA
        (fun i hi => Finset.le_max' A i hi)
      have hstep := hcross m (Finset.mem_insert_of_mem hmA) a
        (Finset.mem_insert_self _ _) (hmax m hmA)
      rw [Finset.sum_insert haA,Finset.card_insert_of_notMem haA]
      nlinarith only [hih,hstep]
    · have hz : A=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hJa := hJ a (Finset.mem_insert_self _ _)
      simp only [hz,Finset.insert_empty,Finset.sum_singleton,Finset.card_singleton,Nat.one_mul]
      omega

theorem total_last_zero {I A : Finset ℤ} (hAI : A ⊆ I)
    (H J : ℤ → ℕ) (X : ℕ) (t : ℤ) (ht : t ∈ A)
    (htop : ∀ i ∈ I, i ≤ t) (hzero : H t=0)
    (hJ : ∀ i ∈ A, J i ≤ X)
    (hcross : ∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1)
    (hinactive : ∀ i ∈ I\A, H i+J i ≤ X) :
    (∑ i ∈ I, (H i+J i))+1 ≤ I.card*X+I.card := by
  have hactive := active_sum_plus_one A H J X hJ hcross t ht
    (fun i hi => htop i (hAI hi))
  rw [hzero,Nat.add_zero] at hactive
  have hrest : (∑ i ∈ I\A, (H i+J i)) ≤ (I\A).card*X := by
    simpa using Finset.sum_le_sum hinactive
  have hsum := Finset.sum_sdiff hAI (f := fun i => H i+J i)
  have hcards := Finset.card_sdiff_add_card_eq_card hAI
  have hAcard := Finset.card_le_card hAI
  have hmul : (I\A).card*X+A.card*X=I.card*X := by
    rw [←Nat.add_mul,hcards]
  nlinarith only [hactive,hrest,hsum,hAcard,hmul]

#print axioms active_sum_plus_one
#print axioms total_last_zero
end JSP233.RightRows67702
