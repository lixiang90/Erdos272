import Erdos272.Resources.CoreCleanup208

namespace JSP233.HeavyCredit208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_light_credit {ι : Type*} [DecidableEq ι] {F : Finset (Finset ℤ)}
    (label : Finset ℤ → ι) (I H : Finset ι) (W T : ι → ℕ)
    (hmap : ∀ S ∈ F, label S ∈ I)
    (hlight : ∀ i ∈ I, i ∉ H → (F.filter (fun S => label S=i)).card ≤ W i)
    (hcredit : ∀ i ∈ I, i ∈ H → T i ≤ W i) :
    F.card+(∑ i∈I, if i∈H then T i else 0) ≤
      (∑ i∈I, W i)+(F.filter (fun S => label S∈H)).card := by
  let A := F.filter (fun S => label S∈H)
  have hpart : F.card=∑ i∈I, (F.filter (fun S => label S=i)).card :=
    Finset.card_eq_sum_card_fiberwise hmap
  have hpartA : A.card=∑ i∈I, if i∈H then (F.filter (fun S => label S=i)).card else 0 := by
    have hAp : A.card=∑ i∈I, (A.filter (fun S => label S=i)).card :=
      Finset.card_eq_sum_card_fiberwise (fun S hS => hmap S (Finset.mem_filter.mp hS).1)
    rw [hAp]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hH : i∈H
    · rw [if_pos hH]
      congr 1
      ext S
      simp only [A,Finset.mem_filter]
      aesop
    · rw [if_neg hH]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSA,hSi⟩ := Finset.mem_filter.mp hS
      have hh := (Finset.mem_filter.mp hSA).2
      exact hH (hSi ▸ hh)
  have hp : ∀ i∈I,
      (F.filter (fun S => label S=i)).card+(if i∈H then T i else 0) ≤
      W i+(if i∈H then (F.filter (fun S => label S=i)).card else 0) := by
    intro i hi
    by_cases hH : i∈H
    · simp only [if_pos hH]
      have hh := hcredit i hi hH
      omega
    · simp only [if_neg hH,add_zero]
      exact hlight i hi hH
  have hs := Finset.sum_le_sum hp
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←hpart,←hpartA] at hs
  exact hs

theorem actual_cleanup_credit {ι : Type*} [DecidableEq ι] {F G : Finset (Finset ℤ)}
    (label : Finset ℤ → ι) (I H : Finset ι) (W T : ι → ℕ) (fee : ℕ)
    (hmap : ∀ S ∈ F, label S ∈ I)
    (hlight : ∀ i ∈ I, i ∉ H → (F.filter (fun S => label S=i)).card ≤ W i)
    (hcredit : ∀ i ∈ I, i ∈ H → T i ≤ W i)
    (hcleanup : (F.filter (fun S => label S∈H)).card ≤ G.card+fee) :
    F.card+(∑ i∈I, if i∈H then T i else 0) ≤ (∑ i∈I, W i)+G.card+fee := by
  have hp := actual_light_credit label I H W T hmap hlight hcredit
  omega

#print axioms actual_light_credit
#print axioms actual_cleanup_credit
end
end JSP233.HeavyCredit208
