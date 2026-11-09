module

public import Erdos272.Foundation.PrivateFinset
public import Mathlib.Data.Int.Interval

@[expose] public section

/-! Actual AP step forcing in the unit-step and near-full step-three
branches. No uniform pair-step or scalar payment premise is assumed. -/

namespace JSP233.PrimeKernel

open StarCompletion

theorem interval_isAP (a b : Int) (hab : a ≤ b) : IsAP (Finset.Icc a b) := by
  refine ⟨1, a, by omega, a, b, ?_, by simp [hab]⟩
  intro x
  simp

theorem step_dvd_gap (S : Finset Int) (a b : Int)
    (hS : IsAP S) (ha : a ∈ S) (hb : b ∈ S) :
    ∃ q : Int, 0 < q ∧ q ∣ b-a ∧ PrivateUnion.APAt q a (fun x => x ∈ S) := by
  rcases (PrivateFinset.isAP_iff_predicate S).mp hS with ⟨q, r, hrep, _⟩
  have hrep' := PrivateUnion.APAt_rebase q r a (fun x => x ∈ S) hrep ha
  rcases hrep' with ⟨hq, lo, hi, hiff⟩
  exact ⟨q, hq, ((hiff b).mp hb).2.2, hq, lo, hi, hiff⟩

theorem positive_divisor_three (q : Int) (hq : 0 < q) (hdiv : q ∣ 3) :
    q = 1 ∨ q = 3 := by
  have hle := Int.le_of_dvd (by norm_num : (0 : Int) < 3) hdiv
  have hcases : q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hcases with h | h | h
  · exact Or.inl h
  · subst q; norm_num at hdiv
  · exact Or.inr h

/-- Unit-step APs contain the whole ordinary hull of any two of their
actual points. -/
theorem unit_step_contains_interval (S : Finset Int) (p a b : Int)
    (hS : PrivateUnion.APAt 1 p (fun x => x ∈ S))
    (ha : a ∈ S) (hb : b ∈ S) : Finset.Icc a b ⊆ S := by
  rcases hS with ⟨_, lo, hi, hrep⟩
  have ha' := (hrep a).mp ha
  have hb' := (hrep b).mp hb
  intro x hx
  have hx' := Finset.mem_Icc.mp hx
  exact (hrep x).mpr ⟨by omega, by omega, one_dvd _⟩

/-- An actual crooked omitter cannot contain an ordinary interval which
already occupies all but at most one point of its ground set. -/
theorem omitter_cannot_contain_near_full_interval
    (Ω S : Finset Int) (c a b : Int) (hc : c ∈ Ω)
    (hground : S ⊆ Ω) (havoid : c ∉ S) (hcrooked : ¬ IsAP S)
    (hab : a ≤ b) (hnear : Ω.card ≤ (Finset.Icc a b).card + 1) :
    ¬ Finset.Icc a b ⊆ S := by
  intro hIS
  have hSsub : S ⊆ Ω.erase c := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro heq; exact havoid (heq ▸ hx), hground hx⟩
  have hScard := Finset.card_le_card hSsub
  rw [Finset.card_erase_of_mem hc] at hScard
  have hΩpos : 0 < Ω.card := Finset.card_pos.mpr ⟨c,hc⟩
  have hScardI : S.card ≤ (Finset.Icc a b).card := by omega
  have heq : Finset.Icc a b = S := Finset.eq_of_subset_of_card_le hIS hScardI
  exact hcrooked (heq ▸ interval_isAP a b hab)

/-- Shared actual adjacent integers force pair-step one. -/
theorem shared_adjacent_forces_step (S T : Finset Int) (a : Int)
    (hpair : IsAP (S ∩ T)) (ha : a ∈ S ∩ T) (hb : a+1 ∈ S ∩ T) :
    PrivateUnion.APAt 1 a (fun x => x ∈ S ∧ x ∈ T) := by
  have hAP := (PrivateFinset.isAP_iff_predicate (S ∩ T)).mp hpair
  apply PrivateUnion.IsAP_same_step_of_adjacent 1 a
    (fun x => x ∈ S) (fun x => x ∈ S ∧ x ∈ T) (by omega)
  · simpa only [Finset.mem_inter] using hAP
  · exact Finset.mem_inter.mp ha
  · exact Finset.mem_inter.mp hb
  · intro x hx; exact hx.1
  · intro x hxlo hxhi; omega

/-- Shared step-three points plus a near-full ordinary hull force the
true AP intersection step to be three, rather than assuming that step. -/
theorem shared_three_near_full_forces_step
    (Ω S T : Finset Int) (c a b : Int) (hc : c ∈ Ω)
    (hground : S ⊆ Ω) (havoid : c ∉ S) (hcrooked : ¬ IsAP S)
    (hab : a ≤ b) (hnear : Ω.card ≤ (Finset.Icc a b).card + 1)
    (hpair : IsAP (S ∩ T))
    (ha : a ∈ S ∩ T) (hnext : a+3 ∈ S ∩ T) (hb : b ∈ S ∩ T) :
    PrivateUnion.APAt 3 a (fun x => x ∈ S ∧ x ∈ T) := by
  rcases step_dvd_gap (S ∩ T) a (a+3) hpair ha hnext with ⟨q,hq,hdiv,hstep⟩
  have hdiv3 : q ∣ 3 := by simpa using hdiv
  rcases positive_divisor_three q hq hdiv3 with hq1 | hq3
  · subst q
    have hI := unit_step_contains_interval (S ∩ T) a a b hstep ha hb
    have hIS : Finset.Icc a b ⊆ S := by
      intro x hx
      exact (Finset.mem_inter.mp (hI hx)).1
    exact False.elim (omitter_cannot_contain_near_full_interval Ω S c a b
      hc hground havoid hcrooked hab hnear hIS)
  · subst q
    simpa only [Finset.mem_inter] using hstep

theorem adjacent_kernel_strict_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (ha : ∀ S ∈ Avoiders F c, a ∈ S)
    (hb : ∀ S ∈ Avoiders F c, a+1 ∈ S) : F.card + 1 ≤ B := by
  apply PrivateFinset.same_step_avoiders_payment Ω F c 1 a B hc hF hstar hm hcrooked ha
  intro S hS T hT hne
  apply shared_adjacent_forces_step S T a
    (hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne)
  · exact Finset.mem_inter.mpr ⟨ha S hS, ha T hT⟩
  · exact Finset.mem_inter.mpr ⟨hb S hS, hb T hT⟩

theorem near_full_three_kernel_strict_payment
    (Ω : Finset Int) (F : Finset (Finset Int)) (c a b : Int) (B : Nat)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hstar : StarBound Ω B)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S)
    (hab : a ≤ b) (hnear : Ω.card ≤ (Finset.Icc a b).card + 1)
    (ha : ∀ S ∈ Avoiders F c, a ∈ S)
    (hnext : ∀ S ∈ Avoiders F c, a+3 ∈ S)
    (hb : ∀ S ∈ Avoiders F c, b ∈ S) : F.card + 1 ≤ B := by
  apply PrivateFinset.same_step_avoiders_payment Ω F c 3 a B hc hF hstar hm hcrooked ha
  intro S hS T hT hne
  apply shared_three_near_full_forces_step Ω S T c a b hc
    (hF.1 S (Finset.mem_filter.mp hS).1) (Finset.mem_filter.mp hS).2
    (hcrooked S hS) hab hnear
    (hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne)
  · exact Finset.mem_inter.mpr ⟨ha S hS, ha T hT⟩
  · exact Finset.mem_inter.mpr ⟨hnext S hS, hnext T hT⟩
  · exact Finset.mem_inter.mpr ⟨hb S hS, hb T hT⟩

#print axioms interval_isAP
#print axioms step_dvd_gap
#print axioms positive_divisor_three
#print axioms unit_step_contains_interval
#print axioms omitter_cannot_contain_near_full_interval
#print axioms shared_adjacent_forces_step
#print axioms shared_three_near_full_forces_step
#print axioms adjacent_kernel_strict_payment
#print axioms near_full_three_kernel_strict_payment

end JSP233.PrimeKernel
