module

public import Erdos272.Geometry.N94488.StepTwoGeometry94488
public import Erdos272.Counting.UnitCount218

@[expose] public section

namespace JSP233.ShadowOverlap94488
open StarCompletion APGeometry APCount41 UnitCount218 OneThird32 AffineLine30
open APShadowCapacity16858 AffineShadow94488 StepTwoGeometry94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem parity_count (c p : ℤ) (A B : ℕ) :
    2*((Finset.Icc (c-A) (c+B)).filter (fun x => (x-p)%2 = 0)).card ≤ A+B+2 := by
  let I := Finset.Icc (c-A) (c+B)
  let V := ParityIndex p I
  let a := (c-(A : ℤ)-p+1)/2
  let b := (c+(B : ℤ)-p)/2
  have he : V = Finset.Icc a b := by
    ext x
    rw [mem_parityIndex]
    simp only [I, Finset.mem_Icc]
    dsimp only [a, b]
    omega
  have hcard : (I.filter (fun x => (x-p)%2 = 0)).card = V.card := by
    have hh := mapSet_card p 2 (by norm_num) V
    rw [map_parity_index] at hh
    exact hh
  change 2*(I.filter (fun x => (x-p)%2 = 0)).card ≤ A+B+2
  rw [hcard]
  by_cases hne : V.Nonempty
  · have hab : a ≤ b := by rw [he] at hne; exact Finset.nonempty_Icc.mp hne
    have hc : (V.card : ℤ) = b+1-a := by rw [he, Int.card_Icc]; omega
    have hb : 2*(V.card : ℤ) ≤ (A : ℤ)+B+2 := by dsimp only [a, b] at hc; omega
    exact_mod_cast hb
  · have hz : V = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz, Finset.card_empty, mul_zero]
    omega

theorem shadow_overlap {N A B : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F)
    (henv : ∀ S ∈ UnitAP F, S ⊆ Finset.Icc (c-A) (c+B)) :
    6*((APShadow (UnitAP F) ∩ APShadow (StepTwo F)).card : ℝ) ≤
      ((A : ℝ)+B)^3/8 := by
  obtain ⟨p, hphase⟩ := actual_phase hF
  let I := (Finset.Icc (c-A) (c+B)).filter (fun x => (x-p)%2 = 0)
  have hsub : APShadow (UnitAP F) ∩ APShadow (StepTwo F) ⊆ I.powersetCard 3 := by
    intro Q hQ
    obtain ⟨hQ1, hQ2⟩ := Finset.mem_inter.mp hQ
    obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ1
    obtain ⟨T, hT, hQT⟩ := Finset.mem_biUnion.mp hQ2
    obtain ⟨hQSsub, hQcard⟩ := Finset.mem_powersetCard.mp hQS
    obtain ⟨hQTsub, hQTcard⟩ := Finset.mem_powersetCard.mp hQT
    refine Finset.mem_powersetCard.mpr ⟨?_, hQcard⟩
    intro x hx
    exact Finset.mem_filter.mpr ⟨henv S hS (hQSsub hx), hphase T hT x (hQTsub hx)⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_powersetCard] at hc
  have hcR : ((APShadow (UnitAP F) ∩ APShadow (StepTwo F)).card : ℝ) ≤
      (I.card.choose 3 : ℝ) := by exact_mod_cast hc
  have hb : 2*(I.card : ℝ) ≤ (A : ℝ)+B+2 := by
    exact_mod_cast parity_count c p A B
  have hchoose := APResidual208.cast_choose_three I.card
  by_cases hz : I.card = 0
  · have hc0 : ((APShadow (UnitAP F) ∩ APShadow (StepTwo F)).card : ℝ) ≤ 0 := by
      simpa only [hz, Nat.choose_zero_succ, Nat.cast_zero] using hcR
    have hw : 0 ≤ (A : ℝ)+B := by positivity
    have hp := pow_nonneg hw 3
    linarith only [hc0, hp]
  · have hk : 1 ≤ (I.card : ℝ) := by exact_mod_cast (show 1 ≤ I.card by omega)
    have hw : 0 ≤ (A : ℝ)+B := by positivity
    have hr : 0 ≤ (I.card : ℝ)-1 := by linarith only [hk]
    have hd : 0 ≤ (A : ℝ)+B-2*((I.card : ℝ)-1) := by linarith only [hb]
    have hp := mul_nonneg hd
      (show 0 ≤ ((A : ℝ)+B)^2+2*((A : ℝ)+B)*((I.card : ℝ)-1)+
        4*((I.card : ℝ)-1)^2 by positivity)
    nlinarith only [hcR, hchoose, hp, hr]

#print axioms parity_count
#print axioms shadow_overlap
end
end JSP233.ShadowOverlap94488
