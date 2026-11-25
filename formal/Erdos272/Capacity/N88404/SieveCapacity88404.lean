module

public import Erdos272.Capacity.N88404.SievePieces88404
public import Erdos272.Resources.APResidual208

@[expose] public section

namespace JSP233.SieveCapacity88404
open StarCompletion APGeometry IntrinsicTriples208 APShadowCapacity16858
open APClasses88404 APClassFrame88404 SieveConstants88404 SievePieces88404
open PhaseCard88404 InclusionExclusion88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem shadow_biUnion {ι : Type*} [DecidableEq ι]
    (J : Finset ι) (U : ι → Finset (Finset ℤ)) :
    APShadow (J.biUnion U) = J.biUnion (fun p => APShadow (U p)) := by
  ext Q
  constructor
  · intro hQ
    obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨p, hp, hSp⟩ := Finset.mem_biUnion.mp hS
    exact Finset.mem_biUnion.mpr ⟨p, hp, Finset.mem_biUnion.mpr ⟨S, hSp, hQS⟩⟩
  · intro hQ
    obtain ⟨p, hp, hQp⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨S, hS, hQS⟩ := Finset.mem_biUnion.mp hQp
    exact Finset.mem_biUnion.mpr ⟨S, Finset.mem_biUnion.mpr ⟨p, hp, hS⟩, hQS⟩

theorem weighted_shadow_of_span {N : ℕ} {F : Finset (Finset ℤ)} {n : ℝ}
    (hN : 1 ≤ N) (hn : 0 ≤ n) (hspan : (N : ℝ)-1 ≤ n) (hF : Legal (Ground N) F) :
    (∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
      (APShadow (Steps.biUnion (StepAP F))).card+
        ∑ p ∈ Steps, Error p*(n/(p : ℝ)+1)^2 := by
  let f : ∀ p ∈ Steps, Frame N p (StepAP F p) :=
    fun p hp => Classical.choice (frame_nonempty (by omega : 1 ≤ N) (steps_positive hp) hF)
  let r : ℕ → ℤ := fun p => if hp : p ∈ Steps then (f p hp).offset else 0
  let M : ℕ → ℕ := fun p => if hp : p ∈ Steps then (f p hp).size else 1
  let S := fun p => APShadow (StepAP F p)
  let A := fun p => Avoid (S p) (fun j => AllPhase j (r j)) (Later p)
  have hphase : ∀ p ∈ Steps, ∀ Q ∈ S p, AllPhase p (r p) Q := by
    intro p hp Q hQ
    simpa only [r, dif_pos hp] using frame_shadow_phase (steps_positive hp) (f p hp) hQ
  have hdisj := pieces_disjoint S r hphase
  have hsub : Steps.biUnion A ⊆ APShadow (Steps.biUnion (StepAP F)) := by
    rw [shadow_biUnion]
    intro Q hQ
    obtain ⟨p, hp, hQp⟩ := Finset.mem_biUnion.mp hQ
    exact Finset.mem_biUnion.mpr ⟨p, hp, (Finset.mem_filter.mp hQp).1⟩
  have hcNat : (∑ p ∈ Steps, (A p).card) ≤ (APShadow (Steps.biUnion (StepAP F))).card := calc
    _ = (Steps.biUnion A).card := (Finset.card_biUnion hdisj).symm
    _ ≤ _ := Finset.card_le_card hsub
  have hcR : (∑ p ∈ Steps, ((A p).card : ℝ)) ≤
      (APShadow (Steps.biUnion (StepAP F))).card := by exact_mod_cast hcNat
  have hp : ∀ p ∈ Steps, Alpha p*((S p).card : ℝ)-Error p*(M p : ℝ)^2 ≤ (A p).card := by
    intro p hp
    simpa only [M, dif_pos hp] using frame_piece_bound hp (f p hp) r
  have hsum := Finset.sum_le_sum hp
  rw [Finset.sum_sub_distrib] at hsum
  have hM : ∀ p ∈ Steps, (M p : ℝ) ≤ n/(p : ℝ)+1 := by
    intro p hp
    have hpR : (0 : ℝ) < p := by exact_mod_cast steps_positive hp
    have hs := (f p hp).span
    have hd : ((f p hp).size : ℝ)-1 ≤ n/(p : ℝ) :=
      (le_div_iff₀ hpR).mpr (by nlinarith only [hs, hspan])
    simpa only [M, dif_pos hp] using (show ((f p hp).size : ℝ) ≤ n/(p : ℝ)+1 by
      linarith only [hd])
  have heach : ∀ p ∈ Steps, Error p*(M p : ℝ)^2 ≤ Error p*(n/(p : ℝ)+1)^2 := by
    intro p hp
    have hs := mul_nonneg (sub_nonneg.mpr (hM p hp))
      (show 0 ≤ n/(p : ℝ)+1+(M p : ℝ) by positivity)
    exact mul_le_mul_of_nonneg_left (by nlinarith only [hs]) (error_nonnegative hp)
  have he := Finset.sum_le_sum heach
  change (∑ p ∈ Steps, Alpha p*((S p).card : ℝ)) ≤ _
  linarith only [hsum, he, hcR]

theorem actual_weighted_shadow {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1000 ≤ N) (hF : Legal (Ground N) F) :
    (∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
      (APShadow (Steps.biUnion (StepAP F))).card+(N : ℝ)^2/2 := by
  have hs := weighted_shadow_of_span (n := (N : ℝ)) (by omega : 1 ≤ N)
    (by positivity) (by linarith) hF
  linarith only [hs, error_sum_bound (n := (N : ℝ)) (by exact_mod_cast hN)]

theorem capacity_of_shadow {N : ℕ} {F : Finset (Finset ℤ)} {E : ℝ}
    (hF : Legal (Ground N) F)
    (hs : (∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
      (APShadow (Steps.biUnion (StepAP F))).card+E) :
    6*(∑ S ∈ F, ((Pool S).card : ℝ))+
      6*(∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
        ((N : ℝ)-1)^3-((N : ℝ)-1)+6*E := by
  let U := Steps.biUnion (StepAP F)
  have hUF : U ⊆ F := by
    intro S hS
    obtain ⟨p, hp, hS⟩ := Finset.mem_biUnion.mp hS
    exact APClasses88404.subset F p hS
  have hAP : ∀ S ∈ U, IsAP S := by
    intro S hS
    obtain ⟨p, hp, hS⟩ := Finset.mem_biUnion.mp hS
    exact APClasses88404.is_ap hS
  have hc := actual_AP_family_capacity hF hUF hAP
  rw [ground_card] at hc
  have hcR : (∑ S ∈ F, ((Pool S).card : ℝ))+(APShadow U).card ≤ (N.choose 3 : ℝ) :=
    by exact_mod_cast hc
  change _ ≤ (APShadow U).card+E at hs
  have hchoose := APResidual208.cast_choose_three N
  nlinarith only [hcR, hs, hchoose]

theorem actual_capacity {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1000 ≤ N) (hF : Legal (Ground N) F) :
    6*(∑ S ∈ F, ((Pool S).card : ℝ))+
      6*(∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
        ((N : ℝ)-1)^3-((N : ℝ)-1)+3*(N : ℝ)^2 := by
  linarith only [capacity_of_shadow hF (actual_weighted_shadow hN hF)]

/-- The exact seven-class error at the span of the original ground set. -/
theorem actual_capacity_at_span {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hF : Legal (Ground N) F) :
    6*(∑ S ∈ F, ((Pool S).card : ℝ))+
      6*(∑ p ∈ Steps, Alpha p*((APShadow (StepAP F p)).card : ℝ)) ≤
        ((N : ℝ)-1)^3-((N : ℝ)-1)+6*
          ((606450017/1803601800 : ℝ)*((N : ℝ)-1)^2+
           (13565611/18036018 : ℝ)*((N : ℝ)-1)+2403389/5010005) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs := weighted_shadow_of_span hN (sub_nonneg.mpr hn) le_rfl hF
  rw [error_sum_identity] at hs
  exact capacity_of_shadow hF hs

#print axioms shadow_biUnion
#print axioms actual_weighted_shadow
#print axioms actual_capacity
end
end JSP233.SieveCapacity88404
