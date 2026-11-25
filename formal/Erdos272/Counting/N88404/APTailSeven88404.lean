module

public import Erdos272.Counting.APTail208
public import Erdos272.Counting.N88404.APClasses88404
public import Erdos272.Capacity.N88404.SieveConstants88404

@[expose] public section

namespace JSP233.APTailSeven88404
open StarCompletion APGeometry APCount41 HarmonicAbel29 APTail208
open APClasses88404 SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def TailSteps (N : ℕ) : Finset ℕ := Finset.Icc 2 N \ Selected

theorem selected_subset {N : ℕ} (hN : 13≤N) : Selected⊆Finset.Icc 2 N := by
  intro p hp
  have hr := selected_range hp
  exact Finset.mem_Icc.mpr ⟨hr.1, hr.2.trans hN⟩

theorem reciprocal_square_tail {N : ℕ} (hN : 13≤N) :
    (∑ d∈TailSteps N, (1 : ℝ)/(d : ℝ)^2) ≤
      129/200-(∑ p∈Selected, (1 : ℝ)/(p : ℝ)^2) := by
  have hs := Finset.sum_sdiff (f := fun d : ℕ => (1 : ℝ)/(d : ℝ)^2) (selected_subset hN)
  have hb := EndpointExterior55.reciprocal_square_tail_two N
  change (∑ d∈TailSteps N, (1 : ℝ)/(d : ℝ)^2)+
    (∑ p∈Selected, (1 : ℝ)/(p : ℝ)^2) = _ at hs
  linarith only [hs, hb]

theorem harmonic_tail {N : ℕ} (hN : 13≤N) :
    (∑ d∈TailSteps N, (1 : ℝ)/(d : ℝ)) =
      Harmonic N-1-(∑ p∈Selected, (1 : ℝ)/(p : ℝ)) := by
  have hs := Finset.sum_sdiff (f := fun d : ℕ => (1 : ℝ)/(d : ℝ)) (selected_subset hN)
  have hb := APTail208.harmonic_tail_two (by omega : 1≤N)
  change (∑ d∈TailSteps N, (1 : ℝ)/(d : ℝ))+
    (∑ p∈Selected, (1 : ℝ)/(p : ℝ)) = _ at hs
  linarith only [hs, hb]

theorem actual_tail_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 13≤N) (hlegal : Legal (Ground N) F)
    (hAP : ∀ S∈F, IsAP S) (htwo : ∀ S∈F, 2≤S.card)
    (houtside : ∀ S∈F, Step S∉Steps) :
    (F.card : ℝ) ≤
      (129/800-(∑ p∈Selected, (1 : ℝ)/(4*(p : ℝ)^2)))*(N : ℝ)^2+
      (N : ℝ)*(Harmonic N-1-(∑ p∈Selected, (1 : ℝ)/(p : ℝ))) := by
  have hmaps : ∀ S∈F, Step S∈TailSteps N := by
    intro S hS
    have hp := (actual_step (hAP S hS)).1
    have h1 : Step S≠1 := by
      intro he
      exact houtside S hS (by simp only [he, Steps, Finset.mem_insert_self])
    have hnot : Step S∉Selected := by
      intro hm
      exact houtside S hS (Finset.mem_insert_of_mem hm)
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,
      actual_step_bound (hlegal.1 S hS) (hAP S hS) (htwo S hS)⟩, hnot⟩
  have hpart : (F.card : ℝ) =
      ∑ d∈TailSteps N, ((F.filter (fun S => Step S=d)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ d∈TailSteps N,
      ((F.filter (fun S => Step S=d)).card : ℝ) ≤
        (N : ℝ)^2/(4*(d : ℝ)^2)+(N : ℝ)/d := by
    intro d hd
    have hsub : F.filter (fun S => Step S=d)⊆F := Finset.filter_subset _ _
    have hC : Legal (Ground N) (F.filter (fun S => Step S=d)) :=
      ⟨fun S hS => hlegal.1 S (hsub hS),
        fun S hS T hT hST => hlegal.2 S (hsub hS) T (hsub hT) hST⟩
    have hdpos : 0<d := by
      have hh := (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1).1
      omega
    apply actual_same_step_two_count hdpos hC (fun S hS => htwo S (hsub hS))
    intro S hS
    obtain ⟨_, p, hp⟩ := actual_step (hAP S (hsub hS))
    exact ⟨p, by simpa only [(Finset.mem_filter.mp hS).2] using hp⟩
  have hsum : (F.card : ℝ) ≤
      (N : ℝ)^2/4*(∑ d∈TailSteps N, (1 : ℝ)/(d : ℝ)^2)+
      (N : ℝ)*(Harmonic N-1-(∑ p∈Selected, (1 : ℝ)/(p : ℝ))) := by
    calc
      _ ≤ ∑ d∈TailSteps N, ((N : ℝ)^2/(4*(d : ℝ)^2)+(N : ℝ)/d) := by
        rw [hpart]
        exact Finset.sum_le_sum hclass
      _ = _ := by
        have hterm : ∀ d : ℕ, (N : ℝ)^2/(4*(d : ℝ)^2)+(N : ℝ)/d =
            (N : ℝ)^2/4*(1/(d : ℝ)^2)+(N : ℝ)*(1/d) := by
          intro d
          ring
        simp_rw [hterm]
        rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum, harmonic_tail hN]
  have hquad := mul_le_mul_of_nonneg_left (reciprocal_square_tail hN)
    (show (0 : ℝ)≤(N : ℝ)^2/4 by positivity)
  norm_num [Selected] at hquad hsum ⊢
  nlinarith only [hsum, hquad]

theorem actual_AP_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 13≤N) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ) ≤
      (∑ p∈Steps, ((StepAP F p).card : ℝ))+
      (129/800-(∑ p∈Selected, (1 : ℝ)/(4*(p : ℝ)^2)))*(N : ℝ)^2+
      (N : ℝ)*(Harmonic N-1-(∑ p∈Selected, (1 : ℝ)/(p : ℝ)))+1 := by
  let P := F.filter IsAP
  let A := P.filter fun S => 2≤S.card
  let C := P.filter fun S => ¬2≤S.card
  let U := A.filter fun S => Step S∈Steps
  let T := A.filter fun S => Step S∉Steps
  have hPF : P⊆F := Finset.filter_subset _ _
  have hAP : A⊆P := Finset.filter_subset _ _
  have hAF : A⊆F := hAP.trans hPF
  have hCF : C⊆F := (Finset.filter_subset _ _).trans hPF
  have hUA : U⊆A := Finset.filter_subset _ _
  have hTA : T⊆A := Finset.filter_subset _ _
  have hTF : T⊆F := hTA.trans hAF
  have hsub : ∀ G : Finset (Finset ℤ), G⊆F → Legal (Ground N) G := by
    intro G hGF
    exact ⟨fun S hS => hF.1 S (hGF hS),
      fun S hS V hV hSV => hF.2 S (hGF hS) V (hGF hV) hSV⟩
  have ht := actual_tail_count hN (hsub T hTF)
    (fun S hS => (Finset.mem_filter.mp (hAP (hTA hS))).2)
    (fun S hS => (Finset.mem_filter.mp (hTA hS)).2)
    (fun S hS => (Finset.mem_filter.mp hS).2)
  have hs := actual_singleton_family_count (hsub C hCF)
    (fun S hS => by have hh := (Finset.mem_filter.mp hS).2; omega)
  have hmaps : ∀ S∈U, Step S∈Steps := fun S hS => (Finset.mem_filter.mp hS).2
  have hpartU : (U.card : ℝ) =
      ∑ p∈Steps, ((U.filter (fun S => Step S=p)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmaps
  have hclass : ∀ p∈Steps, U.filter (fun S => Step S=p)=StepAP F p := by
    intro p hp
    ext S
    simp only [U, A, P, StepAP, Finset.mem_filter]
    constructor
    · rintro ⟨⟨⟨⟨hSF, hSA⟩, htwo⟩, _hSteps⟩, he⟩
      exact ⟨hSF, hSA, htwo, he⟩
    · rintro ⟨hSF, hSA, htwo, he⟩
      exact ⟨⟨⟨⟨hSF, hSA⟩, htwo⟩, by simpa only [he] using hp⟩, he⟩
  have hU : (U.card : ℝ) = ∑ p∈Steps, ((StepAP F p).card : ℝ) := by
    calc
      _ = ∑ p∈Steps, ((U.filter (fun S => Step S=p)).card : ℝ) := hpartU
      _ = _ := Finset.sum_congr rfl (fun p hp => by rw [hclass p hp])
  have hp := Finset.card_filter_add_card_filter_not (s := P) (fun S => 2≤S.card)
  have hq := Finset.card_filter_add_card_filter_not (s := A) (fun S => Step S∈Steps)
  change A.card+C.card=P.card at hp
  change U.card+T.card=A.card at hq
  have hpR : (A.card : ℝ)+C.card=P.card := by exact_mod_cast hp
  have hqR : (U.card : ℝ)+T.card=A.card := by exact_mod_cast hq
  have hsR : (C.card : ℝ)≤1 := by exact_mod_cast hs
  change (P.card : ℝ)≤_
  linarith only [ht, hU, hpR, hqR, hsR]

#print axioms selected_subset
#print axioms reciprocal_square_tail
#print axioms harmonic_tail
#print axioms actual_tail_count
#print axioms actual_AP_count
end
end JSP233.APTailSeven88404
