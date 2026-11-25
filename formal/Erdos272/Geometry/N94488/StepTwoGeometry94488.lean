module

public import Erdos272.Geometry.N94488.AffineShadow94488
public import Erdos272.Arithmetic.N291012.UnitShadowGeometry291012

@[expose] public section

namespace JSP233.StepTwoGeometry94488
open StarCompletion APGeometry APCount41 OneThird32 AffineLine30
open APShadowCapacity16858 AffineShadow94488 UnitShadowGeometry291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def StepTwo (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.filter fun S => IsAP S ∧ 2 ≤ S.card ∧ Step S = 2

theorem actual_frame {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hne : (StepTwo F).Nonempty) :
    ∃ p c : ℤ, -1 ≤ p ∧ p ≤ 0 ∧ c ∈ Ground N ∧ (c-p)%2 = 0 ∧
      ∀ S ∈ StepTwo F, c ∈ S ∧ APAt 2 p S := by
  have hsub : StepTwo F ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (StepTwo F) :=
    ⟨fun S hS => hF.1 S (hsub hS),
      fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
  have htwo : ∀ S ∈ StepTwo F, 2 ≤ S.card :=
    fun S hS => (Finset.mem_filter.mp hS).2.2.1
  have hstep : ∀ S ∈ StepTwo F, ∃ q : ℤ, APAt (2 : ℤ) q S := by
    intro S hS
    obtain ⟨hSF, hAP, ht, hs⟩ := Finset.mem_filter.mp hS
    obtain ⟨hd, q, hp⟩ := actual_step hAP
    exact ⟨q, by simpa only [hs, Nat.cast_ofNat] using hp⟩
  obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root hne hlegal
    (fun S hS => Finset.card_pos.mp (by have hh := htwo S hS; omega)) hstep
  let p := -(c%2)
  have hpdiv : (2 : ℤ) ∣ p-c := ⟨(p-c)/2, by dsimp only [p]; omega⟩
  refine ⟨p, c, by dsimp only [p]; omega, by dsimp only [p]; omega,
    hc, by dsimp only [p]; omega, ?_⟩
  intro S hS
  obtain ⟨q, hq⟩ := hstep S hS
  have hd := apAt_residue hq (hroot S hS)
  have hpd : (2 : ℤ) ∣ p-q := by
    convert Int.dvd_add hpdiv hd using 1 <;> ring
  exact ⟨hroot S hS, apAt_change_phase hq hpd⟩

theorem actual_phase {N : ℕ} {F : Finset (Finset ℤ)} (hF : Legal (Ground N) F) :
    ∃ p : ℤ, ∀ S ∈ StepTwo F, ∀ x ∈ S, (x-p)%2 = 0 := by
  by_cases hne : (StepTwo F).Nonempty
  · obtain ⟨p, c, hp1, hp0, hc, hcp, hframe⟩ := actual_frame hF hne
    refine ⟨p, ?_⟩
    intro S hS x hx
    exact Int.emod_eq_zero_of_dvd (apAt_residue (hframe S hS).2 hx)
  · refine ⟨0, ?_⟩
    intro S hS
    exact False.elim (hne ⟨S, hS⟩)

theorem parity_ground {N : ℕ} {p x : ℤ} (hp1 : -1 ≤ p) (hp0 : p ≤ 0)
    (hx : p+2*x ∈ Ground N) : x ∈ Ground ((N+1)/2) := by
  have hb := (mem_ground N _).mp hx
  have hdiv : N+1 < 2*((N+1)/2+1) := by omega
  have hdivZ : (N : ℤ)+1 < 2*(((N+1)/2 : ℕ) : ℤ)+2 := by exact_mod_cast hdiv
  apply (mem_ground _ _).mpr
  constructor <;> omega

theorem actual_geometry {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) :
    ∃ w y : ℝ, 0 ≤ w ∧ 2*w ≤ ((N-1 : ℕ) : ℝ) ∧ 0 ≤ y ∧ 2*y ≤ w ∧
      ((StepTwo F).card : ℝ) ≤ y^2+w ∧
      8*y^3 ≤ 6*((APShadow (StepTwo F)).card : ℝ)+w := by
  by_cases hne : (StepTwo F).Nonempty
  · obtain ⟨p, c, hp1, hp0, hc, hcp, hframe⟩ := actual_frame hF hne
    let U := StepTwo F
    let V := U.image (ParityIndex p)
    let M := (N+1)/2
    have hphase : ∀ S ∈ U, ∀ x ∈ S, (x-p)%2 = 0 := by
      intro S hS x hx
      exact Int.emod_eq_zero_of_dvd (apAt_residue (hframe S hS).2 hx)
    have hmap : mapFamily p 2 V = U := parity_family hphase
    have hcard : V.card = U.card := by
      have hh := mapFamily_card p 2 (by norm_num) V
      rw [hmap] at hh
      exact hh.symm
    have hshadow : (APShadow V).card = (APShadow U).card := by
      have hh := map_shadow_card p 2 (by norm_num) V
      rw [hmap] at hh
      exact hh.symm
    have hground : ∀ T ∈ V, T ⊆ Ground M := by
      intro T hT x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      exact parity_ground hp1 hp0
        (hF.1 S (Finset.filter_subset _ _ hS) ((mem_parityIndex p x S).mp hx))
    let j := (c-p)/2
    have hj : p+2*j = c := by dsimp only [j]; omega
    have hjground : j ∈ Ground M := parity_ground hp1 hp0 (by rwa [hj])
    have hroot : ∀ T ∈ V, j ∈ T := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      rw [mem_parityIndex, hj]
      exact (hframe S hS).1
    have htwo : ∀ T ∈ V, 2 ≤ T.card := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      have he := mapSet_card p 2 (by norm_num) (ParityIndex p S)
      rw [map_parity_index_of_phase (hphase S hS)] at he
      rw [← he]
      exact (Finset.mem_filter.mp hS).2.2.1
    have hi : ∀ T ∈ V, ∃ a b : ℤ, T = Finset.Icc a b := by
      intro T hT
      have ht := htwo T hT
      have htne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      exact interval_eq_icc htne (parityIndex_interval (Or.inr (hframe S hS).2))
    obtain ⟨y, hy, hyM, hcount, hmass⟩ :=
      interval_geometry hjground hground hroot hi htwo
    let w : ℝ := (M-1 : ℕ)
    have hw : 0 ≤ w := Nat.cast_nonneg _
    have hwN : 2*w ≤ ((N-1 : ℕ) : ℝ) := by
      have hM : 2*(M-1) ≤ N-1 := by dsimp only [M]; omega
      dsimp only [w]
      exact_mod_cast hM
    have hyw : 2*y ≤ w := by
      by_contra hn
      have hp := mul_pos (show 0 < 2*y-w by linarith only [hn])
        (show 0 < 2*y+w by linarith only [hy, hw, hn])
      nlinarith only [hp, hyM]
    rw [hcard] at hcount
    rw [hshadow] at hmass
    exact ⟨w, y, hw, hwN, hy, hyw, hcount, hmass⟩
  · have he : StepTwo F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, 0, le_rfl, by simpa using (Nat.cast_nonneg (α := ℝ) (N-1)),
      le_rfl, by norm_num, ?_, ?_⟩ <;>
      simp [he, APShadow]

#print axioms actual_frame
#print axioms actual_phase
#print axioms parity_ground
#print axioms actual_geometry
end
end JSP233.StepTwoGeometry94488
