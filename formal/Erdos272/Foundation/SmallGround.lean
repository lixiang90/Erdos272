import Erdos272.Foundation.PrivateFinset
import Mathlib.Data.Finset.Powerset

namespace JSP233.SmallGround

open StarCompletion

/-- Strict extensions of an actual AP core are encoded by distinct
nonempty subsets of the actual available exterior. -/
theorem strict_extension_count (Ω K : Finset Int) (D : Finset (Finset Int))
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (hcore : ∀ S ∈ D, K ⊆ S) (hne : ∀ S ∈ D, S ≠ K) :
    D.card ≤ 2 ^ (Ω \ K).card - 1 := by
  classical
  have hinj : Set.InjOn (fun S : Finset Int => S \ K) (D : Set (Finset Int)) := by
    intro S hS T hT heq
    change S \ K = T \ K at heq
    have hs := Finset.sdiff_union_of_subset (hcore S hS)
    have ht := Finset.sdiff_union_of_subset (hcore T hT)
    rw [heq] at hs
    exact hs.symm.trans ht
  have hsub : D.image (fun S => S \ K) ⊆ (Ω \ K).powerset.erase ∅ := by
    intro U hU
    rcases Finset.mem_image.mp hU with ⟨S,hS,rfl⟩
    apply Finset.mem_erase.mpr
    constructor
    · intro hz
      apply hne S hS
      have hs := Finset.sdiff_union_of_subset (hcore S hS)
      rw [hz] at hs
      simpa using hs.symm
    · apply Finset.mem_powerset.mpr
      intro x hx
      have hx' := Finset.mem_sdiff.mp hx
      exact Finset.mem_sdiff.mpr ⟨hground S hS hx'.1,hx'.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem (Finset.empty_mem_powerset _),
    Finset.card_powerset] at hcard
  exact hcard

/-- The large-kernel part of the N≤5 boundary uses actual extension
counting, not enumeration of all families or a numerical capacity input. -/
theorem small_ground_ap_core_capacity
    (Ω K : Finset Int) (D : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ω) (hsmall : Ω.card ≤ 5) (hm : 2 ≤ D.card)
    (hK : IsAP K) (hk : 2 ≤ K.card)
    (hground : ∀ S ∈ D, S ⊆ Ω)
    (havoid : ∀ S ∈ D, c ∉ S)
    (hcrooked : ∀ S ∈ D, ¬ IsAP S)
    (hcore : ∀ S ∈ D, K ⊆ S) : D.card + K.card ≤ Ω.card := by
  classical
  have hD : D.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨S0,hS0⟩ := hD
  have hground' : ∀ S ∈ D, S ⊆ Ω.erase c := by
    intro S hS x hx
    exact Finset.mem_erase.mpr ⟨by intro heq; exact havoid S hS (heq ▸ hx), hground S hS hx⟩
  have hKsub : K ⊆ Ω.erase c := (hcore S0 hS0).trans (hground' S0 hS0)
  have hneq : ∀ S ∈ D, S ≠ K := by
    intro S hS heq
    exact hcrooked S hS (heq ▸ hK)
  have hcount := strict_extension_count (Ω.erase c) K D hground' hcore hneq
  have htail : ((Ω.erase c) \ K).card = Ω.card - 1 - K.card := by
    rw [Finset.card_sdiff_of_subset hKsub, Finset.card_erase_of_mem hc]
  have hkground := Finset.card_le_card hKsub
  rw [Finset.card_erase_of_mem hc] at hkground
  have hΩpos : 0 < Ω.card := Finset.card_pos.mpr ⟨c,hc⟩
  have hrsmall : ((Ω.erase c) \ K).card ≤ 2 := by omega
  have hrlarge : 2 ≤ ((Ω.erase c) \ K).card := by
    by_contra hneg
    have hrle : ((Ω.erase c) \ K).card ≤ 1 := by omega
    interval_cases hr : ((Ω.erase c) \ K).card <;> norm_num at hcount
    · rw [hcount] at hm
      simp at hm
    · omega
  have hre : ((Ω.erase c) \ K).card = 2 := by omega
  rw [hre] at hcount
  norm_num at hcount
  omega

/-- A legal family of at least two crooked omitters cannot live in a
ground of at most three points, since all nonempty ≤2-point sets are AP. -/
theorem no_two_crooked_omitters_on_tiny_ground
    (Ω : Finset Int) (F : Finset (Finset Int)) (c : Int)
    (hc : c ∈ Ω) (hF : Legal Ω F) (hsmall : Ω.card ≤ 3)
    (hm : 2 ≤ (Avoiders F c).card)
    (hcrooked : ∀ S ∈ Avoiders F c, ¬ IsAP S) : False := by
  classical
  obtain ⟨S,hS,T,hT,hne⟩ := Finset.one_lt_card.mp hm
  have hAP := hF.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne
  obtain ⟨x,hx⟩ := isAP_nonempty hAP
  have hSne : S.Nonempty := ⟨x,(Finset.mem_inter.mp hx).1⟩
  have hsub : S ⊆ Ω.erase c := by
    intro y hy
    exact Finset.mem_erase.mpr ⟨by intro heq; exact (Finset.mem_filter.mp hS).2 (heq ▸ hy),
      hF.1 S (Finset.mem_filter.mp hS).1 hy⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hc] at hcard
  have hScard : S.card ≤ 2 := by omega
  exact hcrooked S hS (nonempty_card_le_two_isAP hSne hScard)

#print axioms strict_extension_count
#print axioms small_ground_ap_core_capacity
#print axioms no_two_crooked_omitters_on_tiny_ground

end JSP233.SmallGround
