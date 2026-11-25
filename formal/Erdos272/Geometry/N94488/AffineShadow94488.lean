module

public import Erdos272.Geometry.AffineLine30
public import Erdos272.Core.OneThird32
public import Erdos272.Arithmetic.Source.APShadowCapacity16858

@[expose] public section

namespace JSP233.AffineShadow94488
open StarCompletion APGeometry AffineLine30 OneThird32 APShadowCapacity16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem map_powerset (c d : ℤ) (hd : 0 < d) (S : Finset ℤ) (k : ℕ) :
    (mapSet c d S).powersetCard k = (S.powersetCard k).image (mapSet c d) := by
  ext P
  constructor
  · intro hP
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hP
    obtain ⟨Q, hQ, he⟩ := exists_preimage_subset c d S P hsub
    have hQc : Q.card = k := by rw [← mapSet_card c d hd Q, he, hcard]
    exact Finset.mem_image.mpr ⟨Q, Finset.mem_powersetCard.mpr ⟨hQ, hQc⟩, he⟩
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQ
    exact Finset.mem_powersetCard.mpr
      ⟨(mapSet_subset_iff c d hd Q S).mpr hsub, by rw [mapSet_card c d hd, hcard]⟩

theorem map_shadow (c d : ℤ) (hd : 0 < d) (U : Finset (Finset ℤ)) :
    APShadow (mapFamily c d U) = (APShadow U).image (mapSet c d) := by
  ext P
  constructor
  · intro hP
    obtain ⟨S, hS, hPS⟩ := Finset.mem_biUnion.mp hP
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    rw [map_powerset c d hd T 3] at hPS
    obtain ⟨Q, hQ, he⟩ := Finset.mem_image.mp hPS
    exact Finset.mem_image.mpr ⟨Q, Finset.mem_biUnion.mpr ⟨T, hT, hQ⟩, he⟩
  · intro hP
    obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨T, hT, hQT⟩ := Finset.mem_biUnion.mp hQ
    apply Finset.mem_biUnion.mpr
    refine ⟨mapSet c d T, Finset.mem_image.mpr ⟨T, hT, rfl⟩, ?_⟩
    rw [map_powerset c d hd T 3]
    exact Finset.mem_image.mpr ⟨Q, hQT, rfl⟩

theorem map_shadow_card (c d : ℤ) (hd : 0 < d) (U : Finset (Finset ℤ)) :
    (APShadow (mapFamily c d U)).card = (APShadow U).card := by
  rw [map_shadow c d hd]
  exact Finset.card_image_of_injective _ (mapSet_injective c d hd)

theorem map_parity_index (p : ℤ) (S : Finset ℤ) :
    mapSet p 2 (ParityIndex p S) = S.filter (fun x => (x-p)%2 = 0) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    have hm := (mem_parityIndex p x S).mp hx
    exact Finset.mem_filter.mpr ⟨hm, by dsimp only [affine]; omega⟩
  · intro hy
    obtain ⟨hyS, hym⟩ := Finset.mem_filter.mp hy
    refine Finset.mem_image.mpr ⟨(y-p)/2, ?_, ?_⟩
    · rw [mem_parityIndex]
      convert hyS using 1 <;> omega
    · dsimp only [affine]
      omega

theorem map_parity_index_of_phase {p : ℤ} {S : Finset ℤ}
    (hphase : ∀ x ∈ S, (x-p)%2 = 0) :
    mapSet p 2 (ParityIndex p S) = S := by
  rw [map_parity_index]
  exact Finset.filter_eq_self.mpr hphase

theorem parity_family {p : ℤ} {U : Finset (Finset ℤ)}
    (hphase : ∀ S ∈ U, ∀ x ∈ S, (x-p)%2 = 0) :
    mapFamily p 2 (U.image (ParityIndex p)) = U := by
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hT
    simpa only [map_parity_index_of_phase (hphase V hV)] using hV
  · intro hS
    exact Finset.mem_image.mpr ⟨ParityIndex p S,
      Finset.mem_image.mpr ⟨S, hS, rfl⟩, map_parity_index_of_phase (hphase S hS)⟩

theorem interval_eq_icc {S : Finset ℤ} (hne : S.Nonempty) (hi : OneThird32.Interval S) :
    ∃ a b : ℤ, S = Finset.Icc a b := by
  refine ⟨S.min' hne, S.max' hne, ?_⟩
  ext x
  constructor
  · intro hx
    exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ x hx, Finset.le_max' _ x hx⟩
  · intro hx
    have hh := Finset.mem_Icc.mp hx
    exact hi _ (Finset.min'_mem _ hne) _ (Finset.max'_mem _ hne) x hh.1 hh.2

#print axioms map_powerset
#print axioms map_shadow
#print axioms map_shadow_card
#print axioms map_parity_index
#print axioms map_parity_index_of_phase
#print axioms parity_family
#print axioms interval_eq_icc
end
end JSP233.AffineShadow94488
