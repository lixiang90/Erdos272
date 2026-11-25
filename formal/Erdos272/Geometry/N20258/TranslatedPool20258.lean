module

public import Erdos272.Geometry.AffineLine30
public import Erdos272.Resources.IntrinsicTriples208
public import Erdos272.Foundation.PrimeKernel
public import Erdos272.Foundation.JSP233

@[expose] public section

/-! Padding the ground set admits several translations of the same family.
Legality, cardinalities, and intrinsic triples survive these translations.
The central triple is allowed to change when the translation changes. -/
namespace JSP233.TranslatedPool20258

open StarCompletion AffineLine30 IntrinsicTriples208
open scoped Classical
noncomputable section
set_option autoImplicit false

theorem mem_pool_map_iff (c d : ℤ) (hd : 0 < d) (Q S : Finset ℤ) :
    mapSet c d Q ∈ Pool (mapSet c d S) ↔ Q ∈ Pool S := by
  rw [mem_pool, mem_pool, mapSet_subset_iff c d hd, mapSet_card c d hd]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · intro h ⟨P,hAP,hQP,hPS⟩
    exact h ⟨mapSet c d P, affine_isAP c d hd hAP,
      (mapSet_subset_iff c d hd Q P).mpr hQP, (mapSet_subset_iff c d hd P S).mpr hPS⟩
  · intro h ⟨T,hAP,hQT,hTS⟩
    obtain ⟨P,hPS,rfl⟩ := exists_preimage_subset c d S T hTS
    exact h ⟨P,(affine_isAP_iff c d hd P).mp hAP,(mapSet_subset_iff c d hd Q P).mp hQT,hPS⟩

theorem pool_map (c d : ℤ) (hd : 0 < d) (S : Finset ℤ) :
    Pool (mapSet c d S) = mapFamily c d (Pool S) := by
  ext T
  constructor
  · intro hT
    obtain ⟨Q,_,rfl⟩ := exists_preimage_subset c d S T (mem_pool.mp hT).1
    exact Finset.mem_image.mpr ⟨Q,(mem_pool_map_iff c d hd Q S).mp hT,rfl⟩
  · intro hT
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hT
    exact (mem_pool_map_iff c d hd Q S).mpr hQ

theorem padded_legal {N U j : ℕ} {F : Finset (Finset ℤ)}
    (hj : j+N ≤ U) (hF : Legal (Ground N) F) : Legal (Ground U) (mapFamily j 1 F) := by
  constructor
  · intro T hT y hy
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hx1,hxN⟩ := (mem_ground N x).mp (hF.1 S hS hx)
    apply (mem_ground U _).mpr
    simp only [affine,one_mul]
    omega
  · intro A hA B hB hne
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hB
    have hint : mapSet (j : ℤ) 1 (S ∩ T) = mapSet j 1 S ∩ mapSet j 1 T :=
      Finset.image_inter S T (affine_injective (j : ℤ) 1 (by decide))
    rw [← hint]
    exact affine_isAP _ _ (by decide) (hF.2 S hS T hT (fun h => hne (h ▸ rfl)))

/-- An intrinsic triple of an actual member lies in the indicated interval. -/
def Central (F : Finset (Finset ℤ)) (a b : ℤ) : Prop :=
  ∃ S ∈ F, ∃ Q ∈ Pool S, Q ⊆ Finset.Icc a b

private theorem map_subset_interval (j a b : ℤ) (Q : Finset ℤ) :
    mapSet j 1 Q ⊆ Finset.Icc a b ↔ Q ⊆ Finset.Icc (a-j) (b-j) := by
  constructor
  · intro h x hx
    have hy := Finset.mem_Icc.mp (h ((mem_mapSet j 1 (by decide) Q x).mpr hx))
    simp only [affine,one_mul] at hy
    exact Finset.mem_Icc.mpr (by omega)
  · intro h y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    have hz := Finset.mem_Icc.mp (h hx)
    simp only [affine,one_mul,Finset.mem_Icc]
    omega

theorem central_translate_iff (F : Finset (Finset ℤ)) (j a b : ℤ) :
    Central (mapFamily j 1 F) a b ↔ Central F (a-j) (b-j) := by
  constructor
  · rintro ⟨T,hT,P,hP,hPW⟩
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    rw [pool_map j 1 (by decide) S] at hP
    obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hP
    exact ⟨S,hS,Q,hQ,(map_subset_interval j a b Q).mp hPW⟩
  · rintro ⟨S,hS,Q,hQ,hQW⟩
    exact ⟨mapSet j 1 S,Finset.mem_image.mpr ⟨S,hS,rfl⟩,mapSet j 1 Q,
      (mem_pool_map_iff j 1 (by decide) Q S).mpr hQ,(map_subset_interval j a b Q).mpr hQW⟩

/-- A unit interval covering any of the witnessed windows cannot be a
member. Its intersection with the witness would cover an intrinsic triple. -/
theorem interval_excluded {N : ℕ} {F : Finset (Finset ℤ)} {a b i t : ℤ}
    (hF : Legal (Ground N) F) (hw : Central F a b)
    (hit : i ≤ t) (hia : i ≤ a) (hbt : b ≤ t) : Finset.Icc i t ∉ F := by
  obtain ⟨S,hS,Q,hQ,hQW⟩ := hw
  intro hI
  have hQI : Q ⊆ Finset.Icc i t := hQW.trans (Finset.Icc_subset_Icc hia hbt)
  have he := pool_private hF hS hI hQ hQI
  exact (mem_pool.mp hQ).2.2 ⟨Finset.Icc i t,PrimeKernel.interval_isAP i t hit,hQI,he ▸ Finset.Subset.rfl⟩

end
end JSP233.TranslatedPool20258
