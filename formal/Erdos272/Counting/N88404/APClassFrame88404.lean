module

public import Erdos272.Geometry.N88404.AffineIndex88404
public import Erdos272.Counting.N88404.APClasses88404
public import Erdos272.Arithmetic.N291012.UnitShadowGeometry291012

@[expose] public section

namespace JSP233.APClassFrame88404
open StarCompletion APGeometry AffineLine30 AffineIndex88404 APClasses88404
open APShadowCapacity16858 AffineShadow94488 UnitShadowGeometry291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Frame (N d : ℕ) (U : Finset (Finset ℤ)) where
  offset : ℤ
  size : ℕ
  family : Finset (Finset ℤ)
  root : ℤ
  size_positive : 1 ≤ size
  mapped : mapFamily offset (d : ℤ) family = U
  ground : ∀ S ∈ family, S ⊆ Ground size
  root_ground : root ∈ Ground size
  common_root : ∀ S ∈ family, root ∈ S
  intervals : ∀ S ∈ family, ∃ a b : ℤ, S = Finset.Icc a b
  card_two : ∀ S ∈ family, 2 ≤ S.card
  span : (d : ℝ)*((size : ℝ)-1) ≤ (N : ℝ)-1

theorem frame_nonempty {N d : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hd : 0 < d) (hF : Legal (Ground N) F) :
    Nonempty (Frame N d (StepAP F d)) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  by_cases hne : (StepAP F d).Nonempty
  · let U := StepAP F d
    obtain ⟨c, hc, hroot⟩ := APClasses88404.common_root hF hne
    let carrier := U.biUnion (fun S => S)
    obtain ⟨S₀, hS₀⟩ := hne
    have hcC : c ∈ carrier := Finset.mem_biUnion.mpr ⟨S₀, hS₀, hroot S₀ hS₀⟩
    have hCne : carrier.Nonempty := ⟨c, hcC⟩
    have hgroundC : carrier ⊆ Ground N := by
      intro x hx
      obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
      exact hF.1 S (APClasses88404.subset F d hS) hxS
    have hphaseC : ∀ x ∈ carrier, (d : ℤ) ∣ x-c := by
      intro x hx
      obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨q, hq⟩ := ap_at hS
      exact apAt_dvd_sub hq (hroot S hS) hxS
    let lo := carrier.min' hCne
    let hi := carrier.max' hCne
    have hlo : lo ∈ carrier := Finset.min'_mem _ hCne
    have hhi : hi ∈ carrier := Finset.max'_mem _ hCne
    have hlow : ∀ x ∈ carrier, lo ≤ x := fun x hx => Finset.min'_le _ x hx
    have hhigh : ∀ x ∈ carrier, x ≤ hi := fun x hx => Finset.le_max' _ x hx
    have hphaseLo : ∀ x ∈ carrier, (d : ℤ) ∣ x-lo := by
      intro x hx
      have hh := dvd_sub (hphaseC x hx) (hphaseC lo hlo)
      have he : (x-c)-(lo-c) = x-lo := by ring
      rw [he] at hh
      exact hh
    have hspanDiv := hphaseLo hi hhi
    have hquot : 0 ≤ (hi-lo)/(d : ℤ) :=
      Int.ediv_nonneg (by have hh := hlow hi hhi; omega) hdZ.le
    let M := ((hi-lo)/(d : ℤ)).toNat+1
    have hM : 1 ≤ M := by dsimp only [M]; omega
    have hMint : (M : ℤ) = (hi-lo)/(d : ℤ)+1 := by
      dsimp only [M]
      push_cast
      rw [Int.toNat_of_nonneg hquot]
    have hspan : (d : ℤ)*((M : ℤ)-1) = hi-lo := by
      rw [hMint]
      have hh := Int.ediv_mul_cancel hspanDiv
      nlinarith only [hh]
    let p := lo-(d : ℤ)
    let V := U.image (Index p (d : ℤ))
    have hphase : ∀ S ∈ U, ∀ x ∈ S, (d : ℤ) ∣ x-p := by
      intro S hS x hx
      have hh := hphaseLo x (Finset.mem_biUnion.mpr ⟨S, hS, hx⟩)
      have hsum := dvd_add hh (dvd_refl (d : ℤ))
      have he : (x-lo)+(d : ℤ) = x-p := by dsimp only [p]; ring
      rw [he] at hsum
      exact hsum
    have hmap : mapFamily p (d : ℤ) V = U := index_family hdZ hphase
    have hground : ∀ T ∈ V, T ⊆ Ground M := by
      intro T hT x hx
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      have hxS := (mem_index hdZ).mp hx
      have hxC : p+(d : ℤ)*x ∈ carrier := Finset.mem_biUnion.mpr ⟨S, hS, hxS⟩
      have hxlo := hlow _ hxC
      have hxhi := hhigh _ hxC
      dsimp only [p] at hxlo hxhi
      apply (mem_ground M x).mpr
      constructor
      · apply (mul_le_mul_iff_right₀ hdZ).mp
        nlinarith only [hxlo]
      · apply (mul_le_mul_iff_right₀ hdZ).mp
        nlinarith only [hxhi, hspan]
    let j := (c-p)/(d : ℤ)
    have hcp : (d : ℤ) ∣ c-p := hphase S₀ hS₀ c (hroot S₀ hS₀)
    have hj : p+(d : ℤ)*j = c := by
      have hh := Int.ediv_mul_cancel hcp
      dsimp only [j]
      nlinarith only [hh]
    have hrootV : ∀ T ∈ V, j ∈ T := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      rw [mem_index hdZ, hj]
      exact hroot S hS
    have hmemV : Index p (d : ℤ) S₀ ∈ V := Finset.mem_image.mpr ⟨S₀, hS₀, rfl⟩
    have hjground : j ∈ Ground M := hground _ hmemV (hrootV _ hmemV)
    have htwo : ∀ T ∈ V, 2 ≤ T.card := by
      intro T hT
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      have hh := mapSet_card p (d : ℤ) hdZ (Index p (d : ℤ) S)
      rw [map_index_of_phase hdZ (hphase S hS)] at hh
      rw [← hh]
      exact APClasses88404.card_two hS
    have hiV : ∀ T ∈ V, ∃ a b : ℤ, T = Finset.Icc a b := by
      intro T hT
      have ht := htwo T hT
      have htne : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
      obtain ⟨q, hq⟩ := ap_at hS
      exact interval_eq_icc htne (index_interval hdZ hq)
    have hspanR : (d : ℝ)*((M : ℝ)-1) ≤ (N : ℝ)-1 := by
      have hl := (mem_ground N lo).mp (hgroundC hlo)
      have hh := (mem_ground N hi).mp (hgroundC hhi)
      have hz : (d : ℤ)*((M : ℤ)-1) ≤ (N : ℤ)-1 := by linarith only [hspan, hl.1, hh.2]
      exact_mod_cast hz
    exact ⟨⟨p, M, V, j, hM, hmap, hground, hjground, hrootV, hiV, htwo, hspanR⟩⟩
  · have he : StepAP F d = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨⟨0, 1, ∅, 1, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp only [mapFamily, Finset.image_empty, he]
    · simp
    · exact (mem_ground 1 1).mpr ⟨by norm_num, by norm_num⟩
    · simp
    · simp
    · simp
    · norm_num
      exact hN

theorem geometry {N d : ℕ} {U : Finset (Finset ℤ)} (f : Frame N d U) (hd : 0 < d) :
    ∃ y : ℝ, 0 ≤ y ∧ 2*y ≤ (f.size : ℝ)-1 ∧
      (U.card : ℝ) ≤ y^2+((f.size : ℝ)-1) ∧
      8*y^3 ≤ 6*((APShadow U).card : ℝ)+((f.size : ℝ)-1) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  obtain ⟨y, hy, hyN, hcount, hmass⟩ :=
    interval_geometry f.root_ground f.ground f.common_root f.intervals f.card_two
  have hcast : ((f.size-1 : ℕ) : ℝ) = (f.size : ℝ)-1 := by
    rw [Nat.cast_sub f.size_positive, Nat.cast_one]
  rw [hcast] at hyN hcount hmass
  have hcard : f.family.card = U.card := by
    have hh := mapFamily_card f.offset (d : ℤ) hdZ f.family
    rw [f.mapped] at hh
    exact hh.symm
  have hshadow : (APShadow f.family).card = (APShadow U).card := by
    have hh := map_shadow_card f.offset (d : ℤ) hdZ f.family
    rw [f.mapped] at hh
    exact hh.symm
  have hw : 0 ≤ (f.size : ℝ)-1 := by
    have hh : (1 : ℝ) ≤ f.size := by exact_mod_cast f.size_positive
    linarith only [hh]
  have hyw : 2*y ≤ (f.size : ℝ)-1 := by
    by_contra hn
    have hp := mul_pos (show 0 < 2*y-((f.size : ℝ)-1) by linarith only [hn])
      (show 0 < 2*y+((f.size : ℝ)-1) by linarith only [hy, hw, hn])
    nlinarith only [hp, hyN]
  rw [hcard] at hcount
  rw [hshadow] at hmass
  exact ⟨y, hy, hyw, hcount, hmass⟩

#print axioms frame_nonempty
#print axioms geometry
end
end JSP233.APClassFrame88404
