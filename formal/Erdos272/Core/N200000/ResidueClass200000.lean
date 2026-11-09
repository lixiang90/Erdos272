module

public import Erdos272.Core.N200000.PrimePairEvents200000
public import Erdos272.Core.N200000.ResiduePeriod200000
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Uniform floor/ceiling census for one residue in any translated
integer index interval. Bounds keep the same interval for all primes. -/
namespace JSP233.ResidueClass200000
open StarCompletion APGeometry SourceBridge208 FarSlot112 RunTrace200000 ResiduePeriod200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Class (l a q : ℕ) (u : ℤ) : Finset ℕ :=
  (Finset.Ico l (l + a)).filter (fun i => (q : ℤ) ∣ (i : ℤ) - u)

theorem class_image (l a q : ℕ) (u : ℤ) :
    (Class l a q u).image (fun i : ℕ => (i : ℤ)) =
      Segment (q : ℤ) u (l : ℤ) (((l + a : ℕ) : ℤ) - 1) := by
  ext x
  rw [Finset.mem_image, mem_segment]
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨hiI, hdiv⟩ := Finset.mem_filter.mp hi
    obtain ⟨hli, hia⟩ := Finset.mem_Ico.mp hiI
    exact ⟨by exact_mod_cast hli, by omega, hdiv⟩
  · rintro ⟨hlo, hhi, hdiv⟩
    have hx0 : 0 ≤ x := (Int.natCast_nonneg l).trans hlo
    have hcast : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    refine ⟨x.toNat, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩, hcast⟩
    simpa only [hcast] using hdiv

theorem class_card_upper (l a : ℕ) {q : ℕ} (hq : 0 < q) (u : ℤ) :
    (Class l a q u).card ≤ (a + q - 1) / q := by
  rcases Nat.eq_zero_or_pos a with hzero | hapos
  · simp [Class, hzero]
  let T := (Class l a q u).image (fun i : ℕ => (i : ℤ))
  let R := Segment 1 0 (l : ℤ) (((l + a : ℕ) : ℤ) - 1)
  have hT : APAt (q : ℤ) u T := by
    dsimp only [T]
    rw [class_image]
    exact segment_APAt (by exact_mod_cast hq)
  have hR : APAt 1 0 R := segment_APAt (by decide)
  have hTR : T ⊆ R := by
    intro x hx
    change x ∈ (Class l a q u).image (fun i : ℕ => (i : ℤ)) at hx
    rw [class_image] at hx
    have hxT := mem_segment.mp hx
    exact mem_segment.mpr ⟨hxT.1, hxT.2.1, one_dvd _⟩
  have hRI : R = Finset.Icc (l : ℤ) (((l + a : ℕ) : ℤ) - 1) := by
    ext x
    simp only [R, Segment, Finset.mem_filter, Finset.mem_Icc, one_dvd, and_true]
  have hcardR : R.card = a := by
    have hh : (R.card : ℤ) = a := by
      rw [hRI, Nat.cast_add]
      have hc := Int.card_Icc_of_le (a := (l : ℤ)) (b := (l : ℤ) + (a : ℤ) - 1) (by omega)
      omega
    exact_mod_cast hh
  have hb := coarse_subAP_card hT hR hTR hcardR.le hq (by ring)
  have hinj : Function.Injective (fun i : ℕ => (i : ℤ)) := by
    intro i j he
    change (i : ℤ) = (j : ℤ) at he
    exact_mod_cast he
  simpa only [T, Finset.card_image_of_injective _ hinj] using hb

theorem class_card_lower (l a : ℕ) {q : ℕ} (hq : 0 < q) (u : ℤ) :
    a / q ≤ (Class l a q u).card := by
  let delta := Residue q (u - (l : ℤ))
  have hdelta : delta < q := residue_lt hq _
  have hdeltaDiv : (q : ℤ) ∣ (delta : ℤ) - (u - (l : ℤ)) := by
    apply (residue_eq_iff hq).mp
    exact residue_nat hq hdelta
  let f : ℕ → ℕ := fun j => l + j * q + delta
  have hmap : ∀ j ∈ Finset.range (a / q), f j ∈ Class l a q u := by
    intro j hj
    have hjs : j + 1 ≤ a / q := by have := Finset.mem_range.mp hj; omega
    have hmul := Nat.mul_le_mul_left q hjs
    have hqa : q * (a / q) ≤ a := Nat.mul_div_le a q
    have hfI : f j ∈ Finset.Ico l (l + a) := by
      apply Finset.mem_Ico.mpr
      dsimp only [f]
      constructor
      · omega
      · nlinarith only [hmul, hqa, hdelta]
    apply Finset.mem_filter.mpr
    refine ⟨hfI, ?_⟩
    have he : (f j : ℤ) - u = (j : ℤ) * q + ((delta : ℤ) - (u - (l : ℤ))) := by
      dsimp only [f]
      push_cast
      ring
    rw [he]
    exact dvd_add (dvd_mul_left _ _) hdeltaDiv
  have hinj : Function.Injective f := by
    intro i j he
    dsimp only [f] at he
    nlinarith only [he, hq]
  have hc := Finset.card_le_card_of_injOn f hmap hinj.injOn
  simpa only [Finset.card_range] using hc

#print axioms class_image
#print axioms class_card_upper
#print axioms class_card_lower
end
end JSP233.ResidueClass200000
