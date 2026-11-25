module

public import Erdos272.Counting.N88404.GapCodes88404

@[expose] public section

namespace JSP233.ResidueDensity88404
open StarCompletion OrderedShadow88404 ResidueMaps88404 GapCodes88404
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem upper_scaled {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (hT : T ⊆ (Ground M).powersetCard 3) (hclosed : Closed T) :
    (q : ℝ)^3*((ResidueCodes M q r T).card : ℝ) ≤ T.card+(q : ℝ)*(M : ℝ)^2/2 := by
  let Good := (ResidueCodes M q r T).filter (fun p => 2*(q : ℤ) ≤ p.2.2-p.2.1)
  let domain := Good ×ˢ Offsets q
  let f := fun v : PointTriple × PointTriple => Expand v.1 v.2
  have hf : Set.MapsTo f domain (Codes M T) := by
    intro v hv
    obtain ⟨hp, ha⟩ := Finset.mem_product.mp hv
    obtain ⟨hp, hgap⟩ := Finset.mem_filter.mp hp
    exact expand_mem hq hclosed hp ha hgap
  have hi : Set.InjOn f domain := by
    intro v hv w hw he
    obtain ⟨hp, ha⟩ := Finset.mem_product.mp hv
    obtain ⟨hs, hb⟩ := Finset.mem_product.mp hw
    have hpR := (mem_residue.mp (Finset.mem_filter.mp hp).1).2
    have hsR := (mem_residue.mp (Finset.mem_filter.mp hs).1).2
    obtain ⟨h₁, h₂⟩ := expand_injective hpR hsR ha hb he
    exact Prod.ext h₁ h₂
  have hc := Finset.card_le_card_of_injOn f hf hi
  have hcNat : Good.card*q^3 ≤ T.card := by
    simpa only [domain, Finset.card_product, offsets_card, codes_card hT] using hc
  have hcR : (Good.card : ℝ)*(q : ℝ)^3 ≤ T.card := by exact_mod_cast hcNat
  have hsub : ResidueCodes M q r T ⊆ Good ∪ BadResidue M q r T := by
    intro p hp
    by_cases hg : 2*(q : ℤ) ≤ p.2.2-p.2.1
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hg⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, by omega⟩)
  have hs := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hsR : ((ResidueCodes M q r T).card : ℝ) ≤
      Good.card+(BadResidue M q r T).card := by exact_mod_cast hs
  have hsm := mul_le_mul_of_nonneg_left hsR (pow_nonneg (Nat.cast_nonneg (α := ℝ) q) 3)
  have hb := bad_residue_real (M := M) r T hq
  have hbm := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (α := ℝ) q)
  nlinarith only [hcR, hsm, hbm]

theorem lower_scaled {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (hT : T ⊆ (Ground M).powersetCard 3) (hclosed : Closed T) :
    (T.card : ℝ) ≤ (q : ℝ)^3*((ResidueCodes M q r T).card : ℝ)+
      3*(q : ℝ)*(M : ℝ)^2/2 := by
  let Good := (Codes M T).filter
    (fun p => (q : ℤ) ≤ p.2.1-p.1 ∧ 2*(q : ℤ) ≤ p.2.2-p.2.1)
  let f := fun p : PointTriple => (Round q r p, RoundOffsets q r p)
  have hf : Set.MapsTo f Good
      (↑(ResidueCodes M q r T ×ˢ Offsets q) : Set (PointTriple × PointTriple)) := by
    intro p hp
    obtain ⟨hp, hfirst, hsecond⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_product.mpr ⟨round_mem hq hclosed hp hfirst hsecond,
      round_offsets_mem hq r p⟩
  have hc := Finset.card_le_card_of_injOn f hf (round_record_injective q r).injOn
  have hcNat : Good.card ≤ (ResidueCodes M q r T).card*q^3 := by
    simpa only [Finset.card_product, offsets_card] using hc
  have hcR : (Good.card : ℝ) ≤ (ResidueCodes M q r T).card*(q : ℝ)^3 :=
    by exact_mod_cast hcNat
  have hsub : Codes M T ⊆ Good ∪ (BadGap M q T false ∪ BadGap M (2*q) T true) := by
    intro p hp
    by_cases hfirst : (q : ℤ) ≤ p.2.1-p.1
    · by_cases hsecond : 2*(q : ℤ) ≤ p.2.2-p.2.1
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, hfirst, hsecond⟩)
      · apply Finset.mem_union_right
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨hp, by change p.2.2-p.2.1 < ((2*q : ℕ) : ℤ); push_cast; omega⟩
    · apply Finset.mem_union_right
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hp, by change p.2.1-p.1 < (q : ℤ); omega⟩
  have hs := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hs' := Finset.card_union_le (BadGap M q T false) (BadGap M (2*q) T true)
  rw [codes_card hT] at hs
  have hsR : (T.card : ℝ) ≤ Good.card+(BadGap M q T false).card+
      (BadGap M (2*q) T true).card := by exact_mod_cast (show
      T.card ≤ Good.card+(BadGap M q T false).card+(BadGap M (2*q) T true).card by omega)
  have hb₁ := bad_gap_real M q T false
  have hb₂ := bad_gap_real M (2*q) T true
  push_cast at hb₂
  nlinarith only [hcR, hsR, hb₁, hb₂]

theorem residue_density {M q : ℕ} {r : ℤ} {T : Finset (Finset ℤ)}
    (hq : 0 < q) (hT : T ⊆ (Ground M).powersetCard 3) (hclosed : Closed T) :
    (T.card : ℝ)/(q : ℝ)^3-3*(M : ℝ)^2/(2*(q : ℝ)^2) ≤
      (ResidueCodes M q r T).card ∧
    ((ResidueCodes M q r T).card : ℝ) ≤
      (T.card : ℝ)/(q : ℝ)^3+(M : ℝ)^2/(2*(q : ℝ)^2) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hq3 : (0 : ℝ) < (q : ℝ)^3 := pow_pos hqR 3
  have hu := upper_scaled (r := r) hq hT hclosed
  have hl := lower_scaled (r := r) hq hT hclosed
  constructor
  · apply sub_le_iff_le_add.mpr
    apply (div_le_iff₀ hq3).mpr
    have he : (((ResidueCodes M q r T).card : ℝ)+
        3*(M : ℝ)^2/(2*(q : ℝ)^2))*(q : ℝ)^3 =
        (q : ℝ)^3*((ResidueCodes M q r T).card : ℝ)+3*(q : ℝ)*(M : ℝ)^2/2 := by
      field_simp [hqR.ne']
      <;> ring
    rw [he]
    exact hl
  · have he : (T.card : ℝ)/(q : ℝ)^3+(M : ℝ)^2/(2*(q : ℝ)^2) =
        ((T.card : ℝ)+(q : ℝ)*(M : ℝ)^2/2)/(q : ℝ)^3 := by
      field_simp [hqR.ne']
      <;> ring
    rw [he]
    apply (le_div_iff₀ hq3).mpr
    nlinarith only [hu]

#print axioms upper_scaled
#print axioms lower_scaled
#print axioms residue_density
end
end JSP233.ResidueDensity88404
