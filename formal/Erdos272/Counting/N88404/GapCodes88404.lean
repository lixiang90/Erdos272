module

public import Erdos272.Counting.N88404.ResidueMaps88404
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section

namespace JSP233.GapCodes88404
open StarCompletion OrderedShadow88404 ResidueMaps88404 ResidueCard88404
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def Gap (second : Bool) (p : PointTriple) : ℤ :=
  if second then p.2.2-p.2.1 else p.2.1-p.1

def BadGap (M L : ℕ) (T : Finset (Finset ℤ)) (second : Bool) : Finset PointTriple :=
  (Codes M T).filter (fun p => Gap second p < L)

def PairCode (p : PointTriple) : Finset ℤ := {p.1,p.2.2}

theorem pair_mem {A : Finset ℤ} {x y : ℤ} (hx : x ∈ A) (hy : y ∈ A) (hxy : x < y) :
    ({x,y} : Finset ℤ) ∈ A.powersetCard 2 := by
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_, ?_⟩
  · intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl <;> assumption
  · simp [ne_of_lt hxy]

theorem pair_count_bound (A : Finset ℤ) :
    ((A.powersetCard 2).card : ℝ) ≤ (A.card : ℝ)^2/2 := by
  rw [Finset.card_powersetCard, Nat.cast_choose_two]
  have hn : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  nlinarith only [hn]

theorem bad_gap_card (M L : ℕ) (T : Finset (Finset ℤ)) (second : Bool) :
    (BadGap M L T second).card ≤ (Ground M).card.choose 2*L := by
  let f := fun p : PointTriple => (PairCode p, (Gap second p).toNat)
  have hf : Set.MapsTo f (BadGap M L T second)
      (↑((Ground M).powersetCard 2 ×ˢ Finset.range L) : Set (Finset ℤ × ℕ)) := by
    intro p hp
    obtain ⟨hp, hgap⟩ := Finset.mem_filter.mp hp
    obtain ⟨ha, hb, hc, hsort, hT⟩ := mem_codes.mp hp
    dsimp only [Sorted] at hsort
    apply Finset.mem_product.mpr
    refine ⟨pair_mem ha hc (hsort.1.trans hsort.2), Finset.mem_range.mpr ?_⟩
    dsimp only [f, Gap] at *
    cases second <;> simp only [Bool.false_eq_true, if_false, if_true] at * <;> omega
  have hi : Set.InjOn f (BadGap M L T second) := by
    intro p hp s hs he
    have hps := (mem_codes.mp (Finset.mem_filter.mp hp).1).2.2.2.1
    have hss := (mem_codes.mp (Finset.mem_filter.mp hs).1).2.2.2.1
    dsimp only [Sorted] at hps hss
    have hpairs := congrArg Prod.fst he
    have hgaps := congrArg Prod.snd he
    obtain ⟨hleft, hright⟩ := sorted_pair_injective
      (hps.1.trans hps.2) (hss.1.trans hss.2) hpairs
    apply Prod.ext hleft
    apply Prod.ext ?_ hright
    dsimp only [f, Gap] at hgaps
    cases second <;> simp only [Bool.false_eq_true, if_false, if_true] at hgaps <;> omega
  have hh := Finset.card_le_card_of_injOn f hf hi
  simpa only [Finset.card_product, Finset.card_powersetCard, Finset.card_range] using hh

theorem bad_gap_real (M L : ℕ) (T : Finset (Finset ℤ)) (second : Bool) :
    ((BadGap M L T second).card : ℝ) ≤ (L : ℝ)*(M : ℝ)^2/2 := by
  have hc : ((BadGap M L T second).card : ℝ) ≤
      ((Ground M).card.choose 2 : ℝ)*L := by exact_mod_cast bad_gap_card M L T second
  have hp := pair_count_bound (Ground M)
  rw [Finset.card_powersetCard, ground_card] at hp
  have hm := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) L)
  rw [ground_card] at hc
  nlinarith only [hc, hm]

def BadResidue (M q : ℕ) (r : ℤ) (T : Finset (Finset ℤ)) : Finset PointTriple :=
  (ResidueCodes M q r T).filter (fun p => p.2.2-p.2.1 < 2*(q : ℤ))

theorem bad_residue_card {M q : ℕ} (r : ℤ) (T : Finset (Finset ℤ)) (hq : 0 < q) :
    (BadResidue M q r T).card ≤ (ShortPhase M q r).card.choose 2 := by
  have hqZ : (0 : ℤ) < q := by exact_mod_cast hq
  have hgap : ∀ p ∈ BadResidue M q r T, p.2.2-p.2.1 = (q : ℤ) := by
    intro p hp
    obtain ⟨hp, hsmall⟩ := Finset.mem_filter.mp hp
    obtain ⟨hcode, hphase⟩ := mem_residue.mp hp
    have hs := (mem_codes.mp hcode).2.2.2.1
    have hd : (q : ℤ) ∣ p.2.2-p.2.1 := by
      have hh := dvd_sub hphase.2.2 hphase.2.1
      have he : (p.2.2-r)-(p.2.1-r) = p.2.2-p.2.1 := by ring
      rw [he] at hh
      exact hh
    exact gap_eq_step hqZ (sub_pos.mpr hs.2) hsmall hd
  let f := fun p : PointTriple => ({p.1,p.2.1} : Finset ℤ)
  have hf : Set.MapsTo f (BadResidue M q r T) ((ShortPhase M q r).powersetCard 2) := by
    intro p hp
    obtain ⟨hcode, hphase⟩ := mem_residue.mp (Finset.mem_filter.mp hp).1
    obtain ⟨ha, hb, hc, hs, hT⟩ := mem_codes.mp hcode
    dsimp only [Sorted] at hs
    have haG := (mem_ground M p.1).mp ha
    have hbG := (mem_ground M p.2.1).mp hb
    have hcG := (mem_ground M p.2.2).mp hc
    have hg := hgap p hp
    apply pair_mem ?_ ?_ hs.1
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨haG.1, by omega⟩, hphase.1⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨hbG.1, by omega⟩, hphase.2.1⟩
  have hi : Set.InjOn f (BadResidue M q r T) := by
    intro p hp s hs he
    have hps := (mem_codes.mp (mem_residue.mp (Finset.mem_filter.mp hp).1).1).2.2.2.1
    have hss := (mem_codes.mp (mem_residue.mp (Finset.mem_filter.mp hs).1).1).2.2.2.1
    obtain ⟨ha, hb⟩ := sorted_pair_injective hps.1 hss.1 he
    have hpq := hgap p hp
    have hsq := hgap s hs
    exact Prod.ext ha (Prod.ext hb (by omega))
  have hh := Finset.card_le_card_of_injOn f hf hi
  simpa only [Finset.card_powersetCard] using hh

theorem bad_residue_real {M q : ℕ} (r : ℤ) (T : Finset (Finset ℤ)) (hq : 0 < q) :
    (q : ℝ)^2*((BadResidue M q r T).card : ℝ) ≤ (M : ℝ)^2/2 := by
  have hc : ((BadResidue M q r T).card : ℝ) ≤ ((ShortPhase M q r).card.choose 2 : ℝ) :=
    by exact_mod_cast bad_residue_card r T hq
  have hp := pair_count_bound (ShortPhase M q r)
  rw [Finset.card_powersetCard] at hp
  have hm := mul_le_mul_of_nonneg_left (hc.trans hp) (sq_nonneg (q : ℝ))
  have hb := short_phase_card (M := M) (r := r) hq
  have hs := mul_nonneg (sub_nonneg.mpr hb)
    (show 0 ≤ (M : ℝ)+(q : ℝ)*(ShortPhase M q r).card by positivity)
  nlinarith only [hm, hs]

#print axioms pair_mem
#print axioms pair_count_bound
#print axioms bad_gap_card
#print axioms bad_gap_real
#print axioms bad_residue_card
#print axioms bad_residue_real
end
end JSP233.GapCodes88404
