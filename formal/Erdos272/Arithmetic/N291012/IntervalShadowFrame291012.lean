module

public import Erdos272.Arithmetic.Source.IntervalFamilyEndpoints16858
public import Erdos272.Resources.UnitShadowGrid218
public import Erdos272.Counting.NonIntervalAP47
public import Erdos272.Resources.APResidual208
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.IntervalShadowFrame291012
open StarCompletion APGeometry APCount41 WitnessInterval43
open APShadowCapacity16858 IntervalMixedShadow16858 IntervalFamilyEndpoints16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actual_frame {N : ℕ} {c : ℤ} {U : Finset (Finset ℤ)}
    (hc : c ∈ Ground N) (hground : ∀ S ∈ U, S ⊆ Ground N)
    (hroot : ∀ S ∈ U, c ∈ S) (hi : ∀ S ∈ U, ∃ a b : ℤ, S = Finset.Icc a b)
    (htwo : ∀ S ∈ U, 2 ≤ S.card) :
    ∃ A B : ℕ, A+B ≤ N-1 ∧
      Pairs c A B U ⊆ (Finset.range A).product (Finset.range B) ∧
      (U.card : ℝ) ≤ (A : ℝ)+B+(Pairs c A B U).card ∧
      (A : ℝ)^3+(B : ℝ)^3-A-B+
        6*(∑ p ∈ Pairs c A B U, ((p.1 : ℝ)+p.2+1)) ≤ 6*((APShadow U).card : ℝ) := by
  obtain ⟨l, r, hlc, hcr, hl, hr, hall⟩ := rooted_interval_envelope hroot hi
  let A := (c-l).toNat
  let B := (r-c).toNat
  have hA : (A : ℤ) = c-l := Int.toNat_of_nonneg (by omega)
  have hB : (B : ℤ) = r-c := Int.toNat_of_nonneg (by omega)
  have heL : c-A = l := by omega
  have heR : c+B = r := by omega
  have hcN := (mem_ground N c).mp hc
  have hlow : 1 ≤ l := by
    rcases hl with he | ⟨S, hSU, _hAP, hsub⟩
    · omega
    · exact ((mem_ground N l).mp
        (hground S hSU (hsub (Finset.mem_Icc.mpr ⟨le_rfl, hlc⟩)))).1
  have hhigh : r ≤ (N : ℤ) := by
    rcases hr with he | ⟨S, hSU, _hAP, hsub⟩
    · omega
    · exact ((mem_ground N r).mp
        (hground S hSU (hsub (Finset.mem_Icc.mpr ⟨hcr, le_rfl⟩)))).2
  have henv : ∀ S ∈ U, S ⊆ Finset.Icc (c-A) (c+B) := by
    intro S hSU
    obtain ⟨a, b, hla, _hac, _hcb, hbr, he⟩ := hall S hSU
    rw [heL, heR, he]
    intro x hx
    have hh := Finset.mem_Icc.mp hx
    exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hleft : (Finset.Icc (c-A) c).powersetCard 3 ⊆ APShadow U := by
    rw [heL]
    intro Q hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQ
    rcases hl with he | ⟨S, hSU, _hAP, hcover⟩
    · rw [he, Finset.Icc_self] at hsub
      have hh := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hcard] at hh
      omega
    · exact Finset.mem_biUnion.mpr ⟨S, hSU,
        Finset.mem_powersetCard.mpr ⟨hsub.trans hcover, hcard⟩⟩
  have hright : (Finset.Icc c (c+B)).powersetCard 3 ⊆ APShadow U := by
    rw [heR]
    intro Q hQ
    obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp hQ
    rcases hr with he | ⟨S, hSU, _hAP, hcover⟩
    · rw [he, Finset.Icc_self] at hsub
      have hh := Finset.card_le_card hsub
      simp only [Finset.card_singleton, hcard] at hh
      omega
    · exact Finset.mem_biUnion.mpr ⟨S, hSU,
        Finset.mem_powersetCard.mpr ⟨hsub.trans hcover, hcard⟩⟩
  have hcount : (U.card : ℝ) ≤ (A : ℝ)+B+(Pairs c A B U).card := by
    exact_mod_cast actual_count_bound henv hroot hi htwo
  have hshadow := actual_shadow_lower (D := Pairs c A B U) hleft hright
    (pairs_cover (A := A) (B := B) hi)
  have hshadowR : ((A+1).choose 3 : ℝ)+((B+1).choose 3 : ℝ)+
      (∑ p ∈ Pairs c A B U, ((p.1 : ℝ)+p.2+1)) ≤ ((APShadow U).card : ℝ) := by
    exact_mod_cast hshadow
  rw [APResidual208.cast_choose_three, APResidual208.cast_choose_three] at hshadowR
  push_cast at hshadowR
  refine ⟨A, B, by omega, Finset.filter_subset _ _, hcount, ?_⟩
  nlinarith only [hshadowR]

#print axioms actual_frame
end
end JSP233.IntervalShadowFrame291012
