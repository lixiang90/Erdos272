module

public import Erdos272.Resources.ActualGrid212
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section
namespace JSP233.ActualGrid213
open StarCompletion APGeometry ActualGrid212 OffResidue44 ThinFringe33
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem actual_heavy_off_count904 {N L R : ℕ} (F : Finset (Finset ℤ))
    (d a : Finset ℤ → ℤ) (hN : 640000 ≤ N)
    (hL : 1 ≤ L) (hLR : L ≤ R) (hRN : R ≤ N)
    (hlegal : Legal (Ground N) F)
    (htrace : ∀ S ∈ F, APAt (d S) (a S) (S ∩ Finset.Icc (L : ℤ) (R : ℤ)))
    (hdense : ∀ S ∈ F, (N : ℝ) < 11 * S.card)
    (hwidth : (L : ℝ) + (N - R) < (N : ℝ) / (2951 / 100 : ℝ)) :
    (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card ≤ 904 := by
  have hnR : (640000 : ℝ) ≤ N := by exact_mod_cast hN
  have hgate : (16 : ℝ) * 15 / 2 <
      (N : ℝ) * ((17 : ℝ) / 11 - 1 - 16 / (2951 / 100 : ℝ)) := by
    norm_num
    nlinarith only [hnR]
  have hactual := actual_central_gate (p := 17) (k := 11) hL hLR hRN (by omega)
    hwidth (by convert hgate using 1 <;> norm_num)
  have hb := actual_heavy_off_incidence F (L : ℤ) (R : ℤ) d a 17 11
    ((3 / 5000 : ℝ) * N) (by omega) (by norm_num) hlegal htrace hdense hactual
  rw [(actual_interval_ground_card hL hLR hRN).2] at hb
  norm_num only [Nat.reduceSub, Nat.cast_ofNat] at hb
  by_contra hh
  have hlarge : (905 : ℝ) ≤
      (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card := by
    exact_mod_cast (show 905 ≤ (HeavyOffMembers F d a ((3 / 5000 : ℝ) * N)).card by omega)
  have hm := mul_le_mul_of_nonneg_right hlarge
    (show (0 : ℝ) ≤ (3 / 5000 : ℝ) * N by positivity)
  nlinarith only [hb, hm, hwidth, hnR]

/-- A member with few off points cannot have a large true trace step.
The on-class points are bounded by the full residue class in the actual
ground set; the member itself need not fill that class. -/
theorem actual_few_off_step_le11 {N : ℕ} {S : Finset ℤ} {d a : ℤ}
    (hN : 640000 ≤ N) (hS : S ⊆ Ground N) (hd : 0 < d)
    (hdense : (N : ℝ) < 11 * S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ) ≤ (3 / 5000 : ℝ) * N) :
    d ≤ 11 := by
  by_contra hh
  have hd12 : (12 : ℤ) ≤ d := by omega
  have hd12R : (12 : ℝ) ≤ d := by exact_mod_cast hd12
  let C := (Ground N).filter (fun y => d ∣ y - a)
  have hclass : APAt d a C := by
    refine ⟨hd, 1, (N : ℤ), ?_⟩
    intro y
    simp only [C, Finset.mem_filter]
    rw [mem_ground]
    tauto
  have hC : (C.card : ℝ) ≤ (N : ℝ) / 12 + 1 := by
    by_cases hne : C.Nonempty
    · have hground : C ⊆ Finset.Icc 1 (N : ℤ) := by
        intro y hy
        exact Finset.mem_Icc.mpr ((mem_ground N y).mp (Finset.mem_filter.mp hy).1)
      have hs := apAt_card_span hclass hne hground
      have hsR : (d : ℝ) * ((C.card : ℝ) - 1) ≤ (N : ℝ) - 1 := by exact_mod_cast hs
      have hcR : (1 : ℝ) ≤ C.card := by
        exact_mod_cast (show 1 ≤ C.card from Finset.card_pos.mpr hne)
      have hm := mul_le_mul_of_nonneg_right hd12R (sub_nonneg.mpr hcR)
      nlinarith only [hsR, hm]
    · have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  let A := S.filter (fun y => d ∣ y - a)
  have hAC : A ⊆ C := by
    intro y hy
    obtain ⟨hyS, hyclass⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨hS hyS, hyclass⟩
  have hA : (A.card : ℝ) ≤ C.card := by exact_mod_cast Finset.card_le_card hAC
  have hpart := Finset.card_filter_add_card_filter_not (s := S) (fun y => d ∣ y - a)
  have hpartR : (A.card : ℝ) + (ActualOffPoints S d a).card = S.card := by
    exact_mod_cast hpart
  have hnR : (640000 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith only [hdense, hfew, hC, hA, hpartR, hnR]

theorem actual_few_positive_off_step_range {N : ℕ} {S : Finset ℤ} {d a : ℤ}
    (hN : 640000 ≤ N) (hS : S ⊆ Ground N) (hd : 0 < d)
    (hdense : (N : ℝ) < 11 * S.card)
    (hfew : ((ActualOffPoints S d a).card : ℝ) ≤ (3 / 5000 : ℝ) * N)
    (hpositive : 0 < (ActualOffPoints S d a).card) : 2 ≤ d ∧ d ≤ 11 := by
  have hu := actual_few_off_step_le11 hN hS hd hdense hfew
  refine ⟨?_, hu⟩
  by_contra hh
  have he : d = 1 := by omega
  simp [ActualOffPoints, he] at hpositive


#print axioms actual_heavy_off_count904
#print axioms actual_few_off_step_le11
#print axioms actual_few_positive_off_step_range
end
end JSP233.ActualGrid213
