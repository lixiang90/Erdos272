module

public import Erdos272.Staircase.StaircaseTailBridge29
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

/-! A quadratic surplus in the actual primitive bad-pair pool of a thick line.
All arithmetic inputs come from the verified floor/Abel accounting chain. -/
namespace JSP233.QuantitativeTail31
open StaircaseGeometry StaircaseSupply StaircaseTailBridge29 HarmonicAbel29
open scoped BigOperators
noncomputable section

theorem log_128_le_seven : Real.log (128 : ℝ) ≤ 7 := by
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  rw [show (128 : ℝ) = 2^7 by norm_num, Real.log_pow]
  norm_num
  linarith

theorem harmonic_128_le_eight : Harmonic 128 ≤ 8 := by
  have hh := HarmonicAbel29.harmonic_le_one_add_log 128
  have hl := log_128_le_seven
  change Harmonic 128 ≤ 1+Real.log (128 : ℝ) at hh
  linarith

theorem harmonic_succ (n : ℕ) : Harmonic (n+1) = Harmonic n + (1 : ℝ)/(n+1) := by
  unfold Harmonic
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n+1)]
  push_cast
  rfl

theorem harmonic_linear_large (n : ℕ) (hn : 128 ≤ n) :
    Harmonic n ≤ 8 + (n : ℝ)/128 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have hh := harmonic_128_le_eight
    change Harmonic 128 ≤ 8+(128 : ℝ)/128
    rw [show (128 : ℝ)/128 = 1 by norm_num]
    linarith
  | succ n hn ih =>
    have hinv : (1 : ℝ)/((n : ℝ)+1) ≤ 1/128 := by
      apply one_div_le_one_div_of_le (by norm_num)
      exact_mod_cast (show 128 ≤ n+1 by omega)
    rw [harmonic_succ]
    push_cast
    linarith

theorem harmonic_linear (n : ℕ) : Harmonic n ≤ 8 + (n : ℝ)/128 := by
  by_cases hn : 128 ≤ n
  · exact harmonic_linear_large n hn
  · have hm := harmonic_mono (show n ≤ 128 by omega)
    have hb := harmonic_128_le_eight
    have hpos : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith

theorem actual_defect_le_harmonic {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C) :
    ((Family C).card : ℝ) - (PrimitivePool (Family C)).card ≤
      -rationalQuadraticLoss (Height C) (Width C) +
      (Height C : ℝ)*Harmonic (Width C) +
      (1/2 : ℝ)*(Height C : ℝ)*Harmonic (Height C) +
      (3/2 : ℝ)*(Width C : ℝ)*Harmonic (Width C) +
      (5/2 : ℝ)*((Height C : ℝ)+(Width C : ℝ))+4 := by
  have hd0 : ((Family C).card : ℝ) ≤ ((Family (ValidDown C)).card : ℝ) := by
    exact_mod_cast validDown_demand_mono hvalid
  exact resource_accounting (hd0.trans (actual_demand_le C))
    (actual_pool_eq_totient C hL hR) (actual_mixed_sum_lower C)
    (actual_profile_weighted_lower C (by omega))
    (TotientFloor29.divisorError_prefix_upper (Width C))
    (actual_height_sum_le_rectangle C)
    (TotientFloor29.totient_prefix_lower (Height C) (by omega))
    (TotientFloor29.totient_prefix_lower (Width C) (by omega))

theorem actual_defect_le_max_harmonic {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C) :
    ((Family C).card : ℝ) - (PrimitivePool (Family C)).card ≤
      -(107/1000 : ℝ)*((max (Height C) (Width C) : ℕ) : ℝ)^2 +
      3*((max (Height C) (Width C) : ℕ) : ℝ)*Harmonic (max (Height C) (Width C)) +
      5*((max (Height C) (Width C) : ℕ) : ℝ)+4 := by
  let M := max (Height C) (Width C)
  have hLM : (Height C : ℝ) ≤ M := by exact_mod_cast (le_max_left (Height C) (Width C))
  have hRM : (Width C : ℝ) ≤ M := by exact_mod_cast (le_max_right (Height C) (Width C))
  have hHL : Harmonic (Height C) ≤ Harmonic M := harmonic_mono (le_max_left _ _)
  have hHR : Harmonic (Width C) ≤ Harmonic M := harmonic_mono (le_max_right _ _)
  have h1 : (Height C : ℝ)*Harmonic (Width C) ≤ (M : ℝ)*Harmonic M :=
    mul_le_mul hLM hHR (harmonic_nonneg _) (Nat.cast_nonneg M)
  have h2 : (Height C : ℝ)*Harmonic (Height C) ≤ (M : ℝ)*Harmonic M :=
    mul_le_mul hLM hHL (harmonic_nonneg _) (Nat.cast_nonneg M)
  have h3 : (Width C : ℝ)*Harmonic (Width C) ≤ (M : ℝ)*Harmonic M :=
    mul_le_mul hRM hHR (harmonic_nonneg _) (Nat.cast_nonneg M)
  have hq : (107/1000 : ℝ)*(M : ℝ)^2 ≤ rationalQuadraticLoss (Height C) (Width C) := by
    simpa only [M, Nat.cast_max] using rationalQuadraticLoss_lower (Height C : ℝ) (Width C : ℝ)
  have ha := actual_defect_le_harmonic hvalid hL hR
  change ((Family C).card : ℝ) - (PrimitivePool (Family C)).card ≤
    -(107/1000 : ℝ)*(M : ℝ)^2 + 3*(M : ℝ)*Harmonic M+5*(M : ℝ)+4
  linarith

theorem quadratic_margin (M : ℝ) (hM : 1000 ≤ M) :
    M^2/20 ≤ (107/1000 : ℝ)*M^2 - 3*M*(8+M/128) - 5*M - 4 := by
  have hp := mul_nonneg (sub_nonneg.mpr hM) (show 0 ≤ M by linarith)
  nlinarith

theorem coordinates_pool_surplus {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C)
    (hM : 1000 ≤ max (Height C) (Width C)) :
    ((Family C).card : ℝ) + ((max (Height C) (Width C) : ℕ) : ℝ)^2/20 ≤
      (PrimitivePool (Family C)).card := by
  let M := max (Height C) (Width C)
  have ha := actual_defect_le_max_harmonic hvalid hL hR
  have hh := harmonic_linear M
  have hp : (0 : ℝ) ≤ 3*(M : ℝ) := by positivity
  have hmul := mul_le_mul_of_nonneg_left hh hp
  have hMr : (1000 : ℝ) ≤ M := by exact_mod_cast hM
  have hq := quadratic_margin (M : ℝ) hMr
  change ((Family C).card : ℝ) + (M : ℝ)^2/20 ≤ (PrimitivePool (Family C)).card
  change ((Family C).card : ℝ) - (PrimitivePool (Family C)).card ≤
    -(107/1000 : ℝ)*(M : ℝ)^2+3*(M : ℝ)*Harmonic M+5*(M : ℝ)+4 at ha
  nlinarith

theorem family_card_le_rectangle (C : Finset (ℕ × ℕ)) :
    (Family C).card ≤ (Height C+1)*(Width C+1) := by
  rw [family_card]
  have hsub : C ⊆ (Finset.range (Height C+1)).product (Finset.range (Width C+1)) := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr
      (by have hh : p.1 ≤ Height C := Finset.le_sup (f := Prod.fst) hp; omega),
      Finset.mem_range.mpr (by have hh : p.2 ≤ Width C := Finset.le_sup (f := Prod.snd) hp; omega)⟩
  simpa using Finset.card_le_card hsub

theorem family_card_le_max_square (C : Finset (ℕ × ℕ)) :
    (Family C).card ≤ (max (Height C) (Width C)+1)^2 := by
  have hh := Nat.mul_le_mul (Nat.succ_le_succ (le_max_left (Height C) (Width C)))
    (Nat.succ_le_succ (le_max_right (Height C) (Width C)))
  exact (family_card_le_rectangle C).trans (by simpa only [pow_two] using hh)

theorem family_count_forces_large_extent (C : Finset (ℕ × ℕ))
    (hcard : 1000000 < (Family C).card) : 1000 ≤ max (Height C) (Width C) := by
  have hh := family_card_le_max_square C
  by_contra hn
  have hm : max (Height C) (Width C) ≤ 999 := by omega
  have hm2 := Nat.mul_le_mul (Nat.succ_le_succ hm) (Nat.succ_le_succ hm)
  have hp : (max (Height C) (Width C)+1)^2 ≤ 1000000 := by
    simpa only [pow_two] using hm2
  omega

theorem coordinates_pool_surplus_count {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C)
    (hM : 1000 ≤ max (Height C) (Width C)) :
    ((Family C).card : ℝ) + ((Family C).card : ℝ)/21 ≤
      (PrimitivePool (Family C)).card := by
  let M := max (Height C) (Width C)
  have hh : ((Family C).card : ℝ) ≤ ((M : ℝ)+1)^2 := by
    exact_mod_cast family_card_le_max_square C
  have hm : (1000 : ℝ) ≤ M := by exact_mod_cast hM
  have hp := mul_nonneg (sub_nonneg.mpr hm) (show (0 : ℝ) ≤ M by linarith)
  have hs := coordinates_pool_surplus hvalid hL hR hM
  change ((Family C).card : ℝ)+(M : ℝ)^2/20 ≤ (PrimitivePool (Family C)).card at hs
  nlinarith

theorem actual_unit_family_pool_surplus_count (F : Finset (Finset ℤ))
    (hF : ∀ S ∈ F, ∃ l r : ℕ, S = Window l r ∧ 4 ≤ S.card)
    (hleft : ∃ S ∈ F, (-2 : ℤ) ∈ S) (hright : ∃ S ∈ F, (2 : ℤ) ∈ S)
    (hcard : 1000000 < F.card) :
    (F.card : ℝ)+(F.card : ℝ)/21 ≤ (PrimitivePool F).card := by
  obtain ⟨C,hC,hvalid⟩ := exists_coordinates F hF
  have hL : 2 ≤ Height C := by
    obtain ⟨S,hS,hpoint⟩ := hleft
    have hSC : S ∈ Family C := by rw [hC]; exact hS
    obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hSC
    have hw : (-2 : ℤ) ∈ Window p.1 p.2 := by rw [heq]; exact hpoint
    have hm := (mem_window p.1 p.2 (-2)).mp hw
    have hh : p.1 ≤ Height C := Finset.le_sup (f := Prod.fst) hp
    omega
  have hR : 2 ≤ Width C := by
    obtain ⟨S,hS,hpoint⟩ := hright
    have hSC : S ∈ Family C := by rw [hC]; exact hS
    obtain ⟨p,hp,heq⟩ := Finset.mem_image.mp hSC
    have hw : (2 : ℤ) ∈ Window p.1 p.2 := by rw [heq]; exact hpoint
    have hm := (mem_window p.1 p.2 2).mp hw
    have hh : p.2 ≤ Width C := Finset.le_sup (f := Prod.snd) hp
    omega
  have hM : 1000 ≤ max (Height C) (Width C) :=
    family_count_forces_large_extent C (by rw [hC]; exact hcard)
  simpa only [hC] using coordinates_pool_surplus_count hvalid hL hR hM

#print axioms log_128_le_seven
#print axioms harmonic_128_le_eight
#print axioms harmonic_succ
#print axioms harmonic_linear_large
#print axioms harmonic_linear
#print axioms actual_defect_le_harmonic
#print axioms actual_defect_le_max_harmonic
#print axioms quadratic_margin
#print axioms coordinates_pool_surplus
#print axioms family_card_le_rectangle
#print axioms family_card_le_max_square
#print axioms family_count_forces_large_extent
#print axioms coordinates_pool_surplus_count
#print axioms actual_unit_family_pool_surplus_count
end
end JSP233.QuantitativeTail31
