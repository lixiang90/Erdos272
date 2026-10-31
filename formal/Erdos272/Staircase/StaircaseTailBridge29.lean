import Erdos272.Foundation.StaircaseTail
import Erdos272.Arithmetic.HarmonicAbel
import Erdos272.Arithmetic.MixedFloor29
import Mathlib.Algebra.BigOperators.Intervals

/-! Actual staircase geometry for the arithmetic-to-analytic tail bridge.
The arithmetic estimates are supplied by the separately checked floor and
Abel modules; no numerical sampling is used for these geometric statements. -/
namespace JSP233.StaircaseTailBridge29
open StaircaseGeometry StaircaseCertificate StaircaseSupply
open scoped BigOperators
noncomputable section

theorem sum_range_eq_zero_add_Icc (f : ℕ → ℝ) (R : ℕ) :
    (∑ r ∈ Finset.range (R+1), f r) = f 0 + ∑ r ∈ Finset.Icc 1 R, f r := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ R+1)]
    ring

theorem profile_zero_eq_height (C : Finset (ℕ × ℕ)) (hne : C.Nonempty) :
    Profile C 0 = Height C + 1 := by
  apply le_antisymm (profile_height_bound C 0)
  obtain ⟨p, hp, hmax⟩ := Finset.exists_mem_eq_sup C hne Prod.fst
  have hdown : (p.1,0) ∈ Down C := (mem_down C _).mpr ⟨p,hp,le_rfl,by omega⟩
  have hlt := (mem_down_iff_profile C p.1 0).mp hdown
  change Height C = p.1 at hmax
  omega

theorem actual_height_antitone (C : Finset (ℕ × ℕ)) :
    Antitone (fun r => Profile C r - 1) := by
  intro r s hrs
  exact Nat.sub_le_sub_right (profile_antitone C hrs) 1

theorem actual_height_le (C : Finset (ℕ × ℕ)) (r : ℕ) :
    Profile C r - 1 ≤ Height C := by
  have := profile_height_bound C r
  omega

theorem actual_height_sum_le_rectangle (C : Finset (ℕ × ℕ)) :
    (∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r - 1 : ℕ) : ℝ)) ≤
      (Height C : ℝ) * (Width C : ℝ) := by
  calc
    _ ≤ ∑ _r ∈ Finset.Icc 1 (Width C), (Height C : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      exact_mod_cast actual_height_le C r
    _ = _ := by simp [Nat.card_Icc]; ring

theorem actual_demand_le (C : Finset (ℕ × ℕ)) :
    ((Family (ValidDown C)).card : ℝ) ≤ (Height C : ℝ) +
      (∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r - 1 : ℕ) : ℝ)) + (Width C : ℝ) := by
  rw [family_card, validDown_card_sum, Nat.cast_sum, sum_range_eq_zero_add_Icc]
  have hzero : ((Profile C 0 - (3-0) : ℕ) : ℝ) ≤ (Height C : ℝ) := by
    exact_mod_cast (show Profile C 0 - (3-0) ≤ Height C by
      have := profile_height_bound C 0
      omega)
  have hcols : (∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r - (3-r) : ℕ) : ℝ)) ≤
      ∑ r ∈ Finset.Icc 1 (Width C), (((Profile C r - 1 : ℕ) : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro r hr
    have hn : Profile C r - (3-r) ≤ Profile C r - 1 + 1 := by omega
    exact_mod_cast hn
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul, mul_one] at hcols
  linarith

theorem leftSupply_real (H : ℕ) (hH : 2 ≤ H) :
    (LeftSupply H : ℝ) = (∑ n ∈ Finset.Icc 1 H, (Nat.totient n : ℝ)) - 2 := by
  have h := StaircaseTail.leftSupply_add_two H hH
  have hc : (LeftSupply H : ℝ) + 2 =
      ∑ n ∈ Finset.range (H+1), (Nat.totient n : ℝ) := by exact_mod_cast h
  rw [sum_range_eq_zero_add_Icc] at hc
  norm_num at hc
  linarith

theorem actual_pool_eq_totient (C : Finset (ℕ × ℕ))
    (hL : 2 ≤ Height C) (hR : 2 ≤ Width C) :
    ((PrimitivePool (Family C)).card : ℝ) =
      (∑ n ∈ Finset.Icc 1 (Height C), (Nat.totient n : ℝ)) +
      (∑ n ∈ Finset.Icc 1 (Width C), (Nat.totient n : ℝ)) - 4 +
      ∑ r ∈ Finset.Icc 1 (Width C), (MixedSupply (Profile C r - 1) r : ℝ) := by
  have hne : C.Nonempty := by
    by_contra hn
    have he : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    simp [he, Height] at hL
  have hzero : Profile C 0 - 1 = Height C := by rw [profile_zero_eq_height C hne]; omega
  rw [← down_primitivePool_eq C, down_pool_card, hzero]
  push_cast
  rw [leftSupply_real _ hL, leftSupply_real _ hR, sum_range_eq_zero_add_Icc]
  simp only [lt_self_iff_false, ↓reduceIte, zero_add]
  congr 1
  · ring
  · apply Finset.sum_congr rfl
    intro r hr
    have hp : 0 < r := (Finset.mem_Icc.mp hr).1
    simp [hp]

def rationalQuadraticLoss (L R : ℝ) : ℝ :=
  (607 / 2000 : ℝ) * (L^2 + R^2) - (393 / 1000 : ℝ) * L * R

def rationalMajorant (L R : ℝ) : ℝ :=
  -rationalQuadraticLoss L R + L * Real.log R + (1/2 : ℝ) * L * Real.log L +
    (3/2 : ℝ) * R * Real.log R + 4*(L+R)+4

theorem rationalQuadraticLoss_lower (L R : ℝ) :
    (107/1000 : ℝ) * (max L R)^2 ≤ rationalQuadraticLoss L R := by
  have hsq : (max L R)^2 ≤ L^2 + R^2 := by
    rcases le_total L R with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg L]
    · rw [max_eq_left h]; nlinarith [sq_nonneg R]
  unfold rationalQuadraticLoss
  nlinarith [sq_nonneg (L-R)]

theorem rationalMajorant_le_tail {L R : ℝ} (hL : 2 ≤ L) (hR : 2 ≤ R) :
    rationalMajorant L R ≤ StaircaseTail.tailMajorant (max L R) := by
  let M := max L R
  have hLM : L ≤ M := le_max_left _ _
  have hRM : R ≤ M := le_max_right _ _
  have hMlog : 0 ≤ Real.log M := Real.log_nonneg (by linarith)
  have hlogL : Real.log L ≤ Real.log M := Real.log_le_log (by linarith) hLM
  have hlogR : Real.log R ≤ Real.log M := Real.log_le_log (by linarith) hRM
  have hLR : L * Real.log R ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogR (by linarith)).trans
      (mul_le_mul_of_nonneg_right hLM hMlog)
  have hRR : R * Real.log R ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogR (by linarith)).trans
      (mul_le_mul_of_nonneg_right hRM hMlog)
  have hLL : L * Real.log L ≤ M * Real.log M :=
    (mul_le_mul_of_nonneg_left hlogL (by linarith)).trans
      (mul_le_mul_of_nonneg_right hLM hMlog)
  have hq := rationalQuadraticLoss_lower L R
  change (107/1000 : ℝ)*M^2 ≤ rationalQuadraticLoss L R at hq
  change rationalMajorant L R ≤ StaircaseTail.tailMajorant M
  unfold rationalMajorant StaircaseTail.tailMajorant
  nlinarith

theorem rationalMajorant_lt_neg_forty {L R : ℝ} (hL : 2 ≤ L) (hR : 2 ≤ R)
    (hM : 250 ≤ max L R) : rationalMajorant L R < -40 :=
  (rationalMajorant_le_tail hL hR).trans_lt (StaircaseTail.tailMajorant_lt_neg_forty hM)

/-- Exact accounting of the four arithmetic errors and the Abel payment.
This algebraic lemma is kept separate from the theorems identifying its
inputs with the actual arithmetic functions. -/
theorem resource_accounting {D P s w e tL tR L R HL HR v : ℝ}
    (hd : D ≤ L+s+R) (hp : P = tL+tR-4+w)
    (hm : v-e-R ≤ w) (ha : (607/1000 : ℝ)*s-L*(1+HR) ≤ v)
    (he : e ≤ R*HR) (hs : s ≤ L*R)
    (hpl : (607/2000 : ℝ)*L^2-L/2-L/2*HL ≤ tL)
    (hpr : (607/2000 : ℝ)*R^2-R/2-R/2*HR ≤ tR) :
    D-P ≤ -rationalQuadraticLoss L R + L*HR+(1/2 : ℝ)*L*HL+
      (3/2 : ℝ)*R*HR+(5/2 : ℝ)*(L+R)+4 := by
  unfold rationalQuadraticLoss
  linarith

theorem harmonic_majorant_le_rational {L R HL HR : ℝ}
    (hL : 0 ≤ L) (hR : 0 ≤ R)
    (hHL : HL ≤ 1+Real.log L) (hHR : HR ≤ 1+Real.log R) :
    -rationalQuadraticLoss L R + L*HR+(1/2 : ℝ)*L*HL+
      (3/2 : ℝ)*R*HR+(5/2 : ℝ)*(L+R)+4 ≤ rationalMajorant L R := by
  have h1 := mul_le_mul_of_nonneg_left hHR hL
  have h2 := mul_le_mul_of_nonneg_left hHL hL
  have h3 := mul_le_mul_of_nonneg_left hHR hR
  unfold rationalMajorant
  nlinarith

theorem actual_profile_weighted_lower (C : Finset (ℕ × ℕ)) (hR : 1 ≤ Width C) :
    (607/1000 : ℝ) * (∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r-1 : ℕ) : ℝ)) -
      (Height C : ℝ) * (1+HarmonicAbel29.Harmonic (Width C)) ≤
    ∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r-1 : ℕ) : ℝ) *
      ((Nat.totient r : ℝ)/r) := by
  apply HarmonicAbel29.actual_totient_nat_profile_lower (fun r => Profile C r-1)
    (Width C) (Height C) hR (actual_height_le C 1)
  · intro r hr hrR
    exact actual_height_antitone C (by omega)
  · intro r hr
    exact TotientFloor29.normalized_totient_prefix_lower r (Finset.mem_Icc.mp hr).1

theorem actual_mixed_sum_lower (C : Finset (ℕ × ℕ)) :
    (∑ r ∈ Finset.Icc 1 (Width C), ((Profile C r-1 : ℕ) : ℝ)*((Nat.totient r : ℝ)/r)) -
      (∑ r ∈ Finset.Icc 1 (Width C), TotientFloor29.divisorError r) - (Width C : ℝ) ≤
    ∑ r ∈ Finset.Icc 1 (Width C), (MixedSupply (Profile C r-1) r : ℝ) := by
  have hs := Finset.sum_le_sum (fun r (hr : r ∈ Finset.Icc 1 (Width C)) =>
    MixedFloor29.mixedSupply_lower (Profile C r-1) r (Finset.mem_Icc.mp hr).1)
  simpa [Finset.sum_sub_distrib] using hs

theorem actual_defect_le_rationalMajorant {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C) :
    ((Family C).card : ℝ) - (PrimitivePool (Family C)).card ≤
      rationalMajorant (Height C) (Width C) := by
  have hd0 : ((Family C).card : ℝ) ≤ ((Family (ValidDown C)).card : ℝ) := by
    exact_mod_cast validDown_demand_mono hvalid
  have hd := hd0.trans (actual_demand_le C)
  have hp := actual_pool_eq_totient C hL hR
  have hm := actual_mixed_sum_lower C
  have ha := actual_profile_weighted_lower C (by omega)
  have he := TotientFloor29.divisorError_prefix_upper (Width C)
  have hs := actual_height_sum_le_rectangle C
  have hpl := TotientFloor29.totient_prefix_lower (Height C) (by omega)
  have hpr := TotientFloor29.totient_prefix_lower (Width C) (by omega)
  have haccount := resource_accounting hd hp hm ha he hs hpl hpr
  apply haccount.trans
  exact harmonic_majorant_le_rational (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (HarmonicAbel29.harmonic_le_one_add_log (Height C))
    (HarmonicAbel29.harmonic_le_one_add_log (Width C))

theorem actual_tail_defect_lt_neg_forty {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C)
    (hM : 250 ≤ max (Height C) (Width C)) :
    ((Family C).card : ℝ) - (PrimitivePool (Family C)).card < -40 := by
  have hLr : (2 : ℝ) ≤ Height C := by exact_mod_cast hL
  have hRr : (2 : ℝ) ≤ Width C := by exact_mod_cast hR
  have hMr : (250 : ℝ) ≤ max (Height C : ℝ) (Width C : ℝ) := by exact_mod_cast hM
  exact (actual_defect_le_rationalMajorant hvalid hL hR).trans_lt
    (rationalMajorant_lt_neg_forty hLr hRr hMr)

theorem actual_tail_defect_negative {C : Finset (ℕ × ℕ)}
    (hvalid : ∀ p ∈ C, Valid p) (hL : 2 ≤ Height C) (hR : 2 ≤ Width C)
    (hM : 250 ≤ max (Height C) (Width C)) :
    ((Family C).card : ℤ) - (PrimitivePool (Family C)).card < 0 := by
  have h := (actual_tail_defect_lt_neg_forty hvalid hL hR hM).trans (by norm_num : (-40:ℝ)<0)
  exact_mod_cast h

#print axioms sum_range_eq_zero_add_Icc
#print axioms profile_zero_eq_height
#print axioms actual_height_antitone
#print axioms actual_height_le
#print axioms actual_height_sum_le_rectangle
#print axioms actual_demand_le
#print axioms leftSupply_real
#print axioms actual_pool_eq_totient
#print axioms rationalQuadraticLoss_lower
#print axioms rationalMajorant_le_tail
#print axioms rationalMajorant_lt_neg_forty
#print axioms resource_accounting
#print axioms harmonic_majorant_le_rational
#print axioms actual_profile_weighted_lower
#print axioms actual_mixed_sum_lower
#print axioms actual_defect_le_rationalMajorant
#print axioms actual_tail_defect_lt_neg_forty
#print axioms actual_tail_defect_negative
end
end JSP233.StaircaseTailBridge29
