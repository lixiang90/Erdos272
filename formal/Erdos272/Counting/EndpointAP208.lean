import Erdos272.Global.APPrepare49
import Erdos272.Arithmetic.Hyperbola131

/-! The actual large-AP endpoint filters are injected into the complete
integer parameter library. Its size uses truncated natural subtraction,
so every step and every small-span boundary is retained exactly. -/
namespace JSP233.EndpointAP208
open StarCompletion APGeometry APCount41 APPrepare49
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def EndpointParameters (t : ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (Finset.Icc 1 t).sigma (fun d => Finset.Icc 3 (t / d))

def EndpointCount (t : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 t, (t / d - 2)

theorem endpoint_parameters_card (t : ℕ) :
    (EndpointParameters t).card = EndpointCount t := by
  rw [EndpointParameters, Finset.card_sigma]
  apply Finset.sum_congr rfl
  intro d _hd
  rw [Nat.card_Icc]
  omega

theorem endpoint_count_mono {t u : ℕ} (htu : t ≤ u) :
    EndpointCount t ≤ EndpointCount u := by
  calc
    EndpointCount t ≤ ∑ d ∈ Finset.Icc 1 t, (u / d - 2) := by
      apply Finset.sum_le_sum
      intro d _hd
      exact Nat.sub_le_sub_right (Nat.div_le_div_right htu) 2
    _ ≤ EndpointCount u := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hd0, hdt⟩ := Finset.mem_Icc.mp hd
        exact Finset.mem_Icc.mpr ⟨hd0, hdt.trans htu⟩
      · intro d _ _
        exact Nat.zero_le _

theorem truncated_two_sum (t : ℕ) :
    (∑ d ∈ Finset.Icc 1 t, min (t / d) 2) = t + t / 2 := by
  have hterm : ∀ d ∈ Finset.Icc 1 t,
      min (t / d) 2 = 1 + if d ≤ t / 2 then 1 else 0 := by
    intro d hd
    obtain ⟨hd0, hdt⟩ := Finset.mem_Icc.mp hd
    have hq0 : 1 ≤ t / d := (Nat.le_div_iff_mul_le hd0).mpr (by omega)
    have hq2 : 2 ≤ t / d ↔ d ≤ t / 2 := by
      rw [Nat.le_div_iff_mul_le hd0, Nat.le_div_iff_mul_le (by decide : 0 < 2)]
      simp only [Nat.mul_comm]
    by_cases h : d ≤ t / 2
    · rw [if_pos h, min_eq_right (hq2.mpr h)]
    · have hq : t / d = 1 := by have hh := mt hq2.mp h; omega
      simp only [hq, if_neg h]
      omega
  have hfilter : (Finset.Icc 1 t).filter (fun d => d ≤ t / 2) =
      Finset.Icc 1 (t / 2) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    have hh := Nat.div_le_self t 2
    omega
  have hbool : (∑ d ∈ Finset.Icc 1 t, (if d ≤ t / 2 then 1 else 0 : ℕ)) = t / 2 := by
    rw [Finset.sum_boole]
    change ((Finset.Icc 1 t).filter (fun d => d ≤ t / 2)).card = t / 2
    rw [hfilter, Nat.card_Icc]
    omega
  calc
    _ = ∑ d ∈ Finset.Icc 1 t, (1 + if d ≤ t / 2 then 1 else 0) :=
      Finset.sum_congr rfl hterm
    _ = t + t / 2 := by
      rw [Finset.sum_add_distrib, hbool]
      simp

theorem endpoint_divisor_identity (t : ℕ) :
    EndpointCount t + t + t / 2 = SimplexMoment57.DivCount 1 t := by
  have hsum : EndpointCount t + (∑ d ∈ Finset.Icc 1 t, min (t / d) 2) =
      ∑ d ∈ Finset.Icc 1 t, t / d := by
    rw [EndpointCount, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d _hd
    omega
  rw [truncated_two_sum] at hsum
  simpa only [SimplexMoment57.DivCount, Nat.add_assoc] using hsum

def FastDivSum (t : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => FastDivSum t m + t / (m + 1)

theorem fast_div_sum_eq (t m : ℕ) :
    FastDivSum t m = ∑ d ∈ Finset.Icc 1 m, t / d := by
  induction m with
  | zero => simp [FastDivSum]
  | succ m ih =>
    rw [FastDivSum, ih, Finset.sum_Icc_succ_top (by omega)]

def FastEndpointCount (t : ℕ) : ℕ :=
  2 * FastDivSum t (Nat.sqrt t) - (Nat.sqrt t)^2 - t - t / 2

theorem fast_endpoint_count_eq (t : ℕ) :
    FastEndpointCount t = EndpointCount t := by
  have h := Hyperbola131.actual_hyperbola_nat
    (by simpa only [pow_two] using Nat.sqrt_le t)
    (by simpa only [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt' t)
  rw [← endpoint_divisor_identity, ← fast_div_sum_eq] at h
  dsimp only [FastEndpointCount]
  omega

theorem actual_fixed_endpoint_parameter_bound {t : ℕ}
    {F : Finset (Finset ℤ)} {q : ℤ} (first : Bool)
    (hAP : ∀ S ∈ F, IsAP S) (hsize : ∀ S ∈ F, 4 ≤ S.card)
    (hend : ∀ S ∈ F, (if first then Low S else High S) = q)
    (hspan : ∀ S ∈ F, High S - Low S ≤ (t : ℤ)) :
    F.card ≤ EndpointCount t := by
  let X := {S // S ∈ F}
  let f (S : X) : Σ _ : ℕ, ℕ := ⟨Step S.val, S.val.card - 1⟩
  have hne : ∀ S ∈ F, S.Nonempty := fun S hS =>
    Finset.card_pos.mp (by have hh := hsize S hS; omega)
  have hdata : ∀ S ∈ F, 0 < Step S ∧
      Step S * (S.card - 1) ≤ t := by
    intro S hS
    obtain ⟨hd, p, hp⟩ := actual_step (hAP S hS)
    have hs : High S - Low S = (Step S : ℤ) * ((S.card : ℤ) - 1) := by
      simpa only [High, Low, dif_pos (hne S hS)] using apAt_span_eq hp (hne S hS)
    have hm : ((Step S * (S.card - 1) : ℕ) : ℤ) ≤ t := by
      rw [Nat.cast_mul, Nat.cast_sub (by have hh := hsize S hS; omega : 1 ≤ S.card),
        Nat.cast_one]
      rw [← hs]
      exact hspan S hS
    exact ⟨hd, by exact_mod_cast hm⟩
  have hmaps : Set.MapsTo f (Finset.univ : Finset X) (EndpointParameters t) := by
    intro S _hS
    have hd := (hdata S.val S.property).1
    have hm := (hdata S.val S.property).2
    have hk : 3 ≤ S.val.card - 1 := by have hh := hsize S.val S.property; omega
    have hdle : Step S.val ≤ t := by
      have hh := Nat.mul_le_mul_left (Step S.val) (show 1 ≤ S.val.card - 1 by omega)
      simp only [Nat.mul_one] at hh
      exact hh.trans hm
    have hkle : S.val.card - 1 ≤ t / Step S.val :=
      (Nat.le_div_iff_mul_le hd).mpr (by simpa only [Nat.mul_comm] using hm)
    exact Finset.mem_sigma.mpr
      ⟨Finset.mem_Icc.mpr ⟨hd, hdle⟩, Finset.mem_Icc.mpr ⟨hk, hkle⟩⟩
  have hinj : Function.Injective f := by
    intro S T he
    have hd : Step S.val = Step T.val := congrArg Sigma.fst he
    have hk' : S.val.card - 1 = T.val.card - 1 := congrArg Sigma.snd he
    have hk : S.val.card = T.val.card := by
      have hS := hsize S.val S.property
      have hT := hsize T.val T.property
      omega
    obtain ⟨_, p, hp⟩ := actual_step (hAP S.val S.property)
    obtain ⟨_, r, hr⟩ := actual_step (hAP T.val T.property)
    have hs : High S.val - Low S.val = (Step S.val : ℤ) * ((S.val.card : ℤ) - 1) := by
      simpa only [High, Low, dif_pos (hne S.val S.property)] using
        apAt_span_eq hp (hne S.val S.property)
    have ht : High T.val - Low T.val = (Step T.val : ℤ) * ((T.val.card : ℤ) - 1) := by
      simpa only [High, Low, dif_pos (hne T.val T.property)] using
        apAt_span_eq hr (hne T.val T.property)
    have hS := hend S.val S.property
    have hT := hend T.val T.property
    rw [hd, hk] at hs
    have heq : Low S.val = Low T.val ∧ High S.val = High T.val := by
      cases first <;> simp only [Bool.false_eq_true, ↓reduceIte] at hS hT
      · constructor <;> omega
      · constructor <;> omega
    apply Subtype.ext
    exact same_step_equal_of_endpoints (hne S.val S.property) (hne T.val T.property)
      hp (by simpa only [hd] using hr) heq.1 heq.2
  have hh := Finset.card_le_card_of_injOn f hmaps hinj.injOn
  rw [endpoint_parameters_card] at hh
  simpa only [Finset.card_univ, X, Fintype.card_coe] using hh

theorem actual_low_cut_parameter_bound {N c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hcN : c ≤ N) :
    (LowCut F (c : ℤ)).card ≤ EndpointCount (N - c) := by
  apply actual_fixed_endpoint_parameter_bound (F := LowCut F (c : ℤ))
    (q := (c : ℤ)) true
    (fun S hS => (actual_large_AP_member (Finset.mem_filter.mp hS).1).2.1)
    (fun S hS => (actual_large_AP_member (Finset.mem_filter.mp hS).1).2.2)
    (fun S hS => by simpa only [↓reduceIte] using (Finset.mem_filter.mp hS).2)
  intro S hS
  have hm := actual_large_AP_member (Finset.mem_filter.mp hS).1
  have hhigh := (mem_ground N (High S)).mp
    (hF.1 S hm.1 (high_spec (isAP_nonempty hm.2.1)).1)
  have hlo := (Finset.mem_filter.mp hS).2
  rw [Nat.cast_sub hcN]
  omega

theorem actual_high_cut_parameter_bound {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hL : 1 ≤ L) :
    (HighCut F (c : ℤ) (L : ℤ)).card ≤ EndpointCount (L - 1) := by
  apply actual_fixed_endpoint_parameter_bound (F := HighCut F (c : ℤ) (L : ℤ))
    (q := (L : ℤ)) false
    (fun S hS => (actual_large_AP_member
      (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2.1)
    (fun S hS => (actual_large_AP_member
      (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2.2)
    (fun S hS => by simpa only [Bool.false_eq_true, ↓reduceIte] using
      (Finset.mem_filter.mp hS).2)
  intro S hS
  have hm := actual_large_AP_member
    (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  have hlow := (mem_ground N (Low S)).mp
    (hF.1 S hm.1 (low_spec (isAP_nonempty hm.2.1)).1)
  have hhi := (Finset.mem_filter.mp hS).2
  rw [Nat.cast_sub hL, Nat.cast_one]
  omega

theorem actual_low_offset_parameter_bound {U t : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground U) F) (ht : t < U) :
    (LowCut F ((t + 1 : ℕ) : ℤ)).card ≤ EndpointCount (U - 1 - t) := by
  have h := actual_low_cut_parameter_bound (c := t + 1) hF (by omega)
  have he : U - (t + 1) = U - 1 - t := by omega
  simpa only [he] using h

theorem actual_high_offset_parameter_bound {U t c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground U) F) (ht : t < U) :
    (HighCut F (c : ℤ) ((U - t : ℕ) : ℤ)).card ≤ EndpointCount (U - 1 - t) := by
  have h := actual_high_cut_parameter_bound (L := U - t) (c := c) hF (by omega)
  have he : U - t - 1 = U - 1 - t := by omega
  simpa only [he] using h

#print axioms endpoint_parameters_card
#print axioms endpoint_count_mono
#print axioms truncated_two_sum
#print axioms endpoint_divisor_identity
#print axioms fast_div_sum_eq
#print axioms fast_endpoint_count_eq
#print axioms actual_fixed_endpoint_parameter_bound
#print axioms actual_low_cut_parameter_bound
#print axioms actual_high_cut_parameter_bound
#print axioms actual_low_offset_parameter_bound
#print axioms actual_high_offset_parameter_bound
end
end JSP233.EndpointAP208
