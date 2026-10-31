import Erdos272.Global.SparseSmall39

/-! The quadratic degree estimate keeps the size of the same actual omitter.
The older root branch discarded its quadratic saving before choosing a scale.
-/
namespace JSP233.RootQuadratic208
open StarCompletion SparseSmall39
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Q (y : ℝ) : ℝ := y - y^2 / 2

/-- Only nine dyadic indices can occur for the actual omitter in this window.
This is a bound on its proved size, rather than a finite sampling assumption. -/
theorem actual207_scale_index {N j : ℕ} (hN : N ≤ 705097)
    (hsize : 11 * 242 * 2^j ≤ N) : j ≤ 8 := by
  by_contra hlarge
  have hp := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (show 9 ≤ j by omega)
  norm_num at hp
  omega

theorem q_mono {x y : ℝ} (hxy : x ≤ y) (hy : y ≤ 1) : Q x ≤ Q y := by
  have hp := mul_nonneg (sub_nonneg.mpr hxy)
    (show 0 ≤ 1 - (x + y) / 2 by linarith only [hxy, hy])
  dsimp only [Q]
  nlinarith only [hp]

theorem actual_omitter_quadratic {N : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ}
    (hN : 2 ≤ N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hT : T ∈ F) (hTc : c ∉ T)
    (hsize : T.card + 1 ≤ N) :
    ((RootPart F c).card : ℝ) ≤
      T.card * (N : ℝ) - ((T.card : ℝ)^2 + 3 * T.card) / 2 := by
  have hdegree := actual_degree_from_omitter hlegal hbad hT hTc
  have he := degreeBudget_closed N T.card hN hsize
  have hdegR : ((RootPart F c).card : ℝ) ≤ DegreeBudget N T.card := by exact_mod_cast hdegree
  have heR := congrArg (fun m : ℕ => (m : ℝ)) he
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hN, Nat.cast_ofNat,
    Nat.cast_choose_two] at heR
  nlinarith only [hdegR, heR]

theorem actual_normalized_root {N : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ} {z : ℝ}
    (hN : 2 ≤ N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hT : T ∈ F) (hTc : c ∉ T)
    (hsize : T.card + 1 ≤ N)
    (hz : (T.card : ℝ) / N ≤ z) (hz1 : z ≤ 1) :
    ((RootPart F c).card : ℝ) / (N : ℝ)^2 ≤ Q z := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hquad := actual_omitter_quadratic hN hlegal hbad hT hTc hsize
  have hq := q_mono hz hz1
  have hmul : Q ((T.card : ℝ) / N) * (N : ℝ)^2 =
      T.card * (N : ℝ) - (T.card : ℝ)^2 / 2 := by
    unfold Q
    field_simp [hNp.ne']
  apply le_trans _ hq
  apply (div_le_iff₀ (sq_pos_of_pos hNp)).mpr
  rw [hmul]
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg T.card
  linarith only [hquad, ht]

theorem actual_root_scale_envelope {N R v : ℕ} {F : Finset (Finset ℤ)}
    {c : ℤ} {T : Finset ℤ}
    (hN : 4 ≤ N) (hlegal : Legal (Ground N) F)
    (hbad : ∀ S ∈ F, ¬ IsAP S) (hT : T ∈ F) (hTc : c ∉ T)
    (hscale : T.card ≤ 2 * R * v) (hsparse : 11 * T.card ≤ N) :
    ((RootPart F c).card : ℝ) / (N : ℝ)^2 ≤
      Q (min (2 * (R : ℝ) * v / N) (1 / 11)) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have htN : T.card + 1 ≤ N := by omega
  have hsR : (T.card : ℝ) ≤ 2 * (R : ℝ) * v := by exact_mod_cast hscale
  have hspR : 11 * (T.card : ℝ) ≤ N := by exact_mod_cast hsparse
  apply actual_normalized_root (by omega) hlegal hbad hT hTc htN
  · apply le_min
    · exact div_le_div_of_nonneg_right hsR hNp.le
    · apply (div_le_iff₀ hNp).mpr
      linarith only [hspR]
  · exact (min_le_right _ _).trans (by norm_num)

/-- Both contributions here belong to the same actual family and root. -/
theorem actual_partition_payment {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    {rootPrice avoidPrice : ℝ}
    (hroot : ((RootPart F c).card : ℝ) / (N : ℝ)^2 ≤ rootPrice)
    (havoid : ((Avoiders F c).card : ℝ) / (N : ℝ)^2 ≤ avoidPrice) :
    (F.card : ℝ) / (N : ℝ)^2 ≤ rootPrice + avoidPrice := by
  have hpart : ((RootPart F c).card : ℝ) / (N : ℝ)^2 +
      ((Avoiders F c).card : ℝ) / (N : ℝ)^2 = (F.card : ℝ) / (N : ℝ)^2 := by
    rw [← add_div, ← Nat.cast_add, root_avoider_card_partition]
  linarith only [hroot, havoid, hpart]

#print axioms actual_omitter_quadratic
#print axioms actual_root_scale_envelope
#print axioms actual_partition_payment
end
end JSP233.RootQuadratic208
