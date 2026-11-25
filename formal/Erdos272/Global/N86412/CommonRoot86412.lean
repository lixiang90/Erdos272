module

public import Erdos272.Global.N86412.WindowGates86412
public import Erdos272.Counting.N88404.DenseJoint88404
public import Erdos272.Resources.N86412.LocalRecovery86412
public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Global.N86412.HighRoot86412
public import Erdos272.Resources.SharpSmall212

@[expose] public section

namespace JSP233.CommonRoot86412
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData86412 WindowGates86412 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def SourceBound (N w : ℕ) : Prop :=
  ∀ A : Finset (Finset ℤ), Legal (Ground N) A →
    (∀ S ∈ A, ¬IsAP S) → (∀ S ∈ A, (info w).memberFloor ≤ S.card) →
    (∀ S ∈ A, 12*S.card ≤ N) →
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N

theorem original_lower {N : ℕ} {F : Finset (Finset ℤ)} (hcard : B N ≤ F.card) :
    (N : ℝ)*((N : ℝ)-1)/2+1 ≤ F.card := by
  have h : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by unfold B at hcard; omega)
  simpa only [Nat.cast_choose_two] using h

theorem sparse_partition {N : ℕ} {F : Finset (Finset ℤ)} :
    ((F.filter IsAP).card : ℝ)+(SparseCrooked N 12 F).card+(Deleted N 12 F).card = F.card := by
  exact_mod_cast actual_original_three_part_partition N 12 F

theorem harmonic_payment {N : ℕ} (hN : 86412 ≤ N) (hhi : N ≤ 88403) :
    (N : ℝ)*Harmonic N ≤ HCommon*N := by
  have hc := LocalRecovery86412.actual_caps (k := 0) (by decide)
    (by omega : 10000 ≤ N) (by simpa only [LocalRecovery86412.High] using hhi)
  have hh : Harmonic N ≤ HCommon := by
    convert hc.harmonic_le using 1 <;>
      norm_num [HCommon, LocalRecovery86412.HLocal, LocalRecovery86412.LogLocal]
  nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N)]

theorem source_contradiction {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F)
    (hinner : (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ A.card+(RootK w : ℝ)*(N : ℝ)-(RootCredit w : ℝ)) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hupper : (N : ℝ) ≤ (info w).high := by exact_mod_cast hhi
  have hj : ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (129/800+QuadraticExtra w : ℝ)*(N : ℝ)^2+EffectiveG w*((N-1 : ℕ) : ℝ)^3+
        Penalty w+(N : ℝ)*Harmonic N+Fee w N := by
    by_cases hlow : w < 2
    · have hcap : 3*G w*((N-1 : ℕ) : ℝ) ≤ 1 := by
        have hcast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
        rw [hcast]
        have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hupper 1)
          (show 0 ≤ 3*G w by linarith only [hg.g_positive])
        exact hh.trans (hg.shadow_cap hlow)
      have hb := DenseJoint88404.actual_AP_inner_with_deleted
        (by omega : 15000 ≤ N) (by omega : N ≤ 2^18) hF hAF hsparse
        hg.g_positive hg.dense_payment hcap hinner
      simpa only [EffectiveG, Penalty, QuadraticExtra, if_pos hlow,
        SieveConstants88404.alpha_one, mul_comm] using hb
    · have hb := DenseJoint158375.actual_AP_inner_with_deleted
        (by omega : 15000 ≤ N) (by omega : N ≤ 2^18) hF hAF hsparse
        hg.g_positive hg.dense_payment hinner
      simpa only [EffectiveG, Penalty, QuadraticExtra, if_neg hlow, add_zero] using hb
  have hcast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hj
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hNhi
  have hm := ExactResponse200000.margin_min_endpoints
    (a := (271/800 : ℝ)-CoeffA w-QuadraticExtra w) (g := EffectiveG w) (loss := Loss w)
    (fee := CoeffC w+Penalty w-((RootCredit w : ℝ)+1))
    hn hupper hg.effective_positive.le hg.chord
  change min (PayMargin w (info w).low) (PayMargin w (info w).high) ≤ PayMargin w N at hm
  have hpositive : 0 < min (PayMargin w (info w).low) (PayMargin w (info w).high) :=
    lt_min_iff.mpr ⟨hg.low_gap, hg.high_gap⟩
  have hgate := lt_of_lt_of_le hpositive hm
  dsimp only [PayMargin, ExactResponse200000.Margin, Loss, Fee] at hgate hj
  nlinarith only [hj, hp, hb, hh, hG, hgate]

theorem small_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 86412 ≤ N) (hhi : N ≤ 88403)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (SmallCount : ℝ)*N) : False := by
  have hn : (86412 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (by omega : N ≤ 179999) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : 0 < (71/800 : ℝ)*N-((SmallCount : ℝ)+HCommon) := by
    have hg := small_gate (w := 0) (by decide)
    change 0 < (71/800 : ℝ)*86412-((SmallCount : ℝ)+HCommon) at hg
    nlinarith only [hg, hn]
  have hm := mul_pos hlin hn0
  nlinarith only [ha, hp, hb, hh, hG, hm]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 86412 ≤ N) (hhi : N ≤ 88403) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (86412 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (by omega : N ≤ 179999) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : HCommon < (1/800 : ℝ)*N := by
    norm_num [HCommon]
    linarith only [hn]
  have hm := mul_lt_mul_of_pos_right hlin hn0
  nlinarith only [ha, hp, hb, hh, hG, hm]

theorem degree_payment {N K : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 86412 ≤ N) (hK : K ≤ 554) (hlegal : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hT : T ∈ Avoiders G c) (hcut : T.card ≤ K) :
    ((RootPart G c).card : ℝ) ≤ (K : ℝ)*N-(K : ℝ)*((K : ℝ)+3)/2 := by
  have hb := actual_degree_from_omitter hlegal hbad
    (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
  have hd := degreeBudget_mono N hcut
  have hn : (86412 : ℝ) ≤ N := by exact_mod_cast hN
  have hk : (K : ℝ) ≤ 554 := by exact_mod_cast hK
  have he := degreeBudget_real_upper N K (K : ℝ) (by omega) (by omega)
    (le_refl _) (by linarith only [hn, hk])
  have hbR : ((RootPart G c).card : ℝ) ≤ DegreeBudget N K := by exact_mod_cast hb.trans hd
  nlinarith only [hbR, he]

theorem actual_common_root {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 86412 ≤ N) (hhi : N ≤ 88403)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsource : ∀ w < 3, SourceBound N w) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  let G := SparseCrooked N 12 F
  have hGF : G ⊆ F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S ∈ G, 12*S.card ≤ N := fun S hS => (actual_sparse_membership.mp hS).2.2
  by_cases hsmall : Small G 88 = ∅
  · have hsize : ∀ S ∈ G, (info 0).memberFloor ≤ S.card := by
      intro S hS
      by_contra hn
      have hh : S ∈ Small G 88 := Finset.mem_filter.mpr ⟨hS, by change ¬89 ≤ S.card at hn; omega⟩
      rw [hsmall] at hh
      exact Finset.notMem_empty _ hh
    have hn : (86412 : ℝ) ≤ N := by exact_mod_cast hN
    apply False.elim (source_contradiction (w := 0) (by decide) hN hhi hF hcard hsparse hGF
      (hsource 0 (by decide) G hlegal hbad hsize hsparse) ?_)
    norm_num only [RootK, RootCredit, Nat.cast_ofNat]
    change (G.card : ℝ) ≤ G.card+89*N-4094
    linarith only [hn]
  have hsmallne : (Small G 88).Nonempty := Finset.nonempty_iff_ne_empty.mpr hsmall
  by_cases hkernel : Kernel (Ground N) (Small G 88) = ∅
  · have hb := SharpSmall212.actual_small_empty_kernel_whole (by omega : 1 ≤ N)
      (by decide : 2 ≤ 88) hlegal hbad hsmallne hkernel
    have hbR : (G.card : ℝ) ≤ (SmallCount : ℝ)*N := by
      change G.card ≤ SmallCount*N at hb
      exact_mod_cast hb
    exact False.elim (small_contradiction hN hhi hF hcard hbR)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hkernel
  obtain ⟨hcN, hcsmall⟩ := Finset.mem_filter.mp hc
  by_cases hroot : ∀ S ∈ G, c ∈ S
  · exact ⟨c, hcN, fun S hS hbadS => hroot S (Finset.mem_filter.mpr ⟨hS, hbadS⟩)⟩
  have homit : ∃ S ∈ G, c ∉ S := by simpa only [not_forall, exists_prop] using hroot
  obtain ⟨T, hT, hmin⟩ := actual_minimum_omitter homit
  let A := Avoiders G c
  have hAG : A ⊆ G := Finset.filter_subset _ _
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hlegal.1 S (hAG hS), fun S hS U hU hSU => hlegal.2 S (hAG hS) U (hAG hU) hSU⟩
  have hAsize : ∀ S ∈ A, 89 ≤ S.card := by
    intro S hS
    by_contra hn
    have hh : S ∈ Small G 88 := Finset.mem_filter.mpr ⟨hAG hS, by omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  have hp := root_avoider_card_partition G c
  have hpR : (G.card : ℝ) = (RootPart G c).card+A.card := by exact_mod_cast hp.symm
  have hpaid : ∀ w, w < 3 → T.card ≤ RootK w →
      (∀ S ∈ A, (info w).memberFloor ≤ S.card) → False := by
    intro w hw hcut hsize
    have hK : RootK w ≤ 554 := by interval_cases w <;> norm_num [RootK]
    have hr := degree_payment hN hK hlegal hbad hT hcut
    have hcredit : (RootCredit w : ℝ) = (RootK w : ℝ)*((RootK w : ℝ)+3)/2 := by
      interval_cases w <;> norm_num [RootCredit, RootK]
    have hpay : (G.card : ℝ) ≤ A.card+(RootK w : ℝ)*N-(RootCredit w : ℝ) := by
      rw [hcredit]
      linarith only [hpR, hr]
    have hlo : (info w).low ≤ N := by interval_cases w <;> exact hN
    have hupper : N ≤ (info w).high := by interval_cases w <;> exact hhi
    exact source_contradiction hw hlo hupper hF hcard
      (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF)
      (hsource w hw A hA (fun S hS => hbad S (hAG hS)) hsize
        (fun S hS => hsparse S (hAG hS))) hpay
  by_cases h89 : T.card ≤ 89
  · exact False.elim (hpaid 0 (by decide) h89 hAsize)
  by_cases h129 : T.card ≤ 129
  · apply False.elim (hpaid 1 (by decide) h129 ?_)
    intro S hS
    change 90 ≤ S.card
    have hm := hmin S hS
    omega
  by_cases h554 : T.card ≤ 554
  · apply False.elim (hpaid 2 (by decide) h554 ?_)
    intro S hS
    change 130 ≤ S.card
    have hm := hmin S hS
    omega
  have hb := HighRoot86412.actual_high_root hN hhi hlegal hbad hsparse hT (by omega) hmin
  exact False.elim (high_contradiction hN hhi hF hcard hb)

#print axioms original_lower
#print axioms sparse_partition
#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms small_contradiction
#print axioms high_contradiction
#print axioms degree_payment
#print axioms actual_common_root
end
end JSP233.CommonRoot86412
