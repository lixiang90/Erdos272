module

public import Erdos272.Global.N151879.WindowGates151879
public import Erdos272.Counting.N158375.DenseJoint158375
public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Global.N153080.HighRoot153080
public import Erdos272.Resources.SharpSmall212

@[expose] public section

namespace JSP233.CommonRoot151879
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData151879 WindowGates151879 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

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

theorem harmonic_payment {N : ℕ} (hN : 151879 ≤ N) (hhi : N ≤ 179999) :
    (N : ℝ)*Harmonic N ≤ HCommon*N := by
  have caps := LocalRecovery158375.actual_caps (by omega : 100000 ≤ N) hhi
  have hh : Harmonic N ≤ HCommon := caps.harmonic_le.trans
    (by norm_num [LocalRecovery158375.HLocal, HCommon])
  nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N)]

theorem source_contradiction {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w < 1) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F)
    (hinner : (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ A.card+554*(N : ℝ)-154289) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hupper : (N : ℝ) ≤ (info w).high := by exact_mod_cast hhi
  have hj := DenseJoint158375.actual_AP_inner_with_deleted
    (by omega : 15000 ≤ N) (by omega : N ≤ 2^18) hF hAF hsparse
    hg.g_positive hg.dense_payment hinner
  have hcast : (((N-1 : ℕ) : ℝ)) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N)]
    norm_num
  rw [hcast] at hj
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hNhi
  have hm := ExactResponse200000.margin_min_endpoints
    (a := (271/800 : ℝ)-CoeffA w) (g := G w) (loss := Loss w)
    (fee := CoeffC w+1/(432*(G w)^2)-154290)
    hn hupper hg.g_positive.le hg.chord
  change min (PayMargin w (info w).low) (PayMargin w (info w).high) ≤ PayMargin w N at hm
  have hpositive : 0 < min (PayMargin w (info w).low) (PayMargin w (info w).high) :=
    lt_min_iff.mpr ⟨hg.low_gap, hg.high_gap⟩
  have hgate := lt_of_lt_of_le hpositive hm
  dsimp only [PayMargin, ExactResponse200000.Margin, Loss, Fee] at hgate hj
  nlinarith only [hj, hp, hb, hh, hG, hgate]

theorem small_contradiction {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 1) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (SmallCount w : ℝ)*N) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (hhi.trans hg.high_bound) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN (hhi.trans hg.high_bound)
  have hlin : 0 < (71/800 : ℝ)*N-((SmallCount w : ℝ)+HCommon) := by
    nlinarith only [hg.small_gap, hn]
  have hm := mul_pos hlin hn0
  nlinarith only [ha, hp, hb, hh, hG, hm]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 151879 ≤ N) (hhi : N ≤ 179999) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (151879 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N) hhi hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : HCommon < (1/800 : ℝ)*N := by
    norm_num [HCommon]
    linarith only [hn]
  have hm := mul_lt_mul_of_pos_right hlin hn0
  nlinarith only [ha, hp, hb, hh, hG, hm]

theorem actual_common_root {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 1) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) (hsource : SourceBound N w) :
    ∃ c ∈ Ground N, ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S := by
  let G := SparseCrooked N 12 F
  let M := (info w).memberFloor
  have hGF : G ⊆ F := actual_sparse_subset N 12 F
  have hlegal : Legal (Ground N) G := actual_sparse_legal hF
  have hbad : ∀ S ∈ G, ¬IsAP S := fun S hS => (actual_sparse_membership.mp hS).2.1
  have hsparse : ∀ S ∈ G, 12*S.card ≤ N := fun S hS => (actual_sparse_membership.mp hS).2.2
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hM := hg.member_three
  by_cases hsmall : Small G (M-1) = ∅
  · have hsize : ∀ S ∈ G, (info w).memberFloor ≤ S.card := by
      intro S hS
      by_contra hn
      have hh : S ∈ Small G (M-1) := Finset.mem_filter.mpr ⟨hS, by dsimp only [M] at *; omega⟩
      rw [hsmall] at hh
      exact Finset.notMem_empty _ hh
    have hn : (151879 : ℝ) ≤ N := by exact_mod_cast hN
    exact False.elim (source_contradiction hw hlo hhi hF hcard hsparse hGF
      (hsource G hlegal hbad hsize hsparse)
      (by change (G.card : ℝ) ≤ G.card+554*N-154289; linarith only [hn]))
  have hsmallne : (Small G (M-1)).Nonempty := Finset.nonempty_iff_ne_empty.mpr hsmall
  by_cases hk : Kernel (Ground N) (Small G (M-1)) = ∅
  · have hb := SharpSmall212.actual_small_empty_kernel_whole (by omega : 1 ≤ N)
      (by dsimp only [M]; omega : 2 ≤ M-1) hlegal hbad hsmallne hk
    have hbR : (G.card : ℝ) ≤ (SmallCount w : ℝ)*N := by
      have he : (M-1-1)^2+(M-1) = SmallCount w := by rfl
      rw [he] at hb
      exact_mod_cast hb
    exact False.elim (small_contradiction hw hlo hhi hF hcard hbR)
  obtain ⟨c, hc⟩ := Finset.nonempty_iff_ne_empty.mpr hk
  obtain ⟨hcN, hcsmall⟩ := Finset.mem_filter.mp hc
  by_cases hroot : ∀ S ∈ G, c ∈ S
  · exact ⟨c, hcN, fun S hS hbadS => hroot S (Finset.mem_filter.mpr ⟨hS, hbadS⟩)⟩
  have homit : ∃ S ∈ G, c ∉ S := by simpa only [not_forall, exists_prop] using hroot
  obtain ⟨T, hT, hmin⟩ := actual_minimum_omitter homit
  let A := Avoiders G c
  have hAG : A ⊆ G := Finset.filter_subset _ _
  have hA : Legal (Ground N) A :=
    ⟨fun S hS => hlegal.1 S (hAG hS), fun S hS U hU hSU => hlegal.2 S (hAG hS) U (hAG hU) hSU⟩
  have hAsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card := by
    intro S hS
    by_contra hn
    have hh : S ∈ Small G (M-1) := Finset.mem_filter.mpr
      ⟨hAG hS, by dsimp only [M] at *; omega⟩
    exact (Finset.mem_filter.mp hS).2 (hcsmall S hh)
  by_cases ht : T.card < 555
  · have hb := actual_degree_from_omitter hlegal hbad
      (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
    have hd := degreeBudget_mono N (by omega : T.card ≤ 554)
    have hr : ((RootPart G c).card : ℝ) ≤ 554*(N : ℝ)-154289 := by
      have hn : (151879 : ℝ) ≤ N := by exact_mod_cast hN
      have he := degreeBudget_real_upper N 554 554 (by omega) (by omega)
        (by norm_num : (554 : ℝ) ≤ 554) (by linarith only [hn])
      have hbR : ((RootPart G c).card : ℝ) ≤ DegreeBudget N 554 := by exact_mod_cast hb.trans hd
      nlinarith only [hbR, he]
    have hp := root_avoider_card_partition G c
    have hpR : (G.card : ℝ) = (RootPart G c).card+A.card := by exact_mod_cast hp.symm
    have hpay : (G.card : ℝ) ≤ A.card+554*(N : ℝ)-154289 := by linarith only [hpR, hr]
    exact False.elim (source_contradiction hw hlo hhi hF hcard
      (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF)
      (hsource A hA (fun S hS => hbad S (hAG hS)) hAsize (fun S hS => hsparse S (hAG hS))) hpay)
  · have hb := HighRoot153080.actual_high_root (by omega : 151879 ≤ N) hNhi hlegal hbad hsparse hT (by omega) hmin
    exact False.elim (high_contradiction hN hNhi hF hcard hb)

#print axioms original_lower
#print axioms sparse_partition
#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms small_contradiction
#print axioms high_contradiction
#print axioms actual_common_root
end
end JSP233.CommonRoot151879
