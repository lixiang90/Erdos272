module

public import Erdos272.Global.N200000.WindowPayment200000
public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Global.N200000.HighRoot200000
public import Erdos272.Arithmetic.N200000.ExactResponse200000
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Erdos272.Resources.SharpSmall212
public import Erdos272.Global.GlobalSeven208
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CommonRoot200000
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData200000 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 59400

theorem original_lower {N : ℕ} {F : Finset (Finset ℤ)} (hcard : B N ≤ F.card) :
    (N : ℝ)*((N : ℝ)-1)/2+1 ≤ F.card := by
  have h : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by unfold B at hcard; omega)
  simpa only [Nat.cast_choose_two] using h

theorem sparse_partition {N : ℕ} {F : Finset (Finset ℤ)} :
    ((F.filter IsAP).card : ℝ)+(SparseCrooked N 12 F).card+(Deleted N 12 F).card = F.card := by
  exact_mod_cast actual_original_three_part_partition N 12 F

theorem harmonic_payment {N : ℕ} (hN : 200000 ≤ N) (hhi : N ≤ 233810) :
    (N : ℝ)*Harmonic N ≤ HCommon*N := by
  have caps := LowResourceBridges3040.local_caps (by omega : 100000 ≤ N) (by omega : N ≤ 291011)
  have hh : Harmonic N ≤ HCommon := caps.harmonic_le
  nlinarith only [mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N)]

theorem source_contradiction {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hA : Legal (Ground N) A) (hbad : ∀ S ∈ A, ¬IsAP S)
    (hsize : ∀ S ∈ A, (info w).memberFloor ≤ S.card) (hsparse : ∀ S ∈ A, 12*S.card ≤ N)
    (hAF : A ⊆ F) (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ A.card+594*(N : ℝ)) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hnr : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have hj := ExactResponse200000.actual_joint_exact (by omega : 2 ≤ N) hg.g_positive hF
  have hcast : (((N-1 : ℕ) : ℝ)) = (N : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1 ≤ N)]; norm_num
  rw [hcast] at hj
  have ha := WindowPayment200000.actual_source_for_proof hw hlo hhi hA hbad hsize hsparse hAF
  have hd : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hNhi
  have hupper : (N : ℝ) ≤ (info w).high := by exact_mod_cast hhi
  have hm := ExactResponse200000.margin_min_endpoints (a := (271/800 : ℝ)) (g := G w)
    (loss := Loss) (fee := Fee w+1/(432*(G w)^2)+1295) hn hupper hg.g_positive.le hg.chord
  change min (PayMargin w (info w).low) (PayMargin w (info w).high) ≤ PayMargin w N at hm
  have hpositive : 0 < min (PayMargin w (info w).low) (PayMargin w (info w).high) :=
    lt_min_iff.mpr ⟨hg.low_gap, hg.high_gap⟩
  have hgate := lt_of_lt_of_le hpositive hm
  dsimp only [PayMargin, ExactResponse200000.Margin, Loss] at hgate
  nlinarith only [hj, ha, hd, hp, hb, hh, hG, hgate]

theorem small_contradiction {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (SmallCount w : ℝ)*N) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hnr : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have hlow : (0 : ℝ) < (info w).low := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 200000) hg.low_bound)
  have hn0 : (0 : ℝ) < N := by linarith only [hnr]
  have ha := GlobalSeven208.actual_flat_AP (by omega : 1 ≤ N) hF
  have hd : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN (hhi.trans hg.high_bound)
  have hlin : 0 < (71/800 : ℝ)*N-((SmallCount w : ℝ)+289/2+HCommon)-1296/(info w).low := by
    nlinarith only [hg.small_gap, hn]
  have hc := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 1296/(info w).low by positivity)
  have hcancel : 1296/(info w).low*((info w).low : ℝ) = 1296 := by field_simp
  rw [hcancel] at hc
  have hm := mul_pos hlin hn0
  change ((F.filter IsAP).card : ℝ) ≤ _ at ha
  nlinarith only [ha, hd, hp, hb, hh, hG, hm, hc]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 200000 ≤ N) (hhi : N ≤ 233810) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (200000 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith only [hn]
  have ha := GlobalSeven208.actual_flat_AP (by omega : 1 ≤ N) hF
  have hd : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : (289/2+HCommon+1 : ℝ) < (1/800 : ℝ)*N := by
    norm_num [HCommon]
    linarith only [hn]
  have hm := mul_lt_mul_of_pos_right hlin hn0
  change ((F.filter IsAP).card : ℝ) ≤ _ at ha
  nlinarith only [ha, hd, hp, hb, hh, hG, hm, hn]

theorem actual_common_root {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card) :
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
    exact False.elim (source_contradiction hw hlo hhi hF hcard hlegal hbad hsize hsparse hGF
      (by have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg _; change (G.card : ℝ) ≤ G.card+594*N; linarith only [hn]))
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
  by_cases ht : T.card < 594
  · have hb := actual_degree_from_omitter hlegal hbad (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
    have hd : DegreeBudget N T.card ≤ T.card*N := by
      unfold DegreeBudget
      calc
        _ ≤ ∑ _i ∈ Finset.range T.card, N := Finset.sum_le_sum (fun _ _ => by omega)
        _ = _ := by simp [mul_comm]
    have hr : (RootPart G c).card ≤ 594*N := hb.trans (hd.trans (Nat.mul_le_mul_right N (by omega)))
    have hp := root_avoider_card_partition G c
    have hpay : (G.card : ℝ) ≤ A.card+594*(N : ℝ) := by exact_mod_cast (show G.card ≤ A.card+594*N by dsimp only [A]; omega)
    exact False.elim (source_contradiction hw hlo hhi hF hcard hA
      (fun S hS => hbad S (hAG hS)) hAsize (fun S hS => hsparse S (hAG hS)) (hAG.trans hGF) hpay)
  · have hb := HighRoot200000.actual_high_root hN (by omega : N ≤ 233810) hlegal hbad hsparse hT (by omega) hmin
    exact False.elim (high_contradiction hN hNhi hF hcard hb)

#print axioms original_lower
#print axioms sparse_partition
#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms small_contradiction
#print axioms high_contradiction
#print axioms actual_common_root
end
end JSP233.CommonRoot200000
