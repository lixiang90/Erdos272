module

public import Erdos272.Global.N233811.WindowPayment233811
public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Arithmetic.N250262.ResearchMethods3066
public import Erdos272.Resources.N291012.LowResourceBridges3040
public import Erdos272.Resources.SharpSmall212
public import Erdos272.Global.GlobalSeven208
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.CommonRoot233811
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData233811 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 59400

theorem quadratic_positive {delta low loss constant n : ℝ}
    (hn : low ≤ n) (hd : 0 ≤ delta) (hs : 0 ≤ 2*delta*low-loss)
    (hg : 0 < delta*low^2-loss*low-constant) : 0 < delta*n^2-loss*n-constant := by
  have hp := mul_nonneg hd (sq_nonneg (n-low))
  have hq := mul_nonneg hs (sub_nonneg.mpr hn)
  nlinarith only [hg, hp, hq]

theorem original_lower {N : ℕ} {F : Finset (Finset ℤ)} (hcard : B N ≤ F.card) :
    (N : ℝ)*((N : ℝ)-1)/2+1 ≤ F.card := by
  have h : (N.choose 2 : ℝ)+1 ≤ F.card := by
    exact_mod_cast (show N.choose 2+1 ≤ F.card by unfold B at hcard; omega)
  simpa only [Nat.cast_choose_two] using h

theorem sparse_partition {N : ℕ} {F : Finset (Finset ℤ)} :
    ((F.filter IsAP).card : ℝ)+(SparseCrooked N 12 F).card+(Deleted N 12 F).card = F.card := by
  exact_mod_cast actual_original_three_part_partition N 12 F

theorem harmonic_payment {N : ℕ} (hN : 233811 ≤ N) (hhi : N ≤ 243613) :
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
  have hnr : (233811 : ℝ) ≤ N := by exact_mod_cast hN
  have hj := ShadowResponse291012.actual_joint (by omega : 2 ≤ N) hhi hg.g_positive hF
  change ((F.filter IsAP).card : ℝ)+6*G w*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
    (129/800 : ℝ)*(N : ℝ)^2+Response w*((N-1 : ℕ) : ℝ)^2+(N : ℝ)*Harmonic N at hj
  have hsq : (((N-1 : ℕ) : ℝ))^2 ≤ (N : ℝ)^2 := by
    exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le N 1) 2
  have hresponse := mul_le_mul_of_nonneg_left hsq hg.response_nonnegative
  have ha := WindowPayment233811.actual_source_for_proof hw hlo hhi hA hbad hsize hsparse hAF
  have hd : ((Deleted N 12 F).card : ℝ) ≤ 144*(N : ℝ)+1296 := by
    exact_mod_cast RootModel291012.deleted_affine (by omega : 15853 ≤ N) hF
  have hp := sparse_partition (N := N) (F := F)
  have hb := original_lower hcard
  have hh := harmonic_payment hN hNhi
  have hbase : 0 < Delta w*((info w).low : ℝ)^2-Loss w*(info w).low-(FeeC w+1295) := by
    nlinarith only [hg.low_gap]
  have hgate := quadratic_positive hn hg.delta_nonnegative hg.low_slope hbase
  dsimp only [Delta, Loss, Fee] at hgate ha
  nlinarith only [hj, hresponse, ha, hd, hp, hb, hh, hG, hgate]

theorem small_contradiction {N w : ℕ} {F : Finset (Finset ℤ)}
    (hw : w < 3) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (SmallCount w : ℝ)*N) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hnr : (233811 : ℝ) ≤ N := by exact_mod_cast hN
  have hlow : (0 : ℝ) < (info w).low := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 233811) hg.low_bound)
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
    (hN : 233811 ≤ N) (hhi : N ≤ 243613) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (233811 : ℝ) ≤ N := by exact_mod_cast hN
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
  · have hb := ResearchMethods3066.actual_high_root (by omega : 220000 ≤ N) (by omega : N ≤ 250261) hlegal hbad hsparse hT (by omega) hmin
    exact False.elim (high_contradiction hN hNhi hF hcard hb)

#print axioms quadratic_positive
#print axioms original_lower
#print axioms sparse_partition
#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms small_contradiction
#print axioms high_contradiction
#print axioms actual_common_root
end
end JSP233.CommonRoot233811
