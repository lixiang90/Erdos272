module

public import Erdos272.Global.N84364.CommonRoot84364
public import Erdos272.Global.N82427.WindowGates82427
public import Erdos272.Arithmetic.N82427.Harmonic82427

@[expose] public section

namespace JSP233.CommonBounds82427
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData82427 WindowGates82427 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def SourceBound (N w : ℕ) : Prop :=
  ∀ A : Finset (Finset ℤ), Legal (Ground N) A →
    (∀ S ∈ A, ¬IsAP S) → (∀ S ∈ A, (info w).memberFloor ≤ S.card) →
    (∀ S ∈ A, 12*S.card ≤ N) →
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N

theorem harmonic_payment {N : ℕ} (hN : 82427 ≤ N) (hhi : N ≤ 84363) :
    (N : ℝ)*Harmonic N ≤ HCommon*N := by
  have hh := Harmonic82427.actual_cap (by omega : 10000 ≤ N) hhi
  have hb := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N)
  simpa only [HCommon, mul_comm] using hb

theorem source_contradiction {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w < 4) (hlo : (info w).low ≤ N) (hhi : N ≤ (info w).high)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hsparse : ∀ S ∈ A, 12*S.card ≤ N) (hAF : A ⊆ F)
    (hinner : (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤
      A.card+(RootK w : ℝ)*(N : ℝ)-(RootCredit w : ℝ)) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hn : ((info w).low : ℝ) ≤ N := by exact_mod_cast hlo
  have hupper : (N : ℝ) ≤ (info w).high := by exact_mod_cast hhi
  have hj : ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ) ≤
      (129/800+QuadraticExtra w : ℝ)*(N : ℝ)^2+EffectiveG w*((N-1 : ℕ) : ℝ)^3+
        Penalty w+(N : ℝ)*Harmonic N+Fee w N := by
    by_cases hlow : w < 3
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
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  rw [hcast] at hj
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
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

theorem small_low_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427 ≤ N) (hhi : N ≤ 84363)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ 7311*N-632402) : False := by
  have hn : (82427 : ℝ) ≤ N := by exact_mod_cast hN
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (by omega : N ≤ 179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
  have hh := harmonic_payment hN hhi
  have hgate := small_low_gate hn
  norm_num only [SmallLowMargin, SmallLowCount, SmallLowCredit, Nat.cast_ofNat] at hgate
  nlinarith only [ha, hp, hb, hh, hG, hgate]

theorem small_upper_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 83395 ≤ N) (hhi : N ≤ 84363)
    (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ 7397*N-643540) : False := by
  have hn : (83395 : ℝ) ≤ N := by exact_mod_cast hN
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (by omega : N ≤ 179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
  have hh := harmonic_payment (by omega) hhi
  have hgate := small_upper_gate hn
  norm_num only [SmallUpperMargin, SmallUpperCount, SmallUpperCredit, Nat.cast_ofNat] at hgate
  nlinarith only [ha, hp, hb, hh, hG, hgate]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427 ≤ N) (hhi : N ≤ 84363) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (82427 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000 ≤ N)
    (by omega : N ≤ 179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : HCommon < (1/800 : ℝ)*N := by
    norm_num [HCommon]
    linarith only [hn]
  have hm := mul_lt_mul_of_pos_right hlin hn0
  nlinarith only [ha, hp, hb, hh, hG, hm]

theorem degree_payment {N K : ℕ} {G : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (hN : 2 ≤ N) (hK : K+2 ≤ N) (hlegal : Legal (Ground N) G)
    (hbad : ∀ S ∈ G, ¬IsAP S) (hT : T ∈ Avoiders G c) (hcut : T.card ≤ K) :
    ((RootPart G c).card : ℝ) ≤ (K : ℝ)*N-(K : ℝ)*((K : ℝ)+3)/2 := by
  have hb := actual_degree_from_omitter hlegal hbad
    (Finset.mem_filter.mp hT).1 (Finset.mem_filter.mp hT).2
  have hd := degreeBudget_mono N hcut
  have hkR : (K : ℝ)+2 ≤ N := by exact_mod_cast hK
  have he := degreeBudget_real_upper N K (K : ℝ) hN (by omega)
    (le_refl _) (by linarith only [hkR])
  have hbR : ((RootPart G c).card : ℝ) ≤ DegreeBudget N K := by exact_mod_cast hb.trans hd
  nlinarith only [hbR, he]

#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms small_low_contradiction
#print axioms small_upper_contradiction
#print axioms high_contradiction
#print axioms degree_payment
end
end JSP233.CommonBounds82427
