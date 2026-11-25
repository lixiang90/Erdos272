module

public import Erdos272.Global.N84364.CommonRoot84364
public import Erdos272.Global.N80470.WindowGates80470
public import Erdos272.Arithmetic.N82427.Harmonic82427
public import Erdos272.Counting.N80470.OriginalLower80470
public import Erdos272.Counting.N80470.APTail12880470

@[expose] public section

namespace JSP233.CommonBounds80470
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData80470 WindowGates80470 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def WitnessCondition (w : ℕ) (F : Finset (Finset ℤ)) : Prop :=
  w<3 → ∃ A₀∈F, A₀.card≤Witness w

def SourceBound (N w : ℕ) (F : Finset (Finset ℤ)) : Prop :=
  ∀ A : Finset (Finset ℤ), Legal (Ground N) A →
    (∀ S ∈ A, ¬IsAP S) → (∀ S ∈ A, (info w).memberFloor ≤ S.card) →
    (∀ S ∈ A, 12*S.card ≤ N) → A⊆F → WitnessCondition w F →
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N

theorem harmonic_payment {N : ℕ} (hN : 80470 ≤ N) (hhi : N ≤ 82425) :
    (N : ℝ)*Harmonic N ≤ HCommon*N := by
  have hh := Harmonic82427.actual_cap (by omega : 10000 ≤ N) (by omega : N≤84363)
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

theorem harmonic_shift_payment {N : ℕ} (hN : 80470≤N) (hhi : N≤82425) :
    (((N-1 : ℕ) : ℝ))*Harmonic (N-1)≤HCommon*(((N-1 : ℕ) : ℝ)) := by
  have hh := (harmonic_mono (Nat.sub_le N 1)).trans
    (Harmonic82427.actual_cap (by omega : 10000≤N) (by omega : N≤84363))
  have hp := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) (N-1))
  simpa only [HCommon, mul_comm] using hp

theorem small_low_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 80470≤N) (hhi : N≤82425)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ)≤7141*N-610556) : False := by
  have hn : (80470 : ℝ)≤N := by exact_mod_cast hN
  have ha := APTail12880470.actual_flat_AP_deleted (by omega : 16513≤N)
    (by omega : N≤179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := OriginalLower80470.original_quarter_lower hcard
  have hh := harmonic_shift_payment hN hhi
  have hcast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N), Nat.cast_one]
  rw [hcast] at hh
  dsimp only [AP128Family80470.Flat] at ha
  rw [hcast] at ha
  have hgate := small_low_gate hn
  norm_num only [SmallLowMargin,SmallMargin,SmallLowCount,SmallLowCredit,
    Nat.cast_ofNat] at hgate
  norm_num only [AP128Family80470.A,AP128Family80470.Nu,AP128Family80470.C] at ha
  nlinarith only [ha,hp,hb,hh,hG,hgate]

theorem small_upper_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 81427≤N) (hhi : N≤82425)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ)≤7226*N-621437) : False := by
  have hn : (81427 : ℝ)≤N := by exact_mod_cast hN
  have ha := APTail12880470.actual_flat_AP_deleted (by omega : 16513≤N)
    (by omega : N≤179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := OriginalLower80470.original_quarter_lower hcard
  have hh := harmonic_shift_payment (by omega) hhi
  have hcast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N), Nat.cast_one]
  rw [hcast] at hh
  dsimp only [AP128Family80470.Flat] at ha
  rw [hcast] at ha
  have hgate := small_upper_gate hn
  norm_num only [SmallUpperMargin,SmallMargin,SmallUpperCount,SmallUpperCredit,
    Nat.cast_ofNat] at hgate
  norm_num only [AP128Family80470.A,AP128Family80470.Nu,AP128Family80470.C] at ha
  nlinarith only [ha,hp,hb,hh,hG,hgate]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 80470 ≤ N) (hhi : N ≤ 82425) (hF : Legal (Ground N) F) (hcard : B N ≤ F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ) ≤ (7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (80470 : ℝ) ≤ N := by exact_mod_cast hN
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
#print axioms harmonic_shift_payment
#print axioms small_low_contradiction
#print axioms small_upper_contradiction
#print axioms high_contradiction
#print axioms degree_payment
end
end JSP233.CommonBounds80470
