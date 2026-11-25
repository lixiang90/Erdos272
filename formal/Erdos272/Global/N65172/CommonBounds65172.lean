module

public import Erdos272.Global.N80470.CommonBounds80470
public import Erdos272.Arithmetic.N80470.Harmonic80470
public import Erdos272.Global.N65172.WindowGates65172
public import Erdos272.Counting.N65172.SmallGates65172

@[expose] public section

namespace JSP233.CommonBounds65172
open StarCompletion APGeometry DenseDeletion40 Density41 SparseSmall39 PrivateFinset
open SevenFamily208 HarmonicAbel29 WindowData65172 WindowGates65172 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option Elab.async false

def WitnessCondition (w : ℕ) (F : Finset (Finset ℤ)) : Prop :=
  w<7 → ∃ A₀∈F, A₀.card≤Witness w

def SourceBound (N w : ℕ) (F : Finset (Finset ℤ)) : Prop :=
  ∀ A : Finset (Finset ℤ), Legal (Ground N) A →
    (∀ S ∈ A, ¬IsAP S) → (∀ S ∈ A, (info w).memberFloor ≤ S.card) →
    (∀ S ∈ A, 12*S.card ≤ N) → A⊆F → WitnessCondition w F →
    (A.card : ℝ) ≤ 6*G w*(∑ S ∈ A, ((Pool S).card : ℝ))+Fee w N

theorem harmonic_payment {N : ℕ} (hN : 65172≤N) (hhi : N≤65967) :
    (N : ℝ)*Harmonic N≤HCommon*N := by
  have hh := Harmonic82427.actual_cap (by omega : 10000≤N) (by omega : N≤84363)
  have hb := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) N)
  simpa only [HCommon,mul_comm] using hb

theorem source_contradiction {N w : ℕ} {F A : Finset (Finset ℤ)}
    (hw : w<8) (hlo : (info w).low≤N) (hhi : N≤(info w).high)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hsparse : ∀ S∈A, 12*S.card≤N) (hAF : A⊆F)
    (hinner : (A.card : ℝ)≤6*G w*(∑ S∈A, ((Pool S).card : ℝ))+Fee w N)
    (hG : ((SparseCrooked N 12 F).card : ℝ)≤
      A.card+(RootK w : ℝ)*(N : ℝ)-(RootCredit w : ℝ)) : False := by
  have hg := gates hw
  have hN := hg.low_bound.trans hlo
  have hNhi := hhi.trans hg.high_bound
  have hn : ((info w).low : ℝ)≤N := by exact_mod_cast hlo
  have hupper : (N : ℝ)≤(info w).high := by exact_mod_cast hhi
  have hcast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one]
  have hcap : 3*G w*((N-1 : ℕ) : ℝ)≤1 := by
    rw [hcast]
    have hh := mul_le_mul_of_nonneg_left (sub_le_sub_right hupper 1)
      (show 0≤3*G w by linarith only [hg.g_positive])
    exact hh.trans hg.shadow_cap
  have hj : ((F.filter IsAP).card : ℝ)+(A.card : ℝ)+((Deleted N 12 F).card : ℝ)≤
      (129/800+QuadraticExtra w : ℝ)*(N : ℝ)^2+EffectiveG w*((N-1 : ℕ) : ℝ)^3+
        Penalty w+(N : ℝ)*Harmonic N+Fee w N := by
    have hb := DenseJoint88404.actual_AP_inner_with_deleted
      (by omega : 15000≤N) (by omega : N≤2^18) hF hAF hsparse
      hg.g_positive hg.dense_payment hcap hinner
    simpa only [EffectiveG,Penalty,QuadraticExtra,SieveConstants88404.alpha_one,
      mul_comm] using hb
  rw [hcast] at hj
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
  have hh := harmonic_payment hN hNhi
  have hm := ExactResponse200000.margin_min_endpoints
    (a := (271/800 : ℝ)-CoeffA w-QuadraticExtra w) (g := EffectiveG w) (loss := Loss w)
    (fee := CoeffC w+Penalty w-((RootCredit w : ℝ)+1))
    hn hupper hg.effective_positive.le hg.chord
  change min (PayMargin w (info w).low) (PayMargin w (info w).high)≤PayMargin w N at hm
  have hpositive : 0<min (PayMargin w (info w).low) (PayMargin w (info w).high) :=
    lt_min_iff.mpr ⟨hg.low_gap,hg.high_gap⟩
  have hgate := lt_of_lt_of_le hpositive hm
  dsimp only [PayMargin,ExactResponse200000.Margin,Loss,Fee] at hgate hj
  nlinarith only [hj,hp,hb,hh,hG,hgate]

theorem harmonic_shift_payment {N : ℕ} (hN : 65172≤N) (hhi : N≤65967) :
    (((N-1 : ℕ) : ℝ))*Harmonic (N-1)≤
      SmallData65172.HSmall*(((N-1 : ℕ) : ℝ)) := by
  have hh := (harmonic_mono (Nat.sub_le N 1)).trans
    (Harmonic80470.actual_cap (by omega : 10000≤N) (by omega : N≤82427))
  have hp := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α := ℝ) (N-1))
  simpa only [SmallData65172.HSmall,mul_comm] using hp

theorem small_policy_contradiction {N p : ℕ} {F : Finset (Finset ℤ)}
    (hp : p<2) (hN : (SmallData65172.policy p).low≤N)
    (hhi : N≤(SmallData65172.policy p).high)
    (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ)≤
      ((SmallData65172.policy p).coefficient : ℝ)*N-(SmallData65172.policy p).credit) :
    False := by
  have hg := SmallGates65172.gates hp
  have hlo := hg.low_bound.trans hN
  have hupper := hhi.trans hg.high_bound
  have hn : ((SmallData65172.policy p).low : ℝ)≤N := by exact_mod_cast hN
  have ha := APTail12880470.actual_flat_AP_deleted (by omega : 16513≤N)
    (by omega : N≤179999) hF
  have hpartition := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := OriginalLower80470.original_quarter_lower hcard
  have hh := harmonic_shift_payment hlo hupper
  have hcast : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤N),Nat.cast_one]
  rw [hcast] at hh
  dsimp only [AP128Family80470.Flat] at ha
  rw [hcast] at ha
  have hgate := SmallGates65172.small_margin_positive hp hn
  dsimp only [SmallData65172.SmallMargin,SmallData65172.Leading,
    SmallData65172.SmallLoss,SmallData65172.SmallConstant] at hgate
  norm_num only [AP128Family80470.A,AP128Family80470.Nu,AP128Family80470.C] at ha
  nlinarith only [ha,hpartition,hb,hh,hG,hgate]

theorem high_contradiction {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 65172≤N) (hhi : N≤65967) (hF : Legal (Ground N) F) (hcard : B N≤F.card)
    (hG : ((SparseCrooked N 12 F).card : ℝ)≤(7/80 : ℝ)*(N : ℝ)^2) : False := by
  have hn : (65172 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  have ha := DenseJoint158375.actual_flat_AP_deleted (by omega : 15000≤N)
    (by omega : N≤179999) hF
  have hp := CommonRoot84364.sparse_partition (N := N) (F := F)
  have hb := CommonRoot84364.original_lower hcard
  have hh := harmonic_payment hN hhi
  have hlin : HCommon<(1/800 : ℝ)*N := by
    norm_num [HCommon]
    linarith only [hn]
  have hm := mul_lt_mul_of_pos_right hlin hn0
  nlinarith only [ha,hp,hb,hh,hG,hm]

#print axioms harmonic_payment
#print axioms source_contradiction
#print axioms harmonic_shift_payment
#print axioms small_policy_contradiction
#print axioms high_contradiction
end
end JSP233.CommonBounds65172
