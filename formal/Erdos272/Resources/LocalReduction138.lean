module

public import Erdos272.Resources.PairRecovery131
public import Erdos272.Global.CroftKernel138
public import Mathlib.Data.Nat.Choose.Cast

@[expose] public section
namespace JSP233.LocalReduction138
open StarCompletion APGeometry CoprimeDensity52 MiddleJoint51 MiddleDeficit52
open PreparedClasses50 APPrepare49 PreparedWitness48 MiddleCoordinates51
open DenseDeletion40 DenseSharper41 FamilyReflect43 RestrictedWitness44 LongTerminal35
open LinearOmitters43 OutsideEnvelope43 OneSided47 Straddling47 APCount41
open HarmonicAbel29 HarmonicLog55 RawEndpoint112 RawEndpoint115 PairRecovery131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_log_gates {N : ℕ} (hN : 63917403≤N) (hhi : N≤64660617) :
    let J := Nat.log 2 N+1
    26≤J ∧ J≤49 ∧ N<2^J ∧ 1024*J^3≤N ∧ 468*J^3≤N := by
  obtain ⟨hJl,hJu,hpow,_hfixed⟩ := CroftKernel138.actual_log_gates hN hhi
  dsimp only at hJl hJu hpow ⊢
  have hcube := Nat.pow_le_pow_left hJu 3
  refine ⟨hJl,by omega,hpow,?_,?_⟩ <;> norm_num at hcube ⊢ <;> omega


theorem actual_retained_near11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 63917403≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    (N:ℝ)^2/2≤(Retained N 11 F).card+486*(N:ℝ) := by
  have hd := actual_retained_sharp_lower (r:=11) (by decide : 0<11)
    (by norm_num;omega) hF
  have hdR : (F.card:ℝ)≤(Retained N 11 F).card+485*(N:ℝ) := by exact_mod_cast hd
  have hb : N.choose 2+1≤F.card := by unfold B at hcard;omega
  have hbR : (N:ℝ)*((N:ℝ)-1)/2+1≤F.card := by
    have hh : (N.choose 2:ℝ)+1≤F.card := by exact_mod_cast hb
    simpa only [Nat.cast_choose_two] using hh
  have hn : (0:ℝ)≤N := Nat.cast_nonneg N
  nlinarith only [hdR,hbR,hn]

theorem actual_retained_above_cross_gap11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 63917403≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    17*(N:ℝ)^2/36<(Retained N 11 F).card := by
  have hb := actual_retained_near11 hN hF hcard
  have hn : (63917403:ℝ)≤N := by exact_mod_cast hN
  have hp := mul_pos (show (0:ℝ)<(N:ℝ)-17496 by linarith only [hn])
    (show (0:ℝ)<N by linarith only [hn])
  nlinarith only [hp,hb]

theorem actual_retained_card_two11 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 63917403≤N) (hF : Legal (Ground N) F) (hcard : B N≤F.card) :
    2≤(Retained N 11 F).card := by
  have hb := actual_retained_above_cross_gap11 hN hF hcard
  have hn : (2:ℝ)≤N := by exact_mod_cast (show 2≤N by omega)
  by_contra hh
  have hc : ((Retained N 11 F).card:ℝ)≤1 := by
    exact_mod_cast (by omega : (Retained N 11 F).card≤1)
  have hp := mul_nonneg (show (0:ℝ)≤(N:ℝ)-2 by linarith only [hn])
    (show (0:ℝ)≤(N:ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 63917403≤N) (hhi : N≤64660617) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S) (hout : ∃P∈F,c∉P) :
    (F.card:ℝ)≤17*(N:ℝ)^2/36 := by
  let J := Nat.log 2 N+1
  obtain ⟨hJl,_hJu,hNJ,_hbig,hscale⟩ := actual_log_gates hN hhi
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P,hP,hcP,d,hd,p,hAP⟩ := hlarge
    exact NonIntervalAP47.actual_large_step_straddling_gap
      (by omega : 6≤N) hNJ hscale hcN hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
  · exact actual_two_step_straddling_gap (by omega : 1≤N) (by omega : 4≤J)
      hNJ hscale hcN hF hroot hcross hlarge hout

theorem actual_near_one_sided_reduction {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 63917403≤N) (hhi : N≤64660617) (hcN : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hnear : 17*(N:ℝ)^2/36<F.card) :
    Rooted F c ∨ ∃P∈F,c∉P ∧ ((∀x∈P,x<c) ∨ ∀x∈P,c<x) := by
  by_cases hr : Rooted F c
  · exact Or.inl hr
  · apply Or.inr
    by_contra hn
    have hcross := actual_no_one_sided_cross hn
    have hout : ∃P∈F,c∉P := by
      change ¬∀P∈F,c∈P at hr
      push Not at hr
      exact hr
    have hb := actual_all_cross_root_gap hN hhi hcN hF hroot hcross hout
    linarith only [hb,hnear]


#print axioms actual_log_gates
#print axioms actual_retained_near11
#print axioms actual_retained_above_cross_gap11
#print axioms actual_retained_card_two11
#print axioms actual_all_cross_root_gap
#print axioms actual_near_one_sided_reduction
end
end JSP233.LocalReduction138
