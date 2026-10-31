import Erdos272.Counting.EndpointDensity54
import Erdos272.Counting.EndpointExterior55
import Erdos272.Arithmetic.DivisorMoment45
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! Actual harmonic sums and explicit real logarithm windows.  The actual
exception is bounded using the native harmonic moment theorem; the sharper
log-simplex moment is kept as an explicit, separate conditional statement. -/
namespace JSP233.HarmonicLog55
open HarmonicAbel29 EndpointDensity54 DivisorMoment45
open StarCompletion APGeometry RestrictedWitness44 DenseDeletion40 FamilyReflect43
open LongTerminal35
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def LogUpper (J hi : ℕ) : ℝ :=
  (J:ℝ)*(173287/250000)-((2:ℝ)^J-hi)/(2:ℝ)^J

def HarmonicUpper (J hi : ℕ) : ℝ := LogUpper J hi+293/500

def SimplexPolynomial (L H : ℝ) : ℝ := L^3/3+3*L^2+6*L+2+4*H

def NativeTailPolynomial (J hi D : ℕ) : ℝ :=
  81*(6*(HarmonicUpper J hi)^3+40*(HarmonicUpper J hi)^2+6*HarmonicUpper J hi+28+D+1)

def NativeTailPolynomial67 (J hi D : ℕ) : ℝ :=
  67*(6*(HarmonicUpper J hi)^3+40*(HarmonicUpper J hi)^2+6*HarmonicUpper J hi+28+D+1)

theorem actual_log_two_lower :
    (149337754816/215448838605:ℝ)≤Real.log 2 := by
  exact (by norm_num : (149337754816/215448838605:ℝ)≤0.6931471803).trans
    Real.log_two_gt_d9.le

theorem actual_log_two_upper : Real.log 2≤(173287/250000:ℝ) := by
  exact Real.log_two_lt_d9.le.trans (by norm_num)

theorem actual_harmonic63 :
    Harmonic 63=(310559566510213034489743057/65681493561267903750631200:ℝ) := by
  norm_num [Harmonic,Finset.sum_Icc_succ_top]

theorem actual_log63_lower :
    6*(149337754816/215448838605:ℝ)-1/63≤Real.log 63 := by
  have hlog64 : Real.log (64:ℝ)=6*Real.log 2 := by
    calc
      _=Real.log ((2:ℝ)^6) := by norm_num
      _=6*Real.log 2 := by rw [Real.log_pow];norm_num
  have hr := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<64/63)
  rw [Real.log_div (by norm_num) (by norm_num),hlog64] at hr
  linarith only [hr,actual_log_two_lower]

theorem actual_harmonic_log_mono {M N : ℕ} (hM : 1≤M) (hMN : M≤N) :
    Harmonic N-Real.log N≤Harmonic M-Real.log M := by
  have hh := Real.strictAnti_eulerMascheroniSeq'.antitone hMN
  have hm : M≠0 := by omega
  have hn : N≠0 := by omega
  simpa only [Real.eulerMascheroniSeq',hm,hn,if_false,←harmonic_eq_cast] using hh

theorem actual_harmonic_log_586 {N : ℕ} (hN : 63≤N) :
    Harmonic N≤Real.log N+293/500 := by
  have hm := actual_harmonic_log_mono (by decide : 1≤63) hN
  norm_num only [Nat.cast_ofNat] at hm
  have hb : Harmonic 63-(6*(149337754816/215448838605:ℝ)-1/63)≤293/500 := by
    rw [actual_harmonic63]
    norm_num
  linarith only [hm,hb,actual_log63_lower]

theorem actual_refined_log_upper {N hi J : ℕ} (hN : 1≤N) (hhi : N<hi) :
    Real.log N≤LogUpper J hi := by
  have hp : (0:ℝ)<(2:ℝ)^J := by positivity
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hr := Real.log_le_sub_one_of_pos (div_pos hn hp)
  rw [Real.log_div hn.ne' hp.ne',Real.log_pow] at hr
  have hj : (J:ℝ)*Real.log 2≤(J:ℝ)*(173287/250000) :=
    mul_le_mul_of_nonneg_left actual_log_two_upper (Nat.cast_nonneg J)
  have hh : (N:ℝ)/(2:ℝ)^J≤(hi:ℝ)/(2:ℝ)^J :=
    div_le_div_of_nonneg_right (by exact_mod_cast hhi.le) hp.le
  have he : ((2:ℝ)^J-hi)/(2:ℝ)^J=1-(hi:ℝ)/(2:ℝ)^J := by
    field_simp
  dsimp only [LogUpper]
  rw [he]
  linarith only [hr,hj,hh]

theorem actual_refined_harmonic_upper {N hi J : ℕ} (hN : 63≤N) (hhi : N<hi) :
    Harmonic N≤HarmonicUpper J hi := by
  have hh := actual_harmonic_log_586 hN
  have hl := actual_refined_log_upper (J:=J) (by omega) hhi
  dsimp only [HarmonicUpper]
  linarith only [hh,hl]

theorem actual_refined_bounds_nonneg {N hi J : ℕ} (hN : 63≤N) (hhi : N<hi) :
    0≤LogUpper J hi ∧ 0≤HarmonicUpper J hi := by
  have hl := actual_refined_log_upper (J:=J) (by omega) hhi
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have h0 := Real.log_nonneg hn
  refine ⟨by linarith only [hl,h0],?_⟩
  exact (harmonic_nonneg N).trans (actual_refined_harmonic_upper hN hhi)

theorem actual_window_log_le_dyadic {J hi : ℕ} (hhi : hi≤2^J) :
    LogUpper J hi≤(J:ℝ)*(173287/250000) := by
  have hh : (hi:ℝ)≤(2:ℝ)^J := by exact_mod_cast hhi
  have hn : 0≤((2:ℝ)^J-hi)/(2:ℝ)^J := div_nonneg (sub_nonneg.mpr hh) (by positivity)
  dsimp only [LogUpper]
  linarith only [hn]

theorem actual_exception_refined_harmonic {N hi J : ℕ} {c : ℤ}
    (hN : 63≤N) (hhi : N<hi) (hc : c∈Ground N) :
    (WitnessException (Ground N) c:ℝ)≤6*(N:ℝ)*(HarmonicUpper J hi)^3 := by
  apply (actual_exception_harmonic hc).trans
  have hh := actual_refined_harmonic_upper (J:=J) hN hhi
  have h0 := harmonic_nonneg N
  gcongr

theorem actual_simplex_polynomial_refined {N hi J : ℕ}
    (hN : 63≤N) (hhi : N<hi) :
    SimplexPolynomial (Real.log N) (Harmonic N)≤
      SimplexPolynomial (LogUpper J hi) (HarmonicUpper J hi) := by
  have hl := actual_refined_log_upper (J:=J) (by omega) hhi
  have hh := actual_refined_harmonic_upper (J:=J) hN hhi
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have h0 := Real.log_nonneg hn
  dsimp only [SimplexPolynomial]
  gcongr

theorem actual_conditional_simplex_exception {N hi J : ℕ} {c : ℤ}
    (hN : 63≤N) (hhi : N<hi)
    (hsimplex : (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*SimplexPolynomial (Real.log N) (Harmonic N)) :
    (WitnessException (Ground N) c:ℝ)≤
      (N:ℝ)*SimplexPolynomial (LogUpper J hi) (HarmonicUpper J hi) := by
  exact hsimplex.trans (mul_le_mul_of_nonneg_left (actual_simplex_polynomial_refined hN hhi)
    (Nat.cast_nonneg N))

theorem actual_harmonic_error_refined {N hi J : ℕ} (hN : 63≤N) (hhi : N<hi) :
    40*(N:ℝ)*(Harmonic N)^2+6*N*Harmonic N≤
      40*N*(HarmonicUpper J hi)^2+6*N*HarmonicUpper J hi := by
  have hh := actual_refined_harmonic_upper (J:=J) hN hhi
  have h0 := harmonic_nonneg N
  gcongr

theorem actual_prepared_CM_EM_refined81 {N c L R hi J : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} (x p:Finset ℤ→ℤ) (hN : 63≤N) (hhi : N<hi)
    (hF : Legal (Ground N) F) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈F,¬IsAP S→(c:ℤ)∈S) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hW : ∀S∈PreparedWitness48.PreparedCrooked F c L,
      IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ (L:ℤ)<p S) :
    ((PreparedClasses50.CM (PreparedWitness48.PreparedCrooked F c L) p R).card:ℝ)+
      (PreparedClasses50.EM (APPrepare49.PreparedAP F c L) c R).card+
      ((R:ℝ)+(2/3)*L)*(N-R)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81+
        (40*HarmonicUpper J hi+2)*N*HarmonicUpper J hi := by
  have hb := actual_prepared_CM_EM_endpoint81 x p (by omega) hF hcL hLR hRN hroot hP hLP hW
  have hh := actual_refined_harmonic_upper (J:=J) hN hhi
  have h0 := harmonic_nonneg N
  have hu0 : 0≤HarmonicUpper J hi := h0.trans hh
  have he : (40*Harmonic N+2)*(N:ℝ)*Harmonic N≤
      (40*HarmonicUpper J hi+2)*N*HarmonicUpper J hi := by gcongr
  linarith only [hb,he]

def PreparedContext28 (N : ℕ) (F H : Finset (Finset ℤ)) (c L R : ℕ) : Prop :=
  (H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
    (Deleted N 28 H).card=(Deleted N 28 F).card ∧
    (Retained N 28 H).card=(Retained N 28 F).card ∧
    c∈Finset.Icc 1 N ∧ c<L ∧ L≤R ∧ R≤N ∧
    (∀S∈Retained N 28 H,¬IsAP S→(c:ℤ)∈S) ∧
    (∃P∈Avoiders (Retained N 28 H) c,∀z∈P,(L:ℤ)≤z) ∧
    (∃T∈Avoiders (Retained N 28 H) c,∀z∈T,z≤(R:ℤ)) ∧
    (∀S∈Avoiders (Retained N 28 H) c,
      (∃a∈S,a≤(L:ℤ) ∧ ∀z∈S,a≤z) ∧ ∃b∈S,(R:ℤ)≤b ∧ ∀z∈S,z≤b)

theorem actual_original_refined_endpoint28 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/81+(Deleted N 28 F).card+
        6*N*(HarmonicUpper J hi)^3+40*N*(HarmonicUpper J hi)^2+
          6*N*HarmonicUpper J hi+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hraw⟩ :=
    actual_original_prepared_endpoint81 hN hF hcounter
  have h63 : 63≤N := by norm_num at hN;omega
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by
    have hh:=Finset.mem_Icc.mp hc
    omega)
  have hW := actual_exception_refined_harmonic (J:=J) h63 hhi hcG
  have herror := actual_harmonic_error_refined (J:=J) h63 hhi
  refine ⟨H,c,L,R,⟨hHF,hLH,hcard,hD,hG,hc,hLc,hLR,hRN,hroot,hP,hT,henv⟩,?_⟩
  linarith only [hraw,hW,herror]

theorem actual_original_refined_tail28 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (((L+N-R:ℕ):ℝ)^2≤NativeTailPolynomial J hi 3137*N) := by
  obtain ⟨H,c,L,R,hcontext,hraw⟩ := actual_original_refined_endpoint28 (J:=J) hN hhi hF hcounter
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hkeep := hcontext
  obtain ⟨_hHF,_hLH,_hcard,_hD,_hG,_hc,hcL,hLR,hRN,_hroot,_hP,_hT,_henv⟩ := hcontext
  have hD : (Deleted N 28 F).card≤3137*N := by
    apply DenseSharper41.actual_deleted_sharp (by decide : 0<28) (by norm_num;norm_num at hN;omega) hF
  have hDR : ((Deleted N 28 F).card:ℝ)≤3137*(N:ℝ) := by exact_mod_cast hD
  have hdiff : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter;omega
  have hchooseR : ((N.choose 2):ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hchooseR
  have ht : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-R := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
  refine ⟨H,c,L,R,hkeep,?_⟩
  dsimp only [NativeTailPolynomial]
  norm_num only [Nat.cast_ofNat]
  rw [ht]
  nlinarith only [hraw,hDR,hdiff,hchooseR,hn]

theorem actual_original_refined_endpoint67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/67+(Deleted N 28 F).card+
        6*N*(HarmonicUpper J hi)^3+40*N*(HarmonicUpper J hi)^2+
          6*N*HarmonicUpper J hi+24*N+(L-c:ℕ)+3 := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hraw⟩ :=
    EndpointExterior55.actual_original_prepared_endpoint67 hN hF hcounter
  have h63 : 63≤N := by norm_num at hN;omega
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by
    have hh:=Finset.mem_Icc.mp hc
    omega)
  have hW := actual_exception_refined_harmonic (J:=J) h63 hhi hcG
  have herror := actual_harmonic_error_refined (J:=J) h63 hhi
  refine ⟨H,c,L,R,⟨hHF,hLH,hcard,hD,hG,hc,hLc,hLR,hRN,hroot,hP,hT,henv⟩,?_⟩
  linarith only [hraw,hW,herror]

theorem actual_original_refined_tail67 {N hi J : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hhi : N<hi) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),∃c L R:ℕ,PreparedContext28 N F H c L R ∧
      (((L+N-R:ℕ):ℝ)^2≤NativeTailPolynomial67 J hi 3137*N) := by
  obtain ⟨H,c,L,R,hcontext,hraw⟩ := actual_original_refined_endpoint67 (J:=J) hN hhi hF hcounter
  have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by omega)
  have hkeep := hcontext
  obtain ⟨_hHF,_hLH,_hcard,_hD,_hG,_hc,hcL,hLR,hRN,_hroot,_hP,_hT,_henv⟩ := hcontext
  have hD : (Deleted N 28 F).card≤3137*N := by
    apply DenseSharper41.actual_deleted_sharp (by decide : 0<28) (by norm_num;norm_num at hN;omega) hF
  have hDR : ((Deleted N 28 F).card:ℝ)≤3137*(N:ℝ) := by exact_mod_cast hD
  have hdiff : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast (show L-c≤N by omega)
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter;omega
  have hchooseR : ((N.choose 2):ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hchooseR
  have ht : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-R := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
  refine ⟨H,c,L,R,hkeep,?_⟩
  dsimp only [NativeTailPolynomial67]
  norm_num only [Nat.cast_ofNat]
  rw [ht]
  nlinarith only [hraw,hDR,hdiff,hchooseR,hn]

#print axioms actual_log_two_lower
#print axioms actual_log_two_upper
#print axioms actual_harmonic63
#print axioms actual_log63_lower
#print axioms actual_harmonic_log_mono
#print axioms actual_harmonic_log_586
#print axioms actual_refined_log_upper
#print axioms actual_refined_harmonic_upper
#print axioms actual_refined_bounds_nonneg
#print axioms actual_window_log_le_dyadic
#print axioms actual_exception_refined_harmonic
#print axioms actual_simplex_polynomial_refined
#print axioms actual_conditional_simplex_exception
#print axioms actual_harmonic_error_refined
#print axioms actual_prepared_CM_EM_refined81
#print axioms actual_original_refined_endpoint28
#print axioms actual_original_refined_tail28
#print axioms actual_original_refined_endpoint67
#print axioms actual_original_refined_tail67
end
end JSP233.HarmonicLog55
