import Erdos272.Counting.MiddleDeficit52
import Erdos272.Arithmetic.DivisorMoment45
import Erdos272.Core.DenseSharper41
import Mathlib.Data.Nat.Log

/-! Actual original-family endpoint stability and explicit unbounded physical
payments.  No eventual statement or supplied retained capacity is used. -/
namespace JSP233.EndpointStability53
open StarCompletion APGeometry DenseDeletion40 FamilyReflect43 RestrictedWitness44
open MiddleDeficit52 DenseSharper41 DivisorMoment45
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 2500000

theorem cube_succ_step {k : ℕ} (hk : 49≤k) : (k+2)^3≤2*(k+1)^3 := by
  have hs : 50*(k+2)≤51*(k+1) := by omega
  have hh := Nat.pow_le_pow_left hs 3
  simp only [mul_pow] at hh
  norm_num only [Nat.reducePow] at hh
  omega

theorem quint_succ_step {k : ℕ} (hk : 49≤k) : (k+2)^5≤2*(k+1)^5 := by
  have hs : 50*(k+2)≤51*(k+1) := by omega
  have hh := Nat.pow_le_pow_left hs 5
  simp only [mul_pow] at hh
  norm_num only [Nat.reducePow] at hh
  omega

theorem cube_gate {k : ℕ} (hk : 49≤k) : 470771616*(k+1)^3≤2^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hs := cube_succ_step hk
    calc
      470771616*(k+1+1)^3≤470771616*(2*(k+1)^3) := Nat.mul_le_mul_left _ hs
      _=2*(470771616*(k+1)^3) := by ring
      _≤2*(2^k) := Nat.mul_le_mul_left _ ih
      _=2^(k+1) := by rw [pow_succ];ring

theorem quint_gate {k : ℕ} (hk : 49≤k) : 25704*(k+1)^5≤2^k := by
  induction k,hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have hs := quint_succ_step hk
    calc
      25704*(k+1+1)^5≤25704*(2*(k+1)^5) := Nat.mul_le_mul_left _ hs
      _=2*(25704*(k+1)^5) := by ring
      _≤2*(2^k) := Nat.mul_le_mul_left _ ih
      _=2^(k+1) := by rw [pow_succ];ring

theorem actual_log_gates {N : ℕ} (hN : 2^49≤N) :
    50≤Nat.log 2 N+1 ∧ 470771616*(Nat.log 2 N+1)^3≤N ∧
      25704*(Nat.log 2 N+1)^5≤N ∧ 16384*(Nat.log 2 N+1)^3≤N := by
  have hn : N≠0 := by norm_num at hN;omega
  have hk : 49≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide : 1<2) hn).mpr hN
  have hp := Nat.pow_log_le_self 2 hn
  have hc := (cube_gate hk).trans hp
  have hq := (quint_gate hk).trans hp
  refine ⟨by omega,hc,hq,?_⟩
  nlinarith only [hc,Nat.zero_le ((Nat.log 2 N+1)^3)]

theorem actual_harmonic_le_log {N : ℕ} (hN : 2^49≤N) :
    HarmonicAbel29.Harmonic N≤(Nat.log 2 N+1:ℕ) := by
  have hj := (actual_log_gates hN).1
  have hjR : (50:ℝ)≤(Nat.log 2 N+1:ℕ) := by exact_mod_cast hj
  have hh := HarmonicSharp39.actual_harmonic_tight N (Nat.log 2 N+1)
    (Nat.lt_pow_succ_log_self (b:=2) (by decide) N)
  linarith only [hh,hjR]

theorem endpoint_polynomial_le_seven {J : ℝ} (hJ : 50≤J) :
    6*J^3+40*J^2+6*J+3166≤7*J^3 := by
  have h0 : 0≤J := by linarith only [hJ]
  have hp : 0≤(J-50)*(J^2+10*J+494) := mul_nonneg (sub_nonneg.mpr hJ) (by positivity)
  nlinarith only [hp]

theorem actual_counter_endpoint_square {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card)
    (hc : c∈Finset.Icc 1 N) (hcL : c≤L) (hLR : L≤R) (hRN : R≤N)
    (hraw : (F.card:ℝ)≤(N:ℝ)^2/2-((L:ℝ)+(N-R))^2/102+
      (Deleted N 28 F).card+(WitnessException (Ground N) c:ℝ)+
      40*N*(HarmonicAbel29.Harmonic N)^2+6*N*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3) :
    (L+N-R)^2≤714*N*(Nat.log 2 N+1)^3 := by
  let J := Nat.log 2 N+1
  have hn : 1≤N := by norm_num at hN;omega
  have hnR : (1:ℝ)≤N := by exact_mod_cast hn
  have hJ : (50:ℝ)≤J := by exact_mod_cast (actual_log_gates hN).1
  have hH0 := HarmonicAbel29.harmonic_nonneg N
  have hHJ := actual_harmonic_le_log hN
  change HarmonicAbel29.Harmonic N≤(J:ℝ) at hHJ
  have hD : (Deleted N 28 F).card≤3137*N := by
    apply actual_deleted_sharp (by decide : 0<28) (by norm_num;norm_num at hN;omega) hF
  have hDR : ((Deleted N 28 F).card:ℝ)≤3137*(N:ℝ) := by exact_mod_cast hD
  have hcG : (c:ℤ)∈Ground N := (mem_ground N _).mpr (by have hh:=Finset.mem_Icc.mp hc;omega)
  have hW := actual_exception_harmonic hcG
  have hWJ : (WitnessException (Ground N) c:ℝ)≤6*(N:ℝ)*(J:ℝ)^3 := by
    apply hW.trans
    gcongr
  have hH2 : 40*(N:ℝ)*(HarmonicAbel29.Harmonic N)^2≤40*N*(J:ℝ)^2 := by gcongr
  have hH1 : 6*(N:ℝ)*HarmonicAbel29.Harmonic N≤6*N*(J:ℝ) := by gcongr
  have hdiff : (L-c:ℕ)≤N := by omega
  have hdiffR : ((L-c:ℕ):ℝ)≤N := by exact_mod_cast hdiff
  have hchoose : N.choose 2≤F.card := by unfold B at hcounter;omega
  have hchooseR : ((N.choose 2):ℝ)≤F.card := by exact_mod_cast hchoose
  rw [Nat.cast_choose_two] at hchooseR
  have hsq : ((L:ℝ)+(N-R))^2≤102*(N:ℝ)*(6*(J:ℝ)^3+40*(J:ℝ)^2+6*(J:ℝ)+3166) := by
    nlinarith only [hraw,hDR,hWJ,hH2,hH1,hdiffR,hchooseR,hnR]
  have hp := mul_le_mul_of_nonneg_left (endpoint_polynomial_le_seven hJ)
    (show (0:ℝ)≤102*(N:ℝ) by positivity)
  have ht : ((L+N-R:ℕ):ℝ)=(L:ℝ)+(N:ℝ)-R := by
    rw [Nat.cast_sub (by omega : R≤L+N),Nat.cast_add]
  have htR : (((L+N-R)^2:ℕ):ℝ)≤714*(N:ℝ)*(J:ℝ)^3 := by
    rw [Nat.cast_pow,ht]
    nlinarith only [hsq,hp]
  exact_mod_cast htR

theorem physical_payments_of_endpoint {N L R : ℕ} (hN : 2^49≤N)
    (_hLR : L≤R) (hRN : R≤N)
    (hsq : (L+N-R)^2≤714*N*(Nat.log 2 N+1)^3) :
    812*(L+N-R)≤N ∧ 6*(L+N-R)*(Nat.log 2 N+1)≤N ∧
      32*L≤N ∧ 16384*(Nat.log 2 N+1)^3≤N := by
  obtain ⟨_hJ,hc,hq,hJ3⟩ := actual_log_gates hN
  have h812sq : (812*(L+N-R))^2≤N^2 := by
    calc
      _=812^2*(L+N-R)^2 := by ring
      _≤812^2*(714*N*(Nat.log 2 N+1)^3) := Nat.mul_le_mul_left _ hsq
      _=N*(470771616*(Nat.log 2 N+1)^3) := by ring
      _≤N*N := Nat.mul_le_mul_left _ hc
      _=N^2 := by ring
  have h6sq : (6*(L+N-R)*(Nat.log 2 N+1))^2≤N^2 := by
    calc
      _=(36*(Nat.log 2 N+1)^2)*(L+N-R)^2 := by ring
      _≤(36*(Nat.log 2 N+1)^2)*(714*N*(Nat.log 2 N+1)^3) := Nat.mul_le_mul_left _ hsq
      _=N*(25704*(Nat.log 2 N+1)^5) := by ring
      _≤N*N := Nat.mul_le_mul_left _ hq
      _=N^2 := by ring
  have h812 := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp h812sq
  have h6 := (Nat.pow_le_pow_iff_left (by decide : 2≠0)).mp h6sq
  exact ⟨h812,h6,by omega,hJ3⟩

theorem actual_original_prepared_payments28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃c∈Finset.Icc 1 N,∃L R:ℕ,c<L ∧ L≤R ∧ R≤N ∧
        (∀S∈Retained N 28 H,¬IsAP S→(c:ℤ)∈S) ∧
        (∃P∈Avoiders (Retained N 28 H) c,∀z∈P,(L:ℤ)≤z) ∧
        (∃T∈Avoiders (Retained N 28 H) c,∀z∈T,z≤(R:ℤ)) ∧
        (∀S∈Avoiders (Retained N 28 H) c,
          (∃a∈S,a≤(L:ℤ) ∧ ∀z∈S,a≤z) ∧ ∃b∈S,(R:ℤ)≤b ∧ ∀z∈S,z≤b) ∧
        (L+N-R)^2≤714*N*(Nat.log 2 N+1)^3 ∧
        812*(L+N-R)≤N ∧ 6*(L+N-R)*(Nat.log 2 N+1)≤N ∧
        32*L≤N ∧ 16384*(Nat.log 2 N+1)^3≤N := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hraw⟩ :=
    actual_original_prepared_endpoint102 hN hF hcounter
  have hs := actual_counter_endpoint_square hN hF hcounter hc hLc.le hLR hRN hraw
  obtain ⟨h812,h6,h32,hJ3⟩ := physical_payments_of_endpoint hN hLR hRN hs
  exact ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,hs,h812,h6,h32,hJ3⟩

#print axioms cube_succ_step
#print axioms quint_succ_step
#print axioms cube_gate
#print axioms quint_gate
#print axioms actual_log_gates
#print axioms actual_harmonic_le_log
#print axioms endpoint_polynomial_le_seven
#print axioms actual_counter_endpoint_square
#print axioms physical_payments_of_endpoint
#print axioms actual_original_prepared_payments28
end
end JSP233.EndpointStability53
