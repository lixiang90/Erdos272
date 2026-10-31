import Erdos272.Core.DenseSharper41
import Erdos272.Arithmetic.HarmonicSharp39
import Erdos272.Foundation.JSP233

/-! Native unbounded dyadic cubic gate and actual retained-family density. -/
namespace JSP233.CrossStartup47
open StarCompletion DenseDeletion40 DenseSharper41
open scoped Classical
noncomputable section

theorem cubic_doubling (J : ℕ) (hJ : 4≤J) : (J+1)^3≤2*J^3 := by
  have hj : (4:ℝ)≤J := by exact_mod_cast hJ
  have hp := mul_nonneg (show (0:ℝ)≤(J:ℝ)-4 by linarith)
    (show (0:ℝ)≤(J:ℝ)^2+J+1 by positivity)
  have hr : ((J:ℝ)+1)^3≤2*(J:ℝ)^3 := by nlinarith only [hp]
  exact_mod_cast hr

theorem cubic_dyadic_growth (J : ℕ) (hJ : 50≤J) :
    468*J^3≤(2:ℕ)^(J-1) := by
  induction J,hJ using Nat.le_induction with
  | base => norm_num
  | succ J hJ ih =>
    have hc := cubic_doubling J (by omega)
    have he : J=J-1+1 := by omega
    have hp : (2:ℕ)^J=2*2^(J-1) := by
      calc
        (2:ℕ)^J=2^(J-1+1) := by rw [←he]
        _=2*2^(J-1) := by rw [pow_succ]; omega
    have hh := Nat.mul_le_mul_left 468 hc
    have hb := Nat.mul_le_mul_left 2 ih
    simpa only [Nat.add_sub_cancel,hp] using (by nlinarith only [hh,hb] : 468*(J+1)^3≤2*2^(J-1))

theorem actual_dyadic_cross_gate (N : ℕ) (hN : 2^49≤N) :
    let J := Nat.log 2 N+1
    50≤J ∧ N<2^J ∧ 468*J^3≤N := by
  have hn0 : N≠0 := by norm_num at hN; omega
  have hlog : 49≤Nat.log 2 N := (Nat.le_log_iff_pow_le (by decide) hn0).mpr hN
  have hj : 50≤Nat.log 2 N+1 := by omega
  refine ⟨hj,Nat.lt_pow_succ_log_self (by decide) N,?_⟩
  have hg : 468*(Nat.log 2 N+1)^3≤(2:ℕ)^(Nat.log 2 N) := by
    simpa only [Nat.add_sub_cancel] using cubic_dyadic_growth (Nat.log 2 N+1) hj
  exact hg.trans (Nat.pow_log_le_self 2 hn0)

theorem actual_retained_near_counter28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    (N:ℝ)^2/2≤(Retained N 28 F).card+3138*(N:ℝ) := by
  have hn : (4*28^2+1)*(2*28-1)≤N :=
    (by norm_num : (4*28^2+1)*(2*28-1)≤(2:ℕ)^49).trans hN
  have hl := actual_retained_sharp_lower (by decide : 0<28) hn hF
  norm_num only [show 4*28^2+1=3137 by norm_num] at hl
  have hb : N.choose 2+1≤F.card := by
    dsimp only [B] at hcounter
    omega
  have hbR : (N:ℝ)*((N:ℝ)-1)/2+1≤F.card := by
    have hh : (N.choose 2:ℝ)+1≤F.card := by exact_mod_cast hb
    simpa only [Nat.cast_choose_two] using hh
  have hlR : (F.card:ℝ)≤(Retained N 28 F).card+3137*(N:ℝ) := by exact_mod_cast hl
  have hnR : (0:ℝ)≤N := Nat.cast_nonneg N
  nlinarith only [hbR,hlR,hnR]

theorem actual_retained_above_cross_gap28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    17*(N:ℝ)^2/36<(Retained N 28 F).card := by
  have hb := actual_retained_near_counter28 hN hF hcounter
  have hn : (112969:ℝ)≤N := by
    exact_mod_cast ((by norm_num : 112969≤(2:ℕ)^49).trans hN)
  have hp := mul_pos (show (0:ℝ)<(N:ℝ)-112968 by linarith)
    (show (0:ℝ)<N by linarith)
  nlinarith only [hp,hb]

theorem actual_retained_card_two28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    2≤(Retained N 28 F).card := by
  have hb := actual_retained_above_cross_gap28 hN hF hcounter
  have hn : (2:ℝ)≤N := by exact_mod_cast ((by norm_num : 2≤(2:ℕ)^49).trans hN)
  by_contra hh
  have hc : ((Retained N 28 F).card:ℝ)≤1 := by exact_mod_cast (by omega : (Retained N 28 F).card≤1)
  have hp := mul_nonneg (show (0:ℝ)≤(N:ℝ)-2 by linarith) (show (0:ℝ)≤(N:ℝ)+2 by positivity)
  nlinarith only [hp,hb,hc]

#print axioms cubic_doubling
#print axioms cubic_dyadic_growth
#print axioms actual_dyadic_cross_gate
#print axioms actual_retained_near_counter28
#print axioms actual_retained_above_cross_gap28
#print axioms actual_retained_card_two28
end
end JSP233.CrossStartup47
