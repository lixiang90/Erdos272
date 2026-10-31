import Erdos272.Resources.RegionalBootstrap209
import Erdos272.Counting.OneSided47

namespace JSP233.RegionalCross209
open StarCompletion APGeometry OneSided47 Straddling47 NonIntervalAP47 HarmonicAbel29
open scoped Classical
noncomputable section
set_option maxHeartbeats 0

theorem actual_all_cross_root_gap_of_cap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {H : ℝ}
    (hN : 705098 ≤ N) (hc : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S) (hout : ∃P∈F,c∉P)
    (hH : Harmonic N≤H) (hgate1 : 6*H^3+H+6≤(N : ℝ)/36)
    (hgate2 : 6*H^3+4≤(5/144 : ℝ)*N) :
    (F.card : ℝ)≤17*(N : ℝ)^2/36 := by
  have hn0 : (0 : ℝ)≤N := Nat.cast_nonneg _
  have hn1 : (1 : ℝ)≤N := by exact_mod_cast (by omega : 1≤N)
  have hH0 := harmonic_nonneg N
  have hH3 : Harmonic N^3≤H^3 := by gcongr
  have hcube := mul_le_mul_of_nonneg_left hH3 (show (0 : ℝ)≤6*N by positivity)
  by_cases hlarge : LargeStepAvoider F c
  · obtain ⟨P,hP,hcP,d,hd,p,hAP⟩ := hlarge
    have hb := NonIntervalAP47.actual_large_step_straddling_count
      (by omega : 6≤N) hc hF hroot hcross hP hcP (by exact_mod_cast hd) hAP
    have hlin := mul_le_mul_of_nonneg_left hH hn0
    have hpaid := mul_le_mul_of_nonneg_right hgate1 hn0
    nlinarith only [hb,hlin,hcube,hpaid]
  · have hb := OneSided47.actual_two_step_straddling_count hc hF hroot hcross hlarge hout
    have hpaid := mul_le_mul_of_nonneg_right hgate2 hn0
    nlinarith only [hb,hcube,hpaid,hn1]

theorem actual_all_cross_root_gap {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hN : 705098 ≤ N) (hhigh : N≤2000000) (hc : c∈Ground N)
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hcross : ∀S∈F,c∉S→StraddlesRoot c S) (hout : ∃P∈F,c∉P) :
    (F.card : ℝ)≤17*(N : ℝ)^2/36 := by
  by_cases hsmall : N≤1000000
  · have hh := HarmonicLog55.actual_refined_harmonic_upper (J := 20)
      (by omega : 63≤N) (by omega : N<1000001)
    have hcap : Harmonic N≤(29/2 : ℝ) := hh.trans (by
      norm_num [HarmonicLog55.HarmonicUpper,HarmonicLog55.LogUpper])
    have hn : (705098 : ℝ)≤N := by exact_mod_cast hN
    exact actual_all_cross_root_gap_of_cap hN hc hF hroot hcross hout hcap
      (by norm_num; linarith only [hn]) (by norm_num; linarith only [hn])
  · have hcap := RegionalBootstrap209.harmonic_cap (by omega : 10902≤N) hhigh
    have hn : (1000000 : ℝ)≤N := by exact_mod_cast (by omega : 1000000≤N)
    exact actual_all_cross_root_gap_of_cap hN hc hF hroot hcross hout hcap
      (by norm_num; linarith only [hn]) (by norm_num; linarith only [hn])

#print axioms actual_all_cross_root_gap
end
end JSP233.RegionalCross209
