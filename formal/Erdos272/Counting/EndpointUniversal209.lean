import Erdos272.Counting.EndpointAP208

namespace JSP233.EndpointUniversal209
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 SimplexMoment57
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_endpoint_bound {N : ℕ} (hN : 2 ≤ N) :
    (EndpointCount (N-1) : ℝ) ≤ (N : ℝ)*(Harmonic N-3/2)+2 := by
  have hid : (EndpointCount (N-1) : ℝ)+((N-1 : ℕ) : ℝ)+(((N-1)/2 : ℕ) : ℝ)=
      (DivCount 1 (N-1) : ℝ) := by exact_mod_cast endpoint_divisor_identity (N-1)
  have hdiv := div_count_one_harmonic (N-1)
  have hprod : ((N-1 : ℕ) : ℝ)*Harmonic (N-1) ≤ (N : ℝ)*Harmonic N :=
    mul_le_mul (by exact_mod_cast Nat.sub_le N 1)
      (harmonic_mono (Nat.sub_le N 1)) (harmonic_nonneg _) (Nat.cast_nonneg N)
  have hf : N ≤ 2*((N-1)/2)+2 := by omega
  have hfR : (N : ℝ) ≤ 2*(((N-1)/2 : ℕ) : ℝ)+2 := by exact_mod_cast hf
  have ht : ((N-1 : ℕ) : ℝ)=(N : ℝ)-1 := by rw [Nat.cast_sub (by omega : 1≤N)]; norm_num
  nlinarith only [hid,hdiv,hprod,hfR,ht]

theorem actual_low_cut_universal {N c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hN : 2≤N) (hc : 1≤c) (hcN : c≤N) :
    ((LowCut F (c : ℤ)).card : ℝ) ≤ (N : ℝ)*(Harmonic N-3/2)+2 := by
  have hnat := (actual_low_cut_parameter_bound hF hcN).trans
    (endpoint_count_mono (by omega : N-c≤N-1))
  have hR : ((LowCut F (c : ℤ)).card : ℝ) ≤ (EndpointCount (N-1) : ℝ) := by exact_mod_cast hnat
  exact hR.trans (actual_endpoint_bound hN)

theorem actual_high_cut_universal {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hL : 2≤L) :
    ((HighCut F (c : ℤ) (L : ℤ)).card : ℝ) ≤ (L : ℝ)*(Harmonic L-3/2)+2 := by
  have hR : ((HighCut F (c : ℤ) (L : ℤ)).card : ℝ) ≤ (EndpointCount (L-1) : ℝ) := by
    exact_mod_cast actual_high_cut_parameter_bound (c:=c) hF (by omega : 1≤L)
  exact hR.trans (actual_endpoint_bound hL)

#print axioms actual_endpoint_bound
#print axioms actual_low_cut_universal
#print axioms actual_high_cut_universal
end
end JSP233.EndpointUniversal209
