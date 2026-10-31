import Erdos272.Certificates.EndpointFinite208.Block071

/-! Finite endpoint bounds assembled from sequentially checked certificate
blocks. Candidate data and all checks live in Certificates/EndpointFinite208.
Each check uses ordinary kernel reduction. -/
namespace JSP233.EndpointFinite208
open StarCompletion APPrepare49 HarmonicAbel29 EndpointAP208 EndpointGate208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false

theorem endpoint_library48_25 {U t : ℕ}
    (hU : 2 ≤ U) (hhigh : U ≤ 853476) (ht : t < U) :
    (EndpointCount t : ℝ) ≤ (U : ℝ) * (Harmonic U - 48 / 25) + 11 := by
  have hm : (EndpointCount t : ℝ) ≤ EndpointCount (U - 1) := by
    exact_mod_cast endpoint_count_mono (show t ≤ U - 1 by omega)
  exact hm.trans (bound071 U hU (by omega))

theorem actual_low_cut48_25 {N c : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hN : 2 ≤ N) (hhigh : N ≤ 853476)
    (hc : 1 ≤ c) (hcN : c ≤ N) :
    ((LowCut F (c : ℤ)).card : ℝ) ≤ (N : ℝ) * (Harmonic N - 48 / 25) + 11 := by
  have hm : ((LowCut F (c : ℤ)).card : ℝ) ≤ EndpointCount (N - c) := by
    exact_mod_cast actual_low_cut_parameter_bound hF hcN
  exact hm.trans (endpoint_library48_25 hN hhigh (by omega))

theorem actual_high_cut48_25 {N c L : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hL : 2 ≤ L) (hhigh : L ≤ 853476) :
    ((HighCut F (c : ℤ) (L : ℤ)).card : ℝ) ≤
      (L : ℝ) * (Harmonic L - 48 / 25) + 11 := by
  have hm : ((HighCut F (c : ℤ) (L : ℤ)).card : ℝ) ≤ EndpointCount (L - 1) := by
    exact_mod_cast actual_high_cut_parameter_bound hF (show 1 ≤ L by omega)
  exact hm.trans (endpoint_library48_25 hL hhigh (by omega))

#print axioms endpoint_library48_25
#print axioms actual_low_cut48_25
#print axioms actual_high_cut48_25
end
end JSP233.EndpointFinite208
