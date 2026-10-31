import Erdos272.Global.Global64p660617m137
import Erdos272.Resources.HalfRecovery138
import Erdos272.Arithmetic.HalfIntervalA138
import Erdos272.Arithmetic.HalfIntervalB138
import Erdos272.Arithmetic.HalfIntervalC138
import Erdos272.Arithmetic.HalfIntervalD138
import Erdos272.Arithmetic.HalfIntervalE138
import Erdos272.Arithmetic.HalfIntervalF138

namespace JSP233.Global63p917403m138
open StarCompletion
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_window_certificate {N:ℕ} (hN:63917403≤N) (hhi:N≤64660617) :
    ∃C:ℝ,HalfWindowCertificate137.HalfConstantCertificate N C := by
  by_cases hA : 63995345≤N
  · exact ⟨_,HalfIntervalA138.certificate hA hhi⟩
  by_cases hB : 63925487≤N
  · exact ⟨_,HalfIntervalB138.certificate hB (by omega)⟩
  by_cases hC : 63918317≤N
  · exact ⟨_,HalfIntervalC138.certificate hC (by omega)⟩
  by_cases hD : 63917477≤N
  · exact ⟨_,HalfIntervalD138.certificate hD (by omega)⟩
  by_cases hE : 63917409≤N
  · exact ⟨_,HalfIntervalE138.certificate hE (by omega)⟩
  exact ⟨_,HalfIntervalF138.certificate hN (by omega)⟩

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 63917403≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hhi : 64660617≤N
  · exact Global64p660617m137.actual_original_upper_bound hhi hF
  · have hNhi : N≤64660617 := by omega
    obtain ⟨C,hC⟩ := actual_window_certificate hN hNhi
    exact HalfRecovery138.actual_original_upper_of_certificate hN hNhi
      (by norm_num;omega : N<2^49) hF hC

theorem actual_value_eq_B (N : ℕ) (hN : 63917403≤N) : ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 63917403≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_window_certificate
#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global63p917403m138
