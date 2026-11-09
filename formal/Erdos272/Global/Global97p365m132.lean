module

public import Erdos272.Global.Global97p94m131
public import Erdos272.Arithmetic.PrimeWindowA132
public import Erdos272.Arithmetic.PrimeWindowB132
public import Erdos272.Arithmetic.PrimeWindowC132
public import Erdos272.Arithmetic.PrimeWindowD132
public import Erdos272.Arithmetic.PrimeWindowE132

@[expose] public section

namespace JSP233.Global97p365m132
open StarCompletion PairRecovery131
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_original_upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 97365000≤N) (hF : Legal (Ground N) F) : F.card≤B N := by
  by_cases hhi : 97940000≤N
  · exact Global97p94m131.actual_original_upper_bound hhi hF
  · have hNu : N<2^49 := by omega
    have cert : ∃C:ℝ,ConstantCertificate N C := by
      by_cases h0 : N≤97370944
      · exact ⟨_,PrimeWindowA132.certificate hN h0⟩
      · by_cases h1 : N≤97397160
        · exact ⟨_,PrimeWindowB132.certificate (by omega) h1⟩
        · by_cases h2 : N≤97568046
          · exact ⟨_,PrimeWindowC132.certificate (by omega) h2⟩
          · by_cases h3 : N≤97818046
            · exact ⟨_,PrimeWindowD132.certificate (by omega) h3⟩
            · exact ⟨_,PrimeWindowE132.certificate (by omega) (by omega)⟩
    obtain ⟨C,hC⟩ := cert
    exact actual_original_upper_of_certificate (by omega) hNu hF hC

theorem actual_value_eq_B (N : ℕ) (hN : 97365000≤N) :
    ExtremalValue45.Value N=B N := by
  apply (ExtremalValue45.exact_value_iff_actual_upper N (by omega)).mpr
  intro F hF
  exact actual_original_upper_bound hN hF

theorem actual_optimal_family (N : ℕ) (hN : 97365000≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N (by omega)
  exact ⟨F,hF,hcard,fun G hG=>by simpa only [hcard] using actual_original_upper_bound hN hG⟩

#print axioms actual_original_upper_bound
#print axioms actual_value_eq_B
#print axioms actual_optimal_family
end
end JSP233.Global97p365m132
