import Erdos272.Arithmetic.FullPrefix209_021
namespace JSP233.TotientWindow209
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
private theorem window_le_limit : 720896 ≤ FactorFullData209.Limit := by decide
theorem actual_bounds (t : Nat) (ht : 1 ≤ t) (htN : t ≤ 720896) :
    (500000000 / 822467033 : Real) * t - 17 / 200 ≤
        ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n ∧
    (500000000 / 822467033 : Real) * (t : Real)^2 / 2 - (61 / 200) * t ≤
        ((∑ n ∈ Finset.Icc 2 t, Nat.totient n : Nat) : Real) := by
  exact @FrontierCheck209.actual_bounds FactorFullCertificate209.phi t (fun n hn => FactorFullCertificate209.phi_correct n (hn.trans (htN.trans window_le_limit)))
    (FullPrefix209_021.good t ht htN).1
theorem mass_upper (t : Nat) (htN : t ≤ 720896) :
    (∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n) ≤
      (76 / 125 : Real) * t + 579 / 1000 := by
  by_cases ht0 : t = 0
  · subst t
    norm_num
  · exact @DualFrontier209.actual_upper FactorFullCertificate209.phi t
      (fun n hn => FactorFullCertificate209.phi_correct n (hn.trans (htN.trans window_le_limit)))
      (FullPrefix209_021.good t (by omega) htN).2
theorem bounds (t : Nat) (htN : t ≤ 720896) :
    (500000000 / 822467033 : Real) * t - 17 / 200 ≤
        ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n ∧
    (500000000 / 822467033 : Real) * (t : Real)^2 / 2 - (61 / 200) * t ≤
        ((∑ n ∈ Finset.Icc 2 t, Nat.totient n : Nat) : Real) := by
  by_cases ht0 : t = 0
  · subst t
    norm_num
  · exact actual_bounds t (by omega) htN
theorem weakened_bounds {rho : Real} (hrho : rho ≤ 500000000 / 822467033)
    (t : Nat) (htN : t ≤ 720896) :
    rho * t - 17 / 200 ≤ ∑ n ∈ Finset.Icc 1 t, (Nat.totient n : Real) / n ∧
    rho * (t : Real)^2 / 2 - (61 / 200) * t ≤
        ((∑ n ∈ Finset.Icc 2 t, Nat.totient n : Nat) : Real) := by
  obtain ⟨hF, hU⟩ := bounds t htN
  have hrt := mul_le_mul_of_nonneg_right hrho (by positivity : (0 : Real) ≤ t)
  have hrt2 := mul_le_mul_of_nonneg_right hrho (sq_nonneg (t : Real))
  constructor <;> nlinarith only [hF, hU, hrt, hrt2]
#print axioms actual_bounds
#print axioms mass_upper
#print axioms weakened_bounds
end JSP233.TotientWindow209
