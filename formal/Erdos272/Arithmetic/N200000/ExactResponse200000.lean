module

public import Erdos272.Arithmetic.N291012.ShadowResponse291012
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.ExactResponse200000
open StarCompletion APGeometry HarmonicAbel29 IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem response_identity {g x : ℝ} (hg : g ≠ 0) (hx : x ≠ 0) :
    ShadowResponse291012.Response (g*x)*x^2 = g*x^3+1/(432*g^2) := by
  unfold ShadowResponse291012.Response
  field_simp [hg, hx]

theorem actual_joint_exact {N : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 2 ≤ N) (hg : 0 < g) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800 : ℝ)*(N : ℝ)^2+g*((N-1 : ℕ) : ℝ)^3+
        1/(432*g^2)+(N : ℝ)*Harmonic N := by
  have h := ShadowResponse291012.actual_joint hN (le_refl N) hg hF
  have hx : (((N-1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show N-1 ≠ 0 by omega)
  rw [response_identity hg.ne' hx] at h
  simpa only [add_assoc] using h

def Margin (a g loss fee n : ℝ) : ℝ := a*n^2-g*(n-1)^3-loss*n-fee

theorem margin_chord {a g loss fee lo hi n : ℝ} :
    (hi-lo)*Margin a g loss fee n-
      ((hi-n)*Margin a g loss fee lo+(n-lo)*Margin a g loss fee hi) =
        (n-lo)*(hi-n)*(hi-lo)*(g*(n+lo+hi-3)-a) := by
  unfold Margin
  ring

theorem margin_min_endpoints {a g loss fee lo hi n : ℝ}
    (hlo : lo ≤ n) (hhi : n ≤ hi) (hg : 0 ≤ g)
    (hcurve : a ≤ g*(2*lo+hi-3)) :
    min (Margin a g loss fee lo) (Margin a g loss fee hi) ≤ Margin a g loss fee n := by
  by_cases he : lo = hi
  · have hn : n = lo := by linarith only [hlo, hhi, he]
    simp only [hn, he, min_self, le_refl]
  have hlt : lo < hi := lt_of_le_of_ne (hlo.trans hhi) he
  have hwidth : 0 < hi-lo := sub_pos.mpr hlt
  have hlast : 0 ≤ g*(n+lo+hi-3)-a := by
    have h := mul_nonneg hg (sub_nonneg.mpr hlo)
    nlinarith only [hcurve, h]
  have hproduct := mul_nonneg
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hhi)) hwidth.le) hlast
  have hchord := margin_chord (a := a) (g := g) (loss := loss) (fee := fee)
    (lo := lo) (hi := hi) (n := n)
  have hleft := mul_le_mul_of_nonneg_left
    (min_le_left (Margin a g loss fee lo) (Margin a g loss fee hi)) (sub_nonneg.mpr hhi)
  have hright := mul_le_mul_of_nonneg_left
    (min_le_right (Margin a g loss fee lo) (Margin a g loss fee hi)) (sub_nonneg.mpr hlo)
  have hscaled : (hi-lo)*min (Margin a g loss fee lo) (Margin a g loss fee hi) ≤
      (hi-lo)*Margin a g loss fee n := by
    nlinarith only [hproduct, hchord, hleft, hright]
  exact (mul_le_mul_iff_right₀ hwidth).mp hscaled

#print axioms response_identity
#print axioms actual_joint_exact
#print axioms margin_chord
#print axioms margin_min_endpoints
end
end JSP233.ExactResponse200000
