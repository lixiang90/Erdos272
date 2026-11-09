module

public import Erdos272.Arithmetic.N291012.UnitShadowGeometry291012
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.ShadowResponse291012
open StarCompletion APGeometry HarmonicAbel29 UnitCount218 IntrinsicTriples208
open APShadowCapacity16858 UnitShadowGeometry291012
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Response (t : ℝ) : ℝ := t+1/(432*t^2)

theorem cubic_max {x a : ℝ} (hx : 0 ≤ x) (ha : 0 < a) :
    x^2-8*a*x^3 ≤ 1/(432*a^2) := by
  have hh := mul_nonneg (sq_nonneg (12*a*x-1))
    (show 0 ≤ 24*a*x+1 by positivity)
  apply (le_div_iff₀ (show 0 < 432*a^2 by positivity)).mpr
  nlinarith only [hh]

theorem cap_response {n cap y g : ℝ} (hn : 0 < n) (hg : 0 < g)
    (hcap : n ≤ cap) (hy : 0 ≤ y) (hyN : y^2 ≤ n^2/4) :
    y^2+g*n^3-8*g*y^3 ≤ Response (g*cap)*n^2 := by
  let a := g*cap
  have ha : 0 < a := mul_pos hg (hn.trans_le hcap)
  have hytwo : 2*y ≤ n := by
    by_contra hh
    have hp := mul_pos (show 0 < 2*y-n by linarith only [hh])
      (show 0 < 2*y+n by linarith only [hy, hn])
    nlinarith only [hp, hyN]
  have hcube : 0 ≤ n^3-8*y^3 := by
    have hp := mul_nonneg (sub_nonneg.mpr hytwo)
      (show 0 ≤ n^2+2*n*y+4*y^2 by positivity)
    nlinarith only [hp]
  have heff : g ≤ a/n := (le_div_iff₀ hn).mpr (mul_le_mul_of_nonneg_left hcap hg.le)
  have hmono := mul_le_mul_of_nonneg_right heff hcube
  have hmax := cubic_max hy (div_pos ha hn)
  have hid : (a/n)*n^3+1/(432*(a/n)^2) = Response a*n^2 := by
    unfold Response
    field_simp [hn.ne', ha.ne']
  calc
    _ = y^2+g*(n^3-8*y^3) := by ring
    _ ≤ y^2+(a/n)*(n^3-8*y^3) := by linarith only [hmono]
    _ ≤ (a/n)*n^3+1/(432*(a/n)^2) := by nlinarith only [hmax]
    _ = _ := hid

theorem actual_joint {N cap : ℕ} {F : Finset (Finset ℤ)} {g : ℝ}
    (hN : 2 ≤ N) (hcap : N ≤ cap) (hg : 0 < g) (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ)+6*g*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800 : ℝ)*(N : ℝ)^2+
        Response (g*(cap-1 : ℕ))*((N-1 : ℕ) : ℝ)^2+(N : ℝ)*Harmonic N := by
  obtain ⟨y, hy, hyN, hu, hshadow⟩ := actual_unit_geometry hF
  have hsub : UnitAP F ⊆ F := Finset.filter_subset _ _
  have hAP : ∀ S ∈ UnitAP F, IsAP S := fun S hS => (Finset.mem_filter.mp hS).2.1
  have hc := actual_AP_family_capacity hF hsub hAP
  rw [ground_card] at hc
  have hcR : (∑ S ∈ F, ((Pool S).card : ℝ))+
      ((APShadow (UnitAP F)).card : ℝ) ≤ (N.choose 3 : ℝ) := by exact_mod_cast hc
  have hncast : ((N-1 : ℕ) : ℝ) = (N : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hchoose := APResidual208.cast_choose_three N
  have hcapacity : 6*(∑ S ∈ F, ((Pool S).card : ℝ))+
      6*((APShadow (UnitAP F)).card : ℝ) ≤
      ((N-1 : ℕ) : ℝ)^3-((N-1 : ℕ) : ℝ) := by
    rw [hncast]
    nlinarith only [hcR, hchoose]
  have hpool : 6*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤ ((N-1 : ℕ) : ℝ)^3-8*y^3 := by
    linarith only [hcapacity, hshadow]
  have hresponse := cap_response (n := ((N-1 : ℕ) : ℝ)) (cap := ((cap-1 : ℕ) : ℝ))
    (by exact_mod_cast (by omega : 0 < N-1)) hg
    (by exact_mod_cast (Nat.sub_le_sub_right hcap 1)) hy hyN
  have hpoolg := mul_le_mul_of_nonneg_left hpool hg.le
  have hAPcount := UnitCount218.actual_AP_count (by omega : 1 ≤ N) hF
  nlinarith only [hAPcount, hu, hpoolg, hresponse, hncast]

#print axioms cubic_max
#print axioms cap_response
#print axioms actual_joint
end
end JSP233.ShadowResponse291012
