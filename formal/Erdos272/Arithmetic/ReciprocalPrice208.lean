module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic

@[expose] public section

/-! A continuous endpoint certificate for all prices used in round207,
including the quadratic saving in the actual root degree.  The proof is
algebraic, so its hypotheses can be discharged by exact rational arithmetic.
-/
namespace JSP233.ReciprocalPrice208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Price (a b c s x : ℝ) : ℝ := a*x + b + c/x - s/x^2

theorem window {a b c s lo hi x budget : ℝ}
    (hp : 0 < lo) (hl : lo ≤ x) (hu : x ≤ hi)
    (hc : 0 ≤ c) (hcurvature : 3*s ≤ c*lo)
    (hlo : Price a b c s lo ≤ budget) (hhi : Price a b c s hi ≤ budget) :
    Price a b c s x ≤ budget := by
  have hx : 0 < x := hp.trans_le hl
  have hh : 0 < hi := hx.trans_le hu
  by_cases he : lo = hi
  · have he' : x = lo := by linarith only [hl, hu, he]
    simpa only [he'] using hlo
  have hspan : 0 < hi - lo := by
    have hle : lo ≤ hi := hl.trans hu
    exact sub_pos.mpr (lt_of_le_of_ne hle he)
  have hbracket : 0 ≤ c*lo*hi*x - s*((hi+lo)*x+lo*hi) := by
    by_cases hs : 0 ≤ s
    · have h1 := mul_nonneg (show 0 ≤ hi - lo by linarith only [hl, hu]) hx.le
      have h2 := mul_nonneg (sub_nonneg.mpr hl) hh.le
      have h3 := mul_nonneg hs (add_nonneg h1 h2)
      have h4 := mul_nonneg (sub_nonneg.mpr hcurvature) (mul_nonneg hh.le hx.le)
      nlinarith only [h3, h4]
    · have hs' : 0 ≤ -s := by linarith only [hs]
      have h1 : 0 ≤ c*lo*hi*x := by positivity
      have h2 : 0 ≤ -s*((hi+lo)*x+lo*hi) := by positivity
      linarith only [h1, h2]
  let D : ℝ := lo^2*hi^2*x^2
  let L : ℝ := (hi-x)*Price a b c s lo + (x-lo)*Price a b c s hi -
    (hi-lo)*Price a b c s x
  have hD : 0 < D := by dsimp only [D]; positivity
  have hidentity : L*D = (hi-lo)*(x-lo)*(hi-x)*
      (c*lo*hi*x - s*((hi+lo)*x+lo*hi)) := by
    dsimp only [L, D, Price]
    field_simp [hp.ne', hh.ne', hx.ne']
    ring
  have hproduct : 0 ≤ L*D := by
    rw [hidentity]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hspan.le (sub_nonneg.mpr hl)) (sub_nonneg.mpr hu))
      hbracket
  have hL : 0 ≤ L := nonneg_of_mul_nonneg_left hproduct hD
  have hleft := mul_le_mul_of_nonneg_left hlo (sub_nonneg.mpr hu)
  have hright := mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr hl)
  have hsum : (hi-lo)*Price a b c s x ≤ (hi-lo)*budget := by
    dsimp only [L] at hL
    nlinarith only [hL, hleft, hright]
  exact (mul_le_mul_iff_right₀ hspan).mp hsum

#print axioms window
end
end JSP233.ReciprocalPrice208
