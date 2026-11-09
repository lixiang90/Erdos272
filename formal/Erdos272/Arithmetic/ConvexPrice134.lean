module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic

@[expose] public section
namespace JSP233.ConvexPrice134
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000
def Price (a b c x : ℝ) : ℝ := a*x+b+c/x

theorem quadratic_window {a b c lo hi x : ℝ} (ha : 0≤a)
    (hl : lo≤x) (hu : x≤hi)
    (hlo : a*lo^2+b*lo+c≤0) (hhi : a*hi^2+b*hi+c≤0) :
    a*x^2+b*x+c≤0 := by
  by_cases heq : lo=hi
  · have hx : x=lo := by linarith only [hl,hu,heq]
    simpa only [hx] using hlo
  · have hp : 0<hi-lo := by
      by_contra hh
      have hrev : hi≤lo := by linarith only [hh]
      exact heq (le_antisymm (hl.trans hu) hrev)
    have hleft := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hu) hlo
    have hright := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hl) hhi
    have hcross : 0≤a*(hi-lo)*(x-lo)*(hi-x) :=
      mul_nonneg (mul_nonneg (mul_nonneg ha hp.le) (sub_nonneg.mpr hl)) (sub_nonneg.mpr hu)
    have hid : (hi-lo)*(a*x^2+b*x+c)=
        (hi-x)*(a*lo^2+b*lo+c)+(x-lo)*(a*hi^2+b*hi+c)-a*(hi-lo)*(x-lo)*(hi-x) := by ring
    have hmul : (hi-lo)*(a*x^2+b*x+c)≤0 := by
      rw [hid]
      linarith only [hleft,hright,hcross]
    by_contra hnot
    have hpos := mul_pos hp (lt_of_not_ge hnot)
    linarith only [hmul,hpos]

theorem price_window {a b c lo hi x budget : ℝ} (ha : 0≤a)
    (hpos : 0<lo) (hl : lo≤x) (hu : x≤hi)
    (hlo : Price a b c lo≤budget) (hhi : Price a b c hi≤budget) :
    Price a b c x≤budget := by
  have hx : 0<x := hpos.trans_le hl
  have hh : 0<hi := hx.trans_le hu
  have hlmul := mul_le_mul_of_nonneg_right hlo hpos.le
  have hhmul := mul_le_mul_of_nonneg_right hhi hh.le
  have hcl : c/lo*lo=c := div_mul_cancel₀ c hpos.ne'
  have hch : c/hi*hi=c := div_mul_cancel₀ c hh.ne'
  dsimp only [Price] at hlmul hhmul ⊢
  have hlow : a*lo^2+(b-budget)*lo+c≤0 := by
    nlinarith only [hlmul,hcl]
  have hhigh : a*hi^2+(b-budget)*hi+c≤0 := by
    nlinarith only [hhmul,hch]
  have hq := quadratic_window ha hl hu hlow hhigh
  have hd : c/x≤budget-a*x-b := (div_le_iff₀ hx).mpr (by nlinarith only [hq])
  linarith only [hd]


#print axioms quadratic_window
#print axioms price_window
end
end JSP233.ConvexPrice134
