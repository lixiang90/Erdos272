module

public import Erdos272.Foundation.ProofTactics
public import Mathlib.Data.Real.Basic

@[expose] public section

/-! Kernel checked affine ellipsoid recovery.  The variables in the profile
are the same endpoint `L` and total fringe width `w = L + N - R` throughout.
No bound on a family is assumed or encoded as a proposition in the data. -/
namespace JSP233.Recovery208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def WidthProfile (L w : ℝ) : ℝ :=
  (114959 / 80000 : ℝ) * L^2 - (329 / 200 : ℝ) * L * w + w^2 / 2

def LeftCentre (tL tw : ℝ) : ℝ := (40000 * tL + 65800 * tw) / (2 * 3359)

def WidthCentre (tL tw : ℝ) : ℝ := (65800 * tL + 114959 * tw) / (2 * 3359)

def ShiftEnergy (tL tw C : ℝ) : ℝ :=
  C + (tL * LeftCentre tL tw + tw * WidthCentre tL tw) / 2

theorem left_square_identity (L w : ℝ) :
    WidthProfile L w = (3359 / 40000 : ℝ) * L^2 +
      (w - (329 / 200 : ℝ) * L)^2 / 2 := by
  dsimp only [WidthProfile]
  ring

theorem width_square_identity (L w : ℝ) :
    WidthProfile L w = (3359 / 114959 : ℝ) * w^2 +
      (114959 / 80000 : ℝ) * (L - (65800 / 114959 : ℝ) * w)^2 := by
  dsimp only [WidthProfile]
  ring

theorem centre_identity (L w tL tw : ℝ) :
    WidthProfile (L - LeftCentre tL tw) (w - WidthCentre tL tw) =
      WidthProfile L w - tL * L - tw * w +
        (tL * LeftCentre tL tw + tw * WidthCentre tL tw) / 2 := by
  dsimp only [WidthProfile, LeftCentre, WidthCentre]
  ring

theorem actual_profile_shift {n L w A tL tw C : ℝ}
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C) :
    WidthProfile (L - LeftCentre tL tw) (w - WidthCentre tL tw) ≤
      A * n + ShiftEnergy tL tw C := by
  rw [centre_identity]
  dsimp only [ShiftEnergy]
  linarith only [hprofile]

theorem actual_left_square {n L w A tL tw C : ℝ}
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C) :
    (L - LeftCentre tL tw)^2 ≤ (40000 / 3359 : ℝ) *
      (A * n + ShiftEnergy tL tw C) := by
  have hs := actual_profile_shift hprofile
  rw [left_square_identity] at hs
  have hnon := sq_nonneg (w - WidthCentre tL tw - (329 / 200 : ℝ) *
    (L - LeftCentre tL tw))
  nlinarith only [hs, hnon]

theorem actual_width_square {n L w A tL tw C : ℝ}
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C) :
    (w - WidthCentre tL tw)^2 ≤ (114959 / 3359 : ℝ) *
      (A * n + ShiftEnergy tL tw C) := by
  have hs := actual_profile_shift hprofile
  rw [width_square_identity] at hs
  have hnon := sq_nonneg (L - LeftCentre tL tw - (65800 / 114959 : ℝ) *
    (w - WidthCentre tL tw))
  nlinarith only [hs, hnon]

theorem actual_left_bound {n L w A tL tw C target : ℝ}
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C)
    (htarget : 0 < target - LeftCentre tL tw)
    (hgap : (40000 / 3359 : ℝ) * (A * n + ShiftEnergy tL tw C) <
      (target - LeftCentre tL tw)^2) : L < target := by
  have hs := actual_left_square hprofile
  by_contra hh
  have hge : target ≤ L := le_of_not_gt hh
  have hprod := mul_nonneg (sub_nonneg.mpr hge)
    (show 0 ≤ L + target - 2 * LeftCentre tL tw by linarith only [htarget, hge])
  nlinarith only [hs, hgap, hprod]

theorem actual_width_bound {n L w A tL tw C target : ℝ}
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C)
    (htarget : 0 < target - WidthCentre tL tw)
    (hgap : (114959 / 3359 : ℝ) * (A * n + ShiftEnergy tL tw C) <
      (target - WidthCentre tL tw)^2) : w < target := by
  have hs := actual_width_square hprofile
  by_contra hh
  have hge : target ≤ w := le_of_not_gt hh
  have hprod := mul_nonneg (sub_nonneg.mpr hge)
    (show 0 ≤ w + target - 2 * WidthCentre tL tw by linarith only [htarget, hge])
  nlinarith only [hs, hgap, hprod]

/- The continuous window argument is algebraic: the difference between
the quadratic gate at `n` and its value at `lo` has a nonnegative factor. -/
theorem continuous_square_gate {lo n slope centre norm A energy : ℝ}
    (hn : lo ≤ n) (hslope : 0 ≤ slope)
    (htarget : 0 < slope * lo - centre)
    (hgap : norm * (A * lo + energy) < (slope * lo - centre)^2)
    (hderivative : 0 ≤ 2 * slope * (slope * lo - centre) - norm * A) :
    0 < slope * n - centre ∧
      norm * (A * n + energy) < (slope * n - centre)^2 := by
  have hdelta : 0 ≤ n - lo := sub_nonneg.mpr hn
  have hinc := mul_nonneg hslope hdelta
  have hquad := mul_nonneg (sq_nonneg slope) (sq_nonneg (n - lo))
  have hlinear := mul_nonneg hderivative hdelta
  constructor
  · nlinarith only [htarget, hinc]
  · nlinarith only [hgap, hquad, hlinear]

def StageCertificate (lo A tL tw C sL sw : ℝ) : Prop :=
  0 ≤ sL ∧ 0 ≤ sw ∧
  0 < sL * lo - LeftCentre tL tw ∧
  (40000 / 3359 : ℝ) * (A * lo + ShiftEnergy tL tw C) <
    (sL * lo - LeftCentre tL tw)^2 ∧
  0 ≤ 2 * sL * (sL * lo - LeftCentre tL tw) - (40000 / 3359 : ℝ) * A ∧
  0 < sw * lo - WidthCentre tL tw ∧
  (114959 / 3359 : ℝ) * (A * lo + ShiftEnergy tL tw C) <
    (sw * lo - WidthCentre tL tw)^2 ∧
  0 ≤ 2 * sw * (sw * lo - WidthCentre tL tw) - (114959 / 3359 : ℝ) * A

theorem actual_stage_bounds {lo n L w A tL tw C sL sw : ℝ}
    (hn : lo ≤ n) (hcert : StageCertificate lo A tL tw C sL sw)
    (hprofile : WidthProfile L w ≤ A * n + tL * L + tw * w + C) :
    L < sL * n ∧ w < sw * n := by
  obtain ⟨hsL, hsw, hLt, hLg, hLd, hwt, hwg, hwd⟩ := hcert
  obtain ⟨hLt', hLg'⟩ := continuous_square_gate hn hsL hLt hLg hLd
  obtain ⟨hwt', hwg'⟩ := continuous_square_gate hn hsw hwt hwg hwd
  exact ⟨actual_left_bound hprofile hLt' hLg', actual_width_bound hprofile hwt' hwg'⟩

#print axioms actual_left_bound
#print axioms actual_width_bound
#print axioms continuous_square_gate
end
end JSP233.Recovery208
