import Erdos272.Arithmetic.SevenPrices208

/-! Exhaust the dyadic indices justified by the actual omitter size.  The
continuous N intervals are covered by proved endpoint inequalities, rather
than by sampling N or the real scale variable. -/
namespace JSP233.DyadicPrice208
open SevenPrices208 ReciprocalPrice208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Q (y : ℝ) : ℝ := y - y^2 / 2
def Actual (n v : ℝ) : ℝ :=
  Q (min (484*v/n) (1/11)) + UniformG*n/v^3 + UniformU/v +
    UniformEta/n + Loss/n

theorem low_identity {n v : ℝ} (hn : 0 < n) (hv : 0 < v)
    (hscale : 484*v/n ≤ 1/11) :
    Actual n v = Price (UniformG/v^3) (UniformU/v)
      (484*v+UniformEta+Loss) ((484*v)^2/2) n := by
  unfold Actual Q Price
  rw [min_eq_left hscale]
  field_simp [hn.ne', hv.ne']
  ring

theorem cap_identity {n v : ℝ} (hn : 0 < n) (hv : 0 < v)
    (hscale : 1/11 ≤ 484*v/n) :
    Actual n v = Price (UniformG/v^3) (Beta+UniformU/v)
      (UniformEta+Loss) 0 n := by
  unfold Actual Q Price Beta
  rw [min_eq_right hscale]
  field_simp [hn.ne', hv.ne']
  ring

theorem actual_dyadic_window {n : ℝ} {j : ℕ}
    (hl : 659912 ≤ n) (hu : n ≤ 705097) (hj : 1 ≤ j) (hmax : j ≤ 8) :
    Actual n ((2 : ℝ)^j) ≤ Budget := by
  have hn : 0 < n := by linarith only [hl]
  interval_cases j
  · have hs : 484*(2:ℝ)^1/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow2] using rootlow2_window hl hu
  · have hs : 484*(2:ℝ)^2/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow4] using rootlow4_window hl hu
  · have hs : 484*(2:ℝ)^3/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow8] using rootlow8_window hl hu
  · have hs : 484*(2:ℝ)^4/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow16] using rootlow16_window hl hu
  · have hs : 484*(2:ℝ)^5/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow32] using rootlow32_window hl hu
  · have hs : 484*(2:ℝ)^6/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hl])
    rw [low_identity hn (by positivity) hs]
    norm_num at *
    simpa [RootLow64] using rootlow64_window hl hu
  · by_cases hcut : n ≤ 681472
    · have hs : 1/11 ≤ 484*(2:ℝ)^7/n := (le_div_iff₀ hn).mpr (by norm_num; linarith only [hcut])
      rw [cap_identity hn (by positivity) hs]
      norm_num at *
      exact rootcap128_window hl hcut
    · have hcut' : 681472 ≤ n := (lt_of_not_ge hcut).le
      have hs : 484*(2:ℝ)^7/n ≤ 1/11 := (div_le_iff₀ hn).mpr (by norm_num; linarith only [hcut'])
      rw [low_identity hn (by positivity) hs]
      norm_num at *
      simpa [RootLow128] using rootlow128_window hcut' hu
  · have hs : 1/11 ≤ 484*(2:ℝ)^8/n := (le_div_iff₀ hn).mpr (by norm_num; linarith only [hu])
    rw [cap_identity hn (by positivity) hs]
    norm_num at *
    exact rootcap256_window hl hu

#print axioms actual_dyadic_window
end
end JSP233.DyadicPrice208
