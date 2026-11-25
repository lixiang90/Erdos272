module

public import Erdos272.Resources.N80470.WindowData80470

@[expose] public section

namespace JSP233.WindowGates80470
open WindowData80470
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def EffectiveG (w : ℕ) : ℝ := if w < 3 then (32767248/39364325)*G w else G w

def Penalty (w : ℕ) : ℝ :=
  if w < 3 then 1/(432*((32767248/39364325)*G w)^2) else 1/(432*(G w)^2)

def QuadraticExtra (w : ℕ) : ℝ := if w < 3 then 3*G w else 0

def Loss (w : ℕ) : ℝ := (RootK w : ℝ)+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w-QuadraticExtra w) (EffectiveG w) (Loss w)
    (CoeffC w+Penalty w-((RootCredit w : ℝ)+1)) n

structure Gates (w : ℕ) : Prop where
  low_bound : 80470 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 82425
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  effective_positive : 0 < EffectiveG w
  dense_payment : 1 ≤ 6*G w*180200
  shadow_cap : w < 3 → 3*G w*((info w).high-1 : ℝ) ≤ 1
  chord : (271/800-CoeffA w-QuadraticExtra w : ℝ) ≤
    EffectiveG w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high

theorem gates {w : ℕ} (hw : w < 4) : Gates w := by
  interval_cases w <;> constructor <;>
    norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, RootK, RootCredit,
      EffectiveG, Penalty, QuadraticExtra, Loss, PayMargin, ExactResponse200000.Margin]

def SmallMargin (count credit n : ℝ) : ℝ :=
  (1/2-257021/625000)*n^2-
    (count+HCommon+1/4-2*(257021/625000)-1851/1000)*n+
    credit+HCommon-257021/625000-1851/1000-50945/8-1

def SmallLowMargin (n : ℝ) : ℝ := SmallMargin SmallLowCount SmallLowCredit n

def SmallUpperMargin (n : ℝ) : ℝ := SmallMargin SmallUpperCount SmallUpperCredit n

theorem small_low_gate {n : ℝ} (hn : 80470≤n) : 0<SmallLowMargin n := by
  have hq : 0≤(n-80470)*((1/2-257021/625000 : ℝ)*(n+80470)-
      (7141+11921/1000+1/4-2*(257021/625000)-1851/1000)) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hn])
  norm_num [SmallLowMargin, SmallMargin, SmallLowCount, HCommon, SmallLowCredit]
  nlinarith only [hq]

theorem small_upper_gate {n : ℝ} (hn : 81427≤n) : 0<SmallUpperMargin n := by
  have hq : 0≤(n-81427)*((1/2-257021/625000 : ℝ)*(n+81427)-
      (7226+11921/1000+1/4-2*(257021/625000)-1851/1000)) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hn])
  norm_num [SmallUpperMargin, SmallMargin, SmallUpperCount, HCommon, SmallUpperCredit]
  nlinarith only [hq]

#print axioms gates
#print axioms small_low_gate
#print axioms small_upper_gate
end
end JSP233.WindowGates80470
