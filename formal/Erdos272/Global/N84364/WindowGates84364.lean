module

public import Erdos272.Resources.N84364.WindowData84364

@[expose] public section

namespace JSP233.WindowGates84364
open WindowData84364
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def EffectiveG (w : ℕ) : ℝ := if w < 2 then (32767248/39364325)*G w else G w

def Penalty (w : ℕ) : ℝ :=
  if w < 2 then 1/(432*((32767248/39364325)*G w)^2) else 1/(432*(G w)^2)

def QuadraticExtra (w : ℕ) : ℝ := if w < 2 then 3*G w else 0

def Loss (w : ℕ) : ℝ := (RootK w : ℝ)+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w-QuadraticExtra w) (EffectiveG w) (Loss w)
    (CoeffC w+Penalty w-((RootCredit w : ℝ)+1)) n

structure Gates (w : ℕ) : Prop where
  low_bound : 84364 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 86411
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  effective_positive : 0 < EffectiveG w
  dense_payment : 1 ≤ 6*G w*180200
  shadow_cap : w < 2 → 3*G w*((info w).high-1 : ℝ) ≤ 1
  chord : (271/800-CoeffA w-QuadraticExtra w : ℝ) ≤
    EffectiveG w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high

theorem gates {w : ℕ} (hw : w < 3) : Gates w := by
  interval_cases w <;> constructor <;>
    norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, RootK, RootCredit,
      EffectiveG, Penalty, QuadraticExtra, Loss, PayMargin, ExactResponse200000.Margin]

def SmallMargin (n : ℝ) : ℝ :=
  (71/800 : ℝ)*n^2-((SmallCount : ℝ)+HCommon)*n+SmallCredit

theorem small_gate {n : ℝ} (hn : 84364≤n) : 0<SmallMargin n := by
  have hq : 0≤(n-84364)*((71/800 : ℝ)*(n+84364)-7495) :=
    mul_nonneg (by linarith only [hn]) (by linarith only [hn])
  norm_num [SmallMargin, SmallCount, HCommon, SmallCredit]
  nlinarith only [hq]

#print axioms gates
#print axioms small_gate
end
end JSP233.WindowGates84364
