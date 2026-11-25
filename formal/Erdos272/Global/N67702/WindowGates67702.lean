module

public import Erdos272.Resources.N67702.WindowData67702

@[expose] public section

namespace JSP233.WindowGates67702
open WindowData67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def EffectiveG (w : ℕ) : ℝ := (32767248/39364325)*G w
def Penalty (w : ℕ) : ℝ := 1/(432*(EffectiveG w)^2)
def QuadraticExtra (w : ℕ) : ℝ := 3*G w
def Loss (w : ℕ) : ℝ := (RootK w : ℝ)+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w-QuadraticExtra w) (EffectiveG w) (Loss w)
    (CoeffC w+Penalty w-((RootCredit w : ℝ)+1)) n

structure Gates (w : ℕ) : Prop where
  low_bound : 67702 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 80469
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  effective_positive : 0 < EffectiveG w
  dense_payment : 1 ≤ 6*G w*180200
  shadow_cap : 3*G w*((info w).high-1 : ℝ) ≤ 1
  chord : (271/800-CoeffA w-QuadraticExtra w : ℝ) ≤
    EffectiveG w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high

theorem gates {w : ℕ} (hw : w < 11) : Gates w := by
  interval_cases w <;> constructor <;>
    norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, RootK, RootCredit,
      EffectiveG, Penalty, QuadraticExtra, Loss, PayMargin, ExactResponse200000.Margin]

#print axioms gates
end
end JSP233.WindowGates67702
