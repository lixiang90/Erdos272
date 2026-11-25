module

public import Erdos272.Resources.N94488.WindowData94488

@[expose] public section

namespace JSP233.WindowGates94488
open WindowData94488
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def EffectiveG (w : ℕ) : ℝ := if w < 5 then 7*G w/8 else G w

def Penalty (w : ℕ) : ℝ := if w < 5 then 73/(24000*(G w)^2) else 1/(432*(G w)^2)

def Loss (w : ℕ) : ℝ := (RootK w : ℝ)+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w) (EffectiveG w) (Loss w)
    (CoeffC w+Penalty w-((RootCredit w : ℝ)+1)) n

structure Gates (w : ℕ) : Prop where
  low_bound : 94488 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 109473
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  effective_positive : 0 < EffectiveG w
  dense_payment : 1 ≤ 6*G w*180200
  shadow_cap : w < 5 → 4*G w*((info w).high-1 : ℝ) ≤ 1
  chord : (271/800-CoeffA w : ℝ) ≤ EffectiveG w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high

theorem gates {w : ℕ} (hw : w < 6) : Gates w := by
  interval_cases w <;> constructor <;>
    norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, RootK, RootCredit,
      EffectiveG, Penalty, Loss, PayMargin, ExactResponse200000.Margin]

theorem small_gate {w : ℕ} (hw : w < 5) :
    0 < (71/800 : ℝ)*(info w).low-((SmallCount w : ℝ)+HCommon) := by
  interval_cases w <;> norm_num [info, SmallCount, HCommon]

theorem low_root_k {w : ℕ} (hw : w < 5) : RootK w = 129 ∧ RootCredit w = 8514 := by
  interval_cases w <;> norm_num [RootK, RootCredit]

#print axioms gates
#print axioms small_gate
#print axioms low_root_k
end
end JSP233.WindowGates94488
