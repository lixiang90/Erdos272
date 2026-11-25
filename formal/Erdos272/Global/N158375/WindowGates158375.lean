module

public import Erdos272.Resources.N158375.WindowData158375

@[expose] public section

namespace JSP233.WindowGates158375
open WindowData158375
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Loss (w : ℕ) : ℝ := 554+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w) (G w) (Loss w)
    (CoeffC w+1/(432*(G w)^2)-154290) n

structure Gates (w : ℕ) : Prop where
  low_bound : 158375 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 179999
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  dense_payment : 1 ≤ 6*G w*180200
  chord : (271/800-CoeffA w : ℝ) ≤ G w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high
  small_gap : 0 < (71/800 : ℝ)*(info w).low-((SmallCount w : ℝ)+HCommon)

theorem gate0 : Gates 0 := by
  constructor <;> norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, SmallCount,
    Loss, PayMargin, ExactResponse200000.Margin]

theorem gate1 : Gates 1 := by
  constructor <;> norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, SmallCount,
    Loss, PayMargin, ExactResponse200000.Margin]

theorem gate2 : Gates 2 := by
  constructor <;> norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, SmallCount,
    Loss, PayMargin, ExactResponse200000.Margin]

theorem gates {w : ℕ} (hw : w < 3) : Gates w := by
  interval_cases w
  · exact gate0
  · exact gate1
  · exact gate2

#print axioms gate0
#print axioms gate1
#print axioms gate2
#print axioms gates
end
end JSP233.WindowGates158375
