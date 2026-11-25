module

public import Erdos272.Resources.N130000.WindowData130000

@[expose] public section

namespace JSP233.WindowGates130000
open WindowData130000
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Loss (w : ℕ) : ℝ := (RootK w : ℝ)+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w) (G w) (Loss w)
    (CoeffC w+1/(432*(G w)^2)-((RootCredit w : ℝ)+1)) n

structure Gates (w : ℕ) : Prop where
  low_bound : 130000 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 179999
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  dense_payment : 1 ≤ 6*G w*180200
  chord : (271/800-CoeffA w : ℝ) ≤ G w*(2*(info w).low+(info w).high-3)
  low_gap : 0 < PayMargin w (info w).low
  high_gap : 0 < PayMargin w (info w).high

theorem gates {w : ℕ} (hw : w < 4) : Gates w := by
  interval_cases w <;> constructor <;>
    norm_num [info, G, CoeffA, CoeffB, CoeffC, HCommon, RootK, RootCredit,
      Loss, PayMargin, ExactResponse200000.Margin]

theorem small_gate {w : ℕ} (hw : w < 3) :
    0 < (71/800 : ℝ)*(info w).low-((SmallCount w : ℝ)+HCommon) := by
  interval_cases w <;> norm_num [info, SmallCount, HCommon]

theorem low_root_k {w : ℕ} (hw : w < 3) : RootK w = 129 ∧ RootCredit w = 8514 := by
  interval_cases w <;> norm_num [RootK, RootCredit]

#print axioms gates
#print axioms small_gate
#print axioms low_root_k
end
end JSP233.WindowGates130000
