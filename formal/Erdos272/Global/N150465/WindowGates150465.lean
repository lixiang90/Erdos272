module

public import Erdos272.Resources.N150465.WindowData150465

@[expose] public section

namespace JSP233.WindowGates150465
open WindowData150465
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Loss (w : ℕ) : ℝ := 554+1/2+HCommon+CoeffB w

def PayMargin (w : ℕ) (n : ℝ) : ℝ :=
  ExactResponse200000.Margin (271/800-CoeffA w) (G w) (Loss w)
    (CoeffC w+1/(432*(G w)^2)-154290) n

structure Gates (w : ℕ) : Prop where
  low_bound : 150465 ≤ (info w).low
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

theorem gates {w : ℕ} (hw : w < 1) : Gates w := by
  have he : w=0 := by omega
  subst w
  exact gate0

#print axioms gate0
#print axioms gates
end
end JSP233.WindowGates150465
