module

public import Erdos272.Arithmetic.N65968.SmallData65968
public import Erdos272.Counting.N82427.FixedSmallScalars82427

@[expose] public section

namespace JSP233.SmallGates65968
open SmallData65968 WindowData65968
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option Elab.async false

structure Gates (p : ℕ) : Prop where
  low_bound : 65968≤(policy p).low
  high_bound : (policy p).high≤67701
  low_le_high : (policy p).low≤(policy p).high
  length_lower : 2≤(policy p).L
  length_upper : (policy p).L≤78
  T_lower : 77≤(policy p).T
  T_le_L : (policy p).T≤(policy p).L
  coefficient_eq : (policy p).coefficient=
    FixedSmallScalars82427.Coefficient ((policy p).T-1) ((policy p).L-1)
  credit_eq : (policy p).credit=
    FixedSmallScalars82427.Credit ((policy p).T-1) ((policy p).L-1)
  margin_low : 0<SmallMargin (policy p).coefficient (policy p).credit (policy p).low
  derivative_low : 0<2*Leading*(policy p).low-SmallLoss (policy p).coefficient
  base_lt : (policy p).base<7
  base_low : (info (policy p).base).low≤(policy p).low
  base_high : (policy p).high≤(info (policy p).base).high
  base_minimum : (info (policy p).base).memberFloor=max 80 ((policy p).L+1)
  base_root_cap : RootK (policy p).base=100
  base_root_witness : (policy p).T≤Witness (policy p).base
  base_whole_minimum : (policy p).T≤81 →
    (info (policy p).base).memberFloor≤max 80 ((policy p).T+1)
  base_whole_witness : 82≤Witness (policy p).base
  mid_lt : (policy p).mid<7
  mid_low : (info (policy p).mid).low≤(policy p).low
  mid_high : (policy p).high≤(info (policy p).mid).high
  mid_minimum : (info (policy p).mid).memberFloor=max 83 ((policy p).T+1)
  mid_witness : 86≤Witness (policy p).mid
  root79_low : (policy p).L≤78 → (info 2).low≤(policy p).low
  root79_high : (policy p).L≤78 → (policy p).high≤(info 2).high
  whole79_low : (policy p).T≤78 → (info 3).low≤(policy p).low
  whole79_high : (policy p).T≤78 → (policy p).high≤(info 3).high

  root78_low : (policy p).L≤77 → (info 0).low≤(policy p).low
  root78_high : (policy p).L≤77 → (policy p).high≤(info 0).high
  whole78_low : (info 1).low≤(policy p).low
  whole78_high : (policy p).high≤(info 1).high

theorem gates {p : ℕ} (hp : p<2) : Gates p := by
  interval_cases p <;> constructor <;>
    norm_num [policy, HSmall, Leading, SmallLoss, SmallConstant, SmallMargin,
      FixedSmallScalars82427.Coefficient, FixedSmallScalars82427.Credit,
      Nat.choose_two_right, info, RootK, Witness]

theorem small_margin_positive {p : ℕ} (hp : p<2) {n : ℝ}
    (hn : ((policy p).low : ℝ)≤n) :
    0<SmallMargin (policy p).coefficient (policy p).credit n := by
  have hg := gates hp
  have ha : 0≤Leading := by norm_num [Leading]
  have hshift := mul_nonneg ha (sub_nonneg.mpr hn)
  have hderivative := hg.derivative_low
  have hlinear : 0≤Leading*(n+(policy p).low)-SmallLoss (policy p).coefficient := by
    nlinarith only [hshift,hderivative]
  have hproduct := mul_nonneg (sub_nonneg.mpr hn) hlinear
  have hlow := hg.margin_low
  dsimp only [SmallMargin] at hlow ⊢
  nlinarith only [hproduct,hlow]

#print axioms gates
#print axioms small_margin_positive
end
end JSP233.SmallGates65968
