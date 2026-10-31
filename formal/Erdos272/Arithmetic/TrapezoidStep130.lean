import Erdos272.Arithmetic.FloorTrapezoid130
import Erdos272.Arithmetic.ConvexQuotient130
namespace JSP233.TrapezoidStep130
open Set MeasureTheory intervalIntegral
open VolumeLower125 VolumeStep125 SimplexMoment57 FloorTrapezoid130 ConvexQuotient130
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def W2 (x:ℝ):ℝ := V2 x+V1 x/2
def W3 (x:ℝ):ℝ := V3 x+V2 x+V1 x/4
def W4 (x:ℝ):ℝ := V4 x+3*V3 x/2+3*V2 x/4+V1 x/8

theorem w2_formula (x:ℝ) : W2 x=x*(Real.log x-1/2)+1/2 := by
  dsimp only [W2,V1,V2]
  ring

theorem w3_formula (x:ℝ) : W3 x=x*((Real.log x)^2/2+1/4)-1/4 := by
  dsimp only [W3,V1,V2,V3]
  ring

theorem w4_formula (x:ℝ) :
    W4 x=x*((Real.log x)^3/6+(Real.log x)^2/4+Real.log x/4-1/8)+1/8 := by
  dsimp only [W4,V1,V2,V3,V4]
  ring

theorem w2_derivative {x:ℝ} (hx:0<x) : HasDerivAt W2 (Real.log x+1/2) x := by
  exact (v2_derivative hx).add ((v1_derivative x).div_const 2)

theorem w3_derivative {x:ℝ} (hx:0<x) :
    HasDerivAt W3 ((Real.log x)^2/2+Real.log x+1/4) x := by
  exact ((v3_derivative hx).add (v2_derivative hx)).add ((v1_derivative x).div_const 4)

theorem w2_monotone : MonotoneOn W2 (Ici (1:ℝ)) := by
  apply monotone_from_derivative (fun x hx=>w2_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro x hx
  have hl := Real.log_nonneg hx
  linarith only [hl]

theorem w3_monotone : MonotoneOn W3 (Ici (1:ℝ)) := by
  apply monotone_from_derivative (fun x hx=>w3_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro x hx
  have hl := Real.log_nonneg hx
  positivity

theorem v1_convex : ConvexOn ℝ (Ici (1:ℝ)) V1 := by
  exact convex_from_derivative (convex_Ici _) (fun x _=>v1_derivative x)
    (by intro u hu v hv huv;exact le_rfl)

theorem w2_convex : ConvexOn ℝ (Ici (1:ℝ)) W2 := by
  apply convex_from_derivative (convex_Ici _)
    (fun x hx=>w2_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro u hu v hv huv
  have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one hu) huv
  linarith only [hl]

theorem w3_convex : ConvexOn ℝ (Ici (1:ℝ)) W3 := by
  apply convex_from_derivative (convex_Ici _)
    (fun x hx=>w3_derivative (lt_of_lt_of_le zero_lt_one hx))
  intro u hu v hv huv
  have hlu := Real.log_nonneg hu
  have hlv := Real.log_nonneg hv
  have hl := Real.log_le_log (lt_of_lt_of_le zero_lt_one hu) huv
  have hs : (Real.log u)^2≤(Real.log v)^2 := (sq_le_sq₀ hlu hlv).mpr hl
  linarith only [hl,hs]

theorem step_w1 {x:ℝ} (hx:1≤x) :
    (∫t in (1:ℝ)..x,V1 (x/t))+V1 x/2=W2 x := by
  rw [integral_v1 hx]
  rfl

theorem step_w2 {x:ℝ} (hx:1≤x) :
    (∫t in (1:ℝ)..x,W2 (x/t))+W2 x/2=W3 x := by
  have hi1 : IntervalIntegrable (fun t:ℝ=>V1 (x/t)) volume 1 x :=
    (continuous_comp_quotient (fun t _=>v1_derivative t) hx).intervalIntegrable_of_Icc hx
  have hi2 : IntervalIntegrable (fun t:ℝ=>V2 (x/t)) volume 1 x :=
    (continuous_comp_quotient (fun t ht=>v2_derivative (lt_of_lt_of_le zero_lt_one ht)) hx).intervalIntegrable_of_Icc hx
  change (∫t in (1:ℝ)..x,V2 (x/t)+V1 (x/t)/2)+W2 x/2=W3 x
  rw [intervalIntegral.integral_add hi2 (hi1.div_const 2),intervalIntegral.integral_div,
    integral_v1 hx,integral_v2 hx]
  dsimp only [W2,W3]
  ring

theorem step_w3 {x:ℝ} (hx:1≤x) :
    (∫t in (1:ℝ)..x,W3 (x/t))+W3 x/2=W4 x := by
  have hi1 : IntervalIntegrable (fun t:ℝ=>V1 (x/t)) volume 1 x :=
    (continuous_comp_quotient (fun t _=>v1_derivative t) hx).intervalIntegrable_of_Icc hx
  have hi2 : IntervalIntegrable (fun t:ℝ=>V2 (x/t)) volume 1 x :=
    (continuous_comp_quotient (fun t ht=>v2_derivative (lt_of_lt_of_le zero_lt_one ht)) hx).intervalIntegrable_of_Icc hx
  have hi3 : IntervalIntegrable (fun t:ℝ=>V3 (x/t)) volume 1 x :=
    (continuous_comp_quotient (fun t ht=>v3_derivative (lt_of_lt_of_le zero_lt_one ht)) hx).intervalIntegrable_of_Icc hx
  change (∫t in (1:ℝ)..x,V3 (x/t)+V2 (x/t)+V1 (x/t)/4)+W3 x/2=W4 x
  rw [intervalIntegral.integral_add (hi3.add hi2) (hi1.div_const 4),
    intervalIntegral.integral_add hi3 hi2,intervalIntegral.integral_div,
    integral_v1 hx,integral_v2 hx,integral_v3 hx]
  dsimp only [W3,W4]
  ring

theorem actual_w2_lower {x:ℝ} (hx:1≤x) : W2 x≤(DivCount 1 (Nat.floor x):ℝ) := by
  exact count_step_half 0 V1 W2 v1_monotone (by norm_num [V1])
    (fun _ hz=>continuous_comp_quotient (fun t _=>v1_derivative t) hz)
    (fun _ hz=>convex_comp_quotient v1_convex v1_monotone hz)
    (fun _ hz=>actual_v1_lower hz) (fun _ hz=>step_w1 hz) hx

theorem actual_w3_lower {x:ℝ} (hx:1≤x) : W3 x≤(DivCount 2 (Nat.floor x):ℝ) := by
  exact count_step_half 1 W2 W3 w2_monotone (by norm_num [W2,V1,V2])
    (fun _ hz=>continuous_comp_quotient (fun t ht=>w2_derivative (lt_of_lt_of_le zero_lt_one ht)) hz)
    (fun _ hz=>convex_comp_quotient w2_convex w2_monotone hz)
    (fun _ hz=>actual_w2_lower hz) (fun _ hz=>step_w2 hz) hx

theorem actual_w4_lower {x:ℝ} (hx:1≤x) : W4 x≤(DivCount 3 (Nat.floor x):ℝ) := by
  exact count_step_half 2 W3 W4 w3_monotone (by norm_num [W3,V1,V2,V3])
    (fun _ hz=>continuous_comp_quotient (fun t ht=>w3_derivative (lt_of_lt_of_le zero_lt_one ht)) hz)
    (fun _ hz=>convex_comp_quotient w3_convex w3_monotone hz)
    (fun _ hz=>actual_w3_lower hz) (fun _ hz=>step_w3 hz) hx

#print axioms w2_formula
#print axioms w3_formula
#print axioms w4_formula
#print axioms w2_derivative
#print axioms w3_derivative
#print axioms w2_monotone
#print axioms w3_monotone
#print axioms v1_convex
#print axioms w2_convex
#print axioms w3_convex
#print axioms step_w1
#print axioms step_w2
#print axioms step_w3
#print axioms actual_w2_lower
#print axioms actual_w3_lower
#print axioms actual_w4_lower
end
end JSP233.TrapezoidStep130
