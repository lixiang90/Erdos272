module

public import Erdos272.Counting.N67702.EXOneHole67702
public import Erdos272.Arithmetic.LogThree126

@[expose] public section

namespace JSP233.EXLog67702
open EXOneHole67702
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Beta (k : Fin 2) : ℝ := if k=0 then 15811/5000 else 4009/1250

theorem log_three_lower : (5493/5000 : ℝ)≤Real.log 3 := by
  have hh := LogThree126.log_three_window.1
  norm_num [LogThree126.ThreeLo] at hh ⊢
  linarith only [hh]

theorem width_log_lower (k : Fin 2) : Beta k≤1+Real.log (1/WidthCap k) := by
  have hlo := LogThree126.log_three_window.1
  by_cases hk : k=0
  · subst k
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<207/200)
    have he : Real.log (1/WidthCap 0)=2*Real.log 3-Real.log (207/200) := by
      norm_num [WidthCap,Numerator,Denominator]
      have hx : (200/23 : ℝ)=3^2/(207/200) := by norm_num
      rw [hx,Real.log_div (by positivity) (by norm_num),Real.log_pow]
      norm_num
    rw [he]
    norm_num [Beta,LogThree126.ThreeLo] at hlo ht ⊢
    linarith only [hlo,ht]
  · have hk1 : k=1 := by
      apply Fin.ext
      have hh := k.isLt
      have hn : k.val≠0 := by
        intro he
        apply hk
        exact Fin.ext he
      change k.val=1
      omega
    subst k
    have ht := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ)<99/100)
    have he : Real.log (1/WidthCap 1)=2*Real.log 3-Real.log (99/100) := by
      norm_num [WidthCap,Numerator,Denominator]
      have hx : (100/11 : ℝ)=3^2/(99/100) := by norm_num
      rw [hx,Real.log_div (by positivity) (by norm_num),Real.log_pow]
      norm_num
    rw [he]
    norm_num [Beta,LogThree126.ThreeLo] at hlo ht ⊢
    linarith only [hlo,ht]

#print axioms log_three_lower
#print axioms width_log_lower
end
end JSP233.EXLog67702
