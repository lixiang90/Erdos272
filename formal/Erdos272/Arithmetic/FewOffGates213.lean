import Erdos272.Arithmetic.FewOffGates212
import Erdos272.Resources.AlignedPlans213
namespace JSP233.FewOffGates213
open AlignedPlans212 FewOffGates212
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem endpoint_gate {k : ℕ} (hk2 : 2≤k) (hk11 : k≤11) :
    0<Coefficient k ∧ FewOffGates212.Constant k < 646000*Coefficient k ∧
    (0 : ℝ)<(SourceCount k : ℝ)/2-10/11 := by
  interval_cases k <;> norm_num [Coefficient,FewOffGates212.Constant,SourceCount]

theorem full_phase_gate {N k : ℕ} {w : ℝ}
    (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11) (hw : w<(N : ℝ)/(2951/100)) :
    (10/11 : ℝ)*((N : ℝ)+1-w)+10*(SourceCount k : ℝ)*(SourceCount k-1) <
      (SourceCount k : ℝ)*((N : ℝ)/k-(3/5000 : ℝ)*N-w/2-3) := by
  have he := endpoint_gate hk2 hk11
  have hnR : (646000 : ℝ)≤N := by exact_mod_cast hN
  have hmain := he.2.1.trans_le (mul_le_mul_of_nonneg_right hnR he.1.le)
  have hwidth := mul_pos he.2.2 (sub_pos.mpr hw)
  have hid : (SourceCount k : ℝ)*((N : ℝ)/k-(3/5000 : ℝ)*N-w/2-3)-
      ((10/11 : ℝ)*((N : ℝ)+1-w)+10*(SourceCount k : ℝ)*(SourceCount k-1)) =
      (N : ℝ)*Coefficient k-FewOffGates212.Constant k+
        ((SourceCount k : ℝ)/2-10/11)*((N : ℝ)/(2951/100)-w) := by
    dsimp only [Coefficient,FewOffGates212.Constant]
    ring
  linarith only [hid,hmain,hwidth]

theorem all_off_gate {N k : ℕ} (hN : 646000≤N) (hk2 : 2≤k) (hk11 : k≤11) :
    (120 : ℝ)<(N : ℝ)*(17/(k : ℝ)-1-16/(2951/100)) := by
  have hnR : (646000 : ℝ)≤N := by exact_mod_cast hN
  interval_cases k <;> norm_num <;> nlinarith only [hnR]

theorem combine_k11 {E A O w : ℝ} (hpart : E=A+O)
    (ha : A≤TerminalA 11*w+TerminalB 11)
    (ho : O≤(SourceCount 11-1 : ℝ)*(w-1)+904) :
    E≤(16571/504 : ℝ)*w+150757/168 := by
  norm_num [SourceCount,TerminalA,TerminalB] at ha ho
  linarith only [hpart,ha,ho]


#print axioms endpoint_gate
#print axioms full_phase_gate
#print axioms all_off_gate
#print axioms combine_k11
end
end JSP233.FewOffGates213
