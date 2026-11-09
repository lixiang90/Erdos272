module

public import Erdos272.Arithmetic.NativeGates212

@[expose] public section
namespace JSP233.NativeGates213
open AlignedPlans212 FewOffGates212
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem all_rank_native_gate {N k : ℕ} {s w e : ℝ}
    (hN : 646000 ≤ N) (hk2 : 2 ≤ k) (hk11 : k ≤ 11)
    (hs : s ≤ (N : ℝ)/(k-1 : ℕ)) (hw : w < (N : ℝ)/(2951/100))
    (he : e ≤ (TerminalA k+(SourceCount k : ℝ)-1)*w+
      TerminalB k-(SourceCount k : ℝ)+1+904) : 4*s+4*w+4*e < 5*N := by
  have hn : (646000 : ℝ) ≤ N := by exact_mod_cast hN
  interval_cases k <;> norm_num [TerminalA,TerminalB,SourceCount] at hs he ⊢ <;>
    nlinarith only [hn,hs,hw,he]


#print axioms all_rank_native_gate
end
end JSP233.NativeGates213
