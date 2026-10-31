import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Exact scale gates used by the actual r11 preparation.  Dyadic lower
bounds pay the cube at each real logarithmic index.  There is no unused
7200 J^3 gate that could impose an artificial lower bound on the original
problem.  This module alone makes no family-cardinality assertion. -/
namespace JSP233.PreparationScales119
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem dyadic_cube_gate {J : ℕ} (hJl : 27 ≤ J) (hJu : J ≤ 49) :
    1024 * J^3 ≤ 2^(J-1) := by
  interval_cases J <;> norm_num

theorem actual_log_gates {N : ℕ} (hN : 74320000 ≤ N) (hNu : N < 2^49) :
    let J := Nat.log 2 N + 1
    27 ≤ J ∧ J ≤ 49 ∧ N < 2^J ∧ 1024*J^3 ≤ N ∧ 468*J^3 ≤ N := by
  let J := Nat.log 2 N + 1
  have hn : N ≠ 0 := by omega
  have hl : 26 ≤ Nat.log 2 N :=
    (Nat.le_log_iff_pow_le (by decide : 1 < 2) hn).mpr
      ((by norm_num : (2:ℕ)^26 ≤ 74320000).trans hN)
  have hu : Nat.log 2 N < 49 := Nat.log_lt_of_lt_pow hn hNu
  have hJl : 27 ≤ J := by dsimp only [J]; omega
  have hJu : J ≤ 49 := by dsimp only [J]; omega
  have hp : 2^(J-1) ≤ N := by
    simpa only [J, Nat.add_sub_cancel] using Nat.pow_log_le_self 2 hn
  have hc : 1024*J^3 ≤ N := (dyadic_cube_gate hJl hJu).trans hp
  refine ⟨hJl, hJu, Nat.lt_pow_succ_log_self (by decide : 1 < 2) N, hc, ?_⟩
  change 468*J^3 ≤ N
  nlinarith only [hc, Nat.zero_le (J^3)]

#print axioms dyadic_cube_gate
#print axioms actual_log_gates
end JSP233.PreparationScales119
