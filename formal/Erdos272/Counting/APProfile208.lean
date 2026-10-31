import Erdos272.Counting.APLength208
import Erdos272.Arithmetic.APCoupling208
import Erdos272.Arithmetic.TerminalGcd208

/-! The continuous AP profile follows from actual integer length counts. -/
namespace JSP233.APProfile208
open APLength208
open StarCompletion APGeometry
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def Profile (N x : ℝ) : ℝ :=
  if 2 * x ≤ N then x^2 / 2 else N^2 / 4 - (N - x)^2 / 2

theorem profile_zero (N : ℕ) : Profile N 0 = 0 := by
  have hh : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  simp only [Profile, mul_zero, if_pos hh, zero_pow (by decide : 2 ≠ 0), zero_div]

theorem length_increment {N ell : ℕ} (hell : 1 ≤ ell) (hN : ell ≤ N) :
    ((min ell (N - ell + 1) : ℕ) : ℝ) ≤ Profile N ell - Profile N ((ell : ℝ) - 1) + 1 := by
  have hellR : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have hNR : (ell : ℝ) ≤ N := by exact_mod_cast hN
  have hleft : ((min ell (N - ell + 1) : ℕ) : ℝ) ≤ ell := by exact_mod_cast min_le_left ell (N - ell + 1)
  have hright : ((min ell (N - ell + 1) : ℕ) : ℝ) ≤ (N : ℝ) - ell + 1 := by
    have hh := min_le_right ell (N - ell + 1)
    have hc : ((N - ell + 1 : ℕ) : ℝ) = (N : ℝ) - ell + 1 := by
      rw [Nat.cast_add, Nat.cast_sub hN, Nat.cast_one]
    rw [← hc]
    exact_mod_cast hh
  unfold Profile
  split_ifs with hnow hprev hprev
  · nlinarith only [hleft]
  · linarith only [hnow, hprev]
  · have hint : N + 1 ≤ 2 * ell := by
      have hh : ¬ 2 * ell ≤ N := by exact_mod_cast hnow
      omega
    have hgap : (1 : ℝ) ≤ 2 * (ell : ℝ) - N := by
      have hiR : (N : ℝ) + 1 ≤ 2 * (ell : ℝ) := by exact_mod_cast hint
      linarith only [hiR]
    have hprod : 0 ≤ (2 * (ell : ℝ) - N) * (N + 2 - 2 * ell) := by
      apply mul_nonneg <;> linarith
    nlinarith only [hright, hgap, hprod]
  · nlinarith only [hright]

def SumLengths (N a : ℕ) : ℝ :=
  ∑ ell ∈ Finset.Icc 1 a, ((min ell (N - ell + 1) : ℕ) : ℝ)

theorem sum_lengths_bound {N a : ℕ} (haN : a ≤ N) :
    SumLengths N a ≤ Profile N a + a := by
  induction a with
  | zero => simp [SumLengths, profile_zero]
  | succ a ih =>
    have hprev := ih (by omega : a ≤ N)
    have hincr := length_increment (show 1 ≤ a + 1 by omega) haN
    have hstep : SumLengths N (a + 1) = SumLengths N a +
        ((min (a + 1) (N - (a + 1) + 1) : ℕ) : ℝ) := by
      exact TerminalGcd208.icc_step (fun ell => ((min ell (N - ell + 1) : ℕ) : ℝ))
        (a := 1) (H := a) (by omega)
    rw [hstep, Nat.cast_add, Nat.cast_one]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] at hincr
    linarith only [hprev, hincr]

theorem length_count_profile {N a : ℕ} (haN : a ≤ N) :
    (LengthCount N a : ℝ) ≤ Profile N a + a := by
  have hsub : (LengthCount N a : ℝ) ≤ SumLengths N a := by
    rw [LengthCount, Nat.cast_sum]
    unfold SumLengths
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    intro ell hell hnot
    positivity
  exact hsub.trans (sum_lengths_bound haN)

theorem profile_coefficient {N a : ℕ} (hN : 1 ≤ N) :
    Profile N a = (N : ℝ)^2 * APCoupling208.APCoefficient ((a : ℝ) / N) := by
  have hp : (0 : ℝ) < N := by exact_mod_cast hN
  have he : 2 * (a : ℝ) ≤ N ↔ (a : ℝ) / N ≤ 1 / 2 := by
    rw [div_le_iff₀ hp]
    constructor <;> intro hh <;> linarith only [hh]
  unfold Profile APCoupling208.APCoefficient
  split_ifs with hlow hratio hratio
  · field_simp
  · exact (hratio (he.mp hlow)).elim
  · exact (hlow (he.mpr hratio)).elim
  · field_simp

theorem actual_unit_step_profile {N a : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (haN : a ≤ N)
    (hlegal : Legal (Ground N) F)
    (hne : ∀ S ∈ F, S.Nonempty) (hlen : ∀ S ∈ F, 2 ≤ S.card ∧ S.card ≤ a)
    (hstep : ∀ S ∈ F, ∃ p : ℤ, APGeometry.APAt 1 p S) :
    (F.card : ℝ) ≤ (N : ℝ)^2 * APCoupling208.APCoefficient ((a : ℝ) / N) + N := by
  have hcount := actual_unit_step_length_count hlegal hne hlen hstep
  have hreal : (F.card : ℝ) ≤ LengthCount N a := by exact_mod_cast hcount
  have hp := length_count_profile haN
  rw [profile_coefficient hN] at hp
  have haR : (a : ℝ) ≤ N := by exact_mod_cast haN
  linarith only [hreal, hp, haR]

#print axioms length_increment
#print axioms length_count_profile
#print axioms actual_unit_step_profile
end
end JSP233.APProfile208
