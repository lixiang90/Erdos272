import Erdos272.Arithmetic.StepWeightIntegral208

/-! Exact finite step sums on the short tail; no zeta approximation enters. -/
namespace JSP233.StepWeightMoment208
open UniformSourceCore208 StepWeightShape208 StepWeightTail208 StepWeightIntegral208
open MeasureTheory Set
open scoped BigOperators Interval
noncomputable section
set_option maxHeartbeats 0

theorem polynomial_sum (D : ℕ) (s x : ℝ) :
    (∑ d ∈ Finset.Icc 1 D, x*(s-(d : ℝ)*x)) = Poly D s x := by
  induction D with
  | zero => simp [Poly]
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ D+1), ih]
    unfold Poly
    push_cast
    ring

theorem finite_steps {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hstep : Step s x ≤ 5) :
    w s x = ∑ d ∈ Finset.Icc 1 (5 : ℕ), x*max (s-(d : ℝ)*x) 0 := by
  have hb := step_bounds hs hx
  have hsub : Finset.Icc 1 (Step s x) ⊆ Finset.Icc 1 5 := by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  have htrunc : (∑ d ∈ Finset.Icc 1 (Step s x), x*max (s-(d : ℝ)*x) 0) =
      ∑ d ∈ Finset.Icc 1 (5 : ℕ), x*max (s-(d : ℝ)*x) 0 := by
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hdgt : Step s x+1 ≤ d := by
      simp only [Finset.mem_Icc, not_and_or] at hnot
      omega
    have hdR : (Step s x : ℝ)+1 ≤ d := by exact_mod_cast hdgt
    have hh := mul_le_mul_of_nonneg_right hdR hx.le
    rw [max_eq_right (by linarith only [hb.2.le, hh]), mul_zero]
  rw [← htrunc]
  calc
    _ = ∑ d ∈ Finset.Icc 1 (Step s x), x*(s-(d : ℝ)*x) := (polynomial_sum _ s x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      have hdR : (d : ℝ) ≤ Step s x := by exact_mod_cast (Finset.mem_Icc.mp hd).2
      have hh := mul_le_mul_of_nonneg_right hdR hx.le
      rw [max_eq_left (by linarith only [hb.1, hh])]

theorem w_self {s : ℝ} (hs : 0 < s) : w s s=0 := by
  unfold w Step
  simp only [div_self (ne_of_gt hs), Nat.floor_one, Nat.cast_one]
  ring

def Term (d : ℕ) (s x : ℝ) : ℝ := x*max (s-(d : ℝ)*x) 0

def Tail (d : ℕ) (s m : ℝ) : ℝ :=
  if (d : ℝ)*m ≤ s then s^3/(6*(d : ℝ)^2)-s*m^2/2+(d : ℝ)*m^3/3 else 0

theorem term_integral {d : ℕ} (hd : 1 ≤ d) {s m : ℝ}
    (hs : 0 ≤ s) (hm : 0 ≤ m) (hms : m ≤ s) :
    (∫ x in m..s, Term d s x) = Tail d s m := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hcont : Continuous (Term d s) := by unfold Term; fun_prop
  let c := s/(d : ℝ)
  have hcmul : (d : ℝ)*c=s := by dsimp only [c]; field_simp
  have hcs : c ≤ s := by
    apply (div_le_iff₀ hd0).mpr
    nlinarith only [mul_nonneg hs (sub_nonneg.mpr hd1)]
  unfold Tail
  split_ifs with hcut
  · have hmc : m ≤ c := by apply (le_div_iff₀ hd0).mpr; nlinarith only [hcut]
    have hzero : (∫ x in c..s, Term d s x) = 0 := by
      calc
        _ = ∫ _x in c..s, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hh : c ≤ x ∧ x ≤ s := by simpa only [uIcc_of_le hcs, mem_Icc] using hx
          have hmul := mul_le_mul_of_nonneg_left hh.1 hd0.le
          unfold Term
          rw [max_eq_right (by linarith only [hcmul, hmul]), mul_zero]
        _ = _ := by simp
    have hfirst : (∫ x in m..c, Term d s x) =
        -(d : ℝ)*(c^3-m^3)/3+s*(c^2-m^2)/2 := by
      calc
        _ = ∫ x in m..c, -(d : ℝ)*x^2+s*x+0 := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hh : m ≤ x ∧ x ≤ c := by simpa only [uIcc_of_le hmc, mem_Icc] using hx
          have hmul := mul_le_mul_of_nonneg_left hh.2 hd0.le
          unfold Term
          rw [max_eq_left (by linarith only [hcmul, hmul])]
          ring
        _ = _ := by rw [quadratic_integral]; ring
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable m c) (hcont.intervalIntegrable c s), hfirst, hzero, add_zero]
    dsimp only [c]
    field_simp
    ring
  · calc
      _ = ∫ _x in m..s, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hh : m ≤ x ∧ x ≤ s := by simpa only [uIcc_of_le hms, mem_Icc] using hx
        have hmul := mul_le_mul_of_nonneg_left hh.1 hd0.le
        unfold Term
        rw [max_eq_right (by linarith only [hcut, hmul]), mul_zero]
      _ = _ := by simp

theorem raw_tail_sum (D : ℕ) (s m : ℝ) :
    (∑ d ∈ Finset.Icc 1 D, (s^3/(6*(d : ℝ)^2)-s*m^2/2+(d : ℝ)*m^3/3)) =
      s^3/6*H2 D-(D : ℝ)*s*m^2/2+(D : ℝ)*((D : ℝ)+1)*m^3/6 := by
  induction D with
  | zero => simp [H2]
  | succ D ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1≤D+1),ih]
    unfold H2
    rw [Finset.sum_Icc_succ_top (by omega : 1≤D+1)]
    push_cast
    field_simp
    ring

theorem finite_tail {s m : ℝ} (hs : 0≤s) (hm : 0<m) (hstep : Step s m≤5) :
    (∑ d ∈ Finset.Icc 1 (5 : ℕ), Tail d s m) = s^3/6*UniformSourceCore208.Sigma-I s m := by
  have hb := step_bounds hs hm
  have hsub : Finset.Icc 1 (Step s m) ⊆ Finset.Icc 1 5 := by
    intro d hd
    simp only [Finset.mem_Icc] at hd ⊢
    omega
  have htrunc : (∑ d ∈ Finset.Icc 1 (Step s m), Tail d s m) =
      ∑ d ∈ Finset.Icc 1 5, Tail d s m := by
    apply Finset.sum_subset hsub
    intro d hd hnot
    have hdgt : Step s m+1≤d := by
      simp only [Finset.mem_Icc,not_and_or] at hnot
      have hd1 := (Finset.mem_Icc.mp hd).1
      omega
    have hdR : (Step s m : ℝ)+1≤d := by exact_mod_cast hdgt
    have hh := mul_le_mul_of_nonneg_right hdR hm.le
    exact if_neg (by linarith only [hb.2,hh])
  rw [← htrunc]
  have heq : (∑ d ∈ Finset.Icc 1 (Step s m), Tail d s m) =
      ∑ d ∈ Finset.Icc 1 (Step s m), (s^3/(6*(d : ℝ)^2)-s*m^2/2+(d : ℝ)*m^3/3) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdR : (d : ℝ)≤Step s m := by exact_mod_cast (Finset.mem_Icc.mp hd).2
    have hh := mul_le_mul_of_nonneg_right hdR hm.le
    exact if_pos (by linarith only [hb.1,hh])
  rw [heq,raw_tail_sum]
  unfold I
  ring

theorem integral_eq_moment {s m : ℝ} (hs : 0≤s) (hm : 0<m) (hms : m≤s)
    (hsm : s<6*m) :
    (∫ x in m..s, w s x) = s^3/6*UniformSourceCore208.Sigma-I s m := by
  have he : (∫ x in m..s, w s x) =
      ∫ x in m..s, ∑ d ∈ Finset.Icc 1 (5 : ℕ), Term d s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hh : m≤x ∧ x≤s := by simpa only [uIcc_of_le hms,mem_Icc] using hx
    exact finite_steps hs (by linarith only [hm,hh.1])
      (step_le_five hs (by linarith only [hm,hh.1]) (by linarith only [hsm,hh.1]))
  rw [he,intervalIntegral.integral_finsetSum]
  · calc
      _ = ∑ d ∈ Finset.Icc 1 (5 : ℕ), Tail d s m := by
        apply Finset.sum_congr rfl
        intro d hd
        exact term_integral (Finset.mem_Icc.mp hd).1 hs hm.le hms
      _ = _ := finite_tail hs hm (step_le_five hs hm hsm)
  · intro d hd
    exact (show Continuous (Term d s) by unfold Term; fun_prop).intervalIntegrable m s

#print axioms finite_steps
#print axioms term_integral
#print axioms integral_eq_moment
end
end JSP233.StepWeightMoment208
