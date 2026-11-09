module

public import Erdos272.Arithmetic.StepWeightShape208
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! Pointwise semiconvex control of the actual floor-step weight. -/
namespace JSP233.StepWeightTail208
open UniformSourceCore208 StepWeightShape208
noncomputable section
set_option maxHeartbeats 0

theorem poly_le_w {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (D : ℕ) :
    Poly D s x ≤ w s x := by
  let T := Step s x
  have hb := step_bounds hs hx
  have hid : w s x-Poly D s x =
      ((T : ℝ)-D)*x*(s-((T : ℝ)+D+1)*x/2) := by
    unfold w Poly
    dsimp only [T]
    ring
  by_cases hDT : D ≤ T
  · by_cases hEq : D=T
    · subst D
      exact le_rfl
    · have hlt : D+1 ≤ T := by omega
      have hltR : (D : ℝ)+1 ≤ T := by exact_mod_cast hlt
      have hmul := mul_le_mul_of_nonneg_right hltR hx.le
      have hleft : 0 ≤ ((T : ℝ)-D)*x := by
        apply mul_nonneg _ hx.le
        exact sub_nonneg.mpr (by exact_mod_cast hDT)
      have hright : 0 ≤ s-((T : ℝ)+D+1)*x/2 := by
        dsimp only [T] at hmul ⊢
        nlinarith only [hb.1, hmul]
      have hp := mul_nonneg hleft hright
      linarith only [hid, hp]
  · have hTD : T+1 ≤ D := by omega
    have hTDR : (T : ℝ)+1 ≤ D := by exact_mod_cast hTD
    have hmul := mul_le_mul_of_nonneg_right hTDR hx.le
    have hleft : ((T : ℝ)-D)*x ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hx.le
      exact sub_nonpos.mpr (by exact_mod_cast (by omega : T ≤ D))
    have hright : s-((T : ℝ)+D+1)*x/2 ≤ 0 := by
      dsimp only [T] at hmul ⊢
      nlinarith only [hb.2.le, hmul]
    have hp := mul_nonneg_of_nonpos_of_nonpos hleft hright
    linarith only [hid, hp]

theorem semiconvex_chord {s a x : ℝ} (hs : 0 ≤ s) (ha : 0 < a)
    (hax : a ≤ x) (hxa : x ≤ a+1) (hstep : Step s x ≤ 5) :
    w s x ≤ (a+1-x)*w s a+(x-a)*w s (a+1)+15*(x-a)*(a+1-x) := by
  let D := Step s x
  have hD : (D : ℝ) ≤ 5 := by exact_mod_cast hstep
  have hD0 : (0 : ℝ) ≤ D := by positivity
  have hprod : 0 ≤ (5-(D : ℝ))*((D : ℝ)+6) :=
    mul_nonneg (by linarith only [hD]) (by positivity)
  have hcoef : (D : ℝ)*((D : ℝ)+1)/2 ≤ 15 := by nlinarith only [hprod]
  have hterm := mul_le_mul_of_nonneg_right hcoef
    (mul_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hxa))
  have hleft := mul_le_mul_of_nonneg_left (poly_le_w hs ha D) (sub_nonneg.mpr hxa)
  have hright := mul_le_mul_of_nonneg_left (poly_le_w hs (by linarith only [ha] : 0 < a+1) D)
    (sub_nonneg.mpr hax)
  have hid : w s x = (a+1-x)*Poly D s a+(x-a)*Poly D s (a+1)+
      ((D : ℝ)*((D : ℝ)+1)/2)*((x-a)*(a+1-x)) := by
    unfold w Poly
    dsimp only [D]
    ring
  nlinarith only [hid, hterm, hleft, hright]

def Max5 (s x : ℝ) : ℝ := max (Poly 0 s x) (max (Poly 1 s x)
  (max (Poly 2 s x) (max (Poly 3 s x) (max (Poly 4 s x) (Poly 5 s x)))))

theorem max5_eq_w {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hstep : Step s x ≤ 5) :
    Max5 s x = w s x := by
  apply le_antisymm
  · unfold Max5
    repeat' apply max_le
    all_goals exact poly_le_w hs hx _
  · have hw : w s x=Poly (Step s x) s x := rfl
    rw [hw]
    generalize hD : Step s x=D at *
    interval_cases D <;> simp [Max5, le_max_iff]

theorem max5_continuous (s : ℝ) : Continuous (Max5 s) := by
  unfold Max5 Poly
  fun_prop

theorem step_le_five {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) (hsx : s < 6*x) : Step s x ≤ 5 := by
  have hlt : s/x < 6 := (div_lt_iff₀ hx).mpr hsx
  have hd : (Step s x : ℝ) < 6 := lt_of_le_of_lt (Nat.floor_le (div_nonneg hs hx.le)) hlt
  have hn : Step s x < 6 := by exact_mod_cast hd
  omega

#print axioms poly_le_w
#print axioms semiconvex_chord
#print axioms max5_eq_w
end
end JSP233.StepWeightTail208
