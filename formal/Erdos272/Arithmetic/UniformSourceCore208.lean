import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! Exact stepwise polynomials of the continuous uniform source.
This module proves the scale law algebraically; the actual integer source
bridge additionally needs the finite F/W bounds and the semiconvex tail. -/
namespace JSP233.UniformSourceCore208
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def Sigma : ℝ := 1644934067/1000000000
def Delta : ℝ := 76/125

def Step (s m : ℝ) : ℕ := Nat.floor (s/m)

def H2 (D : ℕ) : ℝ := ∑ d ∈ Finset.Icc 1 D, 1/(d : ℝ)^2

def w (s m : ℝ) : ℝ :=
  (Step s m : ℝ)*s*m-(Step s m : ℝ)*((Step s m : ℝ)+1)*m^2/2

def I (s m : ℝ) : ℝ :=
  (Step s m : ℝ)*s*m^2/2-(Step s m : ℝ)*((Step s m : ℝ)+1)*m^3/6+
    s^3/6*(Sigma-H2 (Step s m))

def Jstar (s e : ℝ) : ℝ :=
  s^3/6-Delta*I s (s-e)+Delta/2*w s (s-e)-11/80*s^2-2014/625*s

theorem step_scale {v s m : ℝ} (hv : v ≠ 0) : Step (v*s) (v*m) = Step s m := by
  unfold Step
  congr 1
  by_cases hm : m=0
  · simp only [hm, mul_zero, div_zero]
  · field_simp

theorem w_scale {v s m : ℝ} (hv : v ≠ 0) : w (v*s) (v*m) = v^2*w s m := by
  unfold w
  rw [step_scale hv]
  ring

theorem I_scale {v s m : ℝ} (hv : v ≠ 0) : I (v*s) (v*m) = v^3*I s m := by
  unfold I
  rw [step_scale hv]
  ring

theorem w_square_upper (s m : ℝ) : w s m ≤ (s-m/2)^2/2 := by
  let theta := s-(Step s m : ℝ)*m
  have hid : w s m = s^2/2-s*m/2+theta*(m-theta)/2 := by
    unfold w
    dsimp only [theta]
    ring
  have hs := sq_nonneg (2*theta-m)
  nlinarith only [hid, hs]

/-- A slightly weaker than optimal quadratic bound suffices for the exact
scale comparison and avoids introducing any numerical approximation. -/
theorem w_quadratic_upper {s m : ℝ} (hs : 0 ≤ s) (hm : s/5 ≤ m) (hms : m ≤ s) :
    w s m ≤ (81/200 : ℝ)*s^2 := by
  have hw := w_square_upper s m
  have hprod : 0 ≤ (9*s/10-(s-m/2))*(9*s/10+(s-m/2)) := by
    apply mul_nonneg <;> linarith only [hs, hm, hms]
  nlinarith only [hw, hprod]

theorem Jstar_scale_difference {v y z : ℝ} (hv : v ≠ 0) :
    Jstar (v*y) (v*z)-v^3*Jstar y z =
      v^2*(v-1)*(11/80*y^2-Delta/2*w y (y-z))+
        (2014/625)*v*(v^2-1)*y := by
  unfold Jstar
  rw [show v*y-v*z=v*(y-z) by ring, I_scale hv, w_scale hv]
  ring

theorem Jstar_scale {v y z : ℝ} (hv : 1 ≤ v) (hy : 0 ≤ y)
    (hz : 0 ≤ z) (hzy : z ≤ 4*y/5) :
    v^3*Jstar y z ≤ Jstar (v*y) (v*z) := by
  have hv0 : 0 < v := by linarith only [hv]
  have hw := w_quadratic_upper (s := y) (m := y-z) hy
    (by linarith only [hzy]) (by linarith only [hz])
  have hquad : 0 ≤ 11/80*y^2-Delta/2*w y (y-z) := by
    unfold Delta
    nlinarith only [hw, sq_nonneg y]
  have hv2 : 0 ≤ v^2-1 := by nlinarith only [hv, sq_nonneg (v-1)]
  have hd := Jstar_scale_difference (y := y) (z := z) (ne_of_gt hv0)
  have hp1 : 0 ≤ v^2*(v-1)*(11/80*y^2-Delta/2*w y (y-z)) :=
    mul_nonneg (mul_nonneg (sq_nonneg v) (by linarith only [hv])) hquad
  have hp2 : 0 ≤ (2014/625 : ℝ)*v*(v^2-1)*y := by positivity
  linarith only [hd, hp1, hp2]

#print axioms w_scale
#print axioms Jstar_scale
end
end JSP233.UniformSourceCore208
