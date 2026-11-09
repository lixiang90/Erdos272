module

public import Erdos272.Arithmetic.UniformSourceCore208
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! Global monotonicity of the exact floor-step weight, including every
breakpoint, follows by induction over the actual step index. -/
namespace JSP233.StepWeightShape208
open UniformSourceCore208
noncomputable section
set_option maxHeartbeats 0

def Poly (D : ℕ) (s x : ℝ) : ℝ := (D : ℝ)*s*x-(D : ℝ)*((D : ℝ)+1)*x^2/2

theorem poly_same {D : ℕ} {s x y : ℝ} (hxy : x ≤ y)
    (hx : s ≤ ((D : ℝ)+1)*x) : Poly D s y ≤ Poly D s x := by
  have hfac : 0 ≤ ((D : ℝ)+1)*(x+y)/2-s := by
    have hh := mul_le_mul_of_nonneg_left hxy (show 0 ≤ (D : ℝ)+1 by positivity)
    linarith only [hx, hh]
  have hp : 0 ≤ (D : ℝ)*(y-x)*(((D : ℝ)+1)*(x+y)/2-s) := by positivity
  have hid : Poly D s x-Poly D s y =
      (D : ℝ)*(y-x)*(((D : ℝ)+1)*(x+y)/2-s) := by unfold Poly; ring
  linarith only [hp, hid]

theorem poly_boundary (D : ℕ) (s : ℝ) :
    Poly (D+1) s (s/((D : ℝ)+1)) = Poly D s (s/((D : ℝ)+1)) := by
  have hd : (D : ℝ)+1 ≠ 0 := by positivity
  unfold Poly
  push_cast
  field_simp
  ring

/-- The closed cells include both sides of a step boundary, so the induction
proves continuity-compatible monotonicity without omitting exceptional points. -/
theorem poly_cross (D : ℕ) : ∀ E : ℕ, ∀ s x y : ℝ,
    0 < s → 0 < x → x ≤ y → E ≤ D →
    (D : ℝ)*x ≤ s → s ≤ ((D : ℝ)+1)*x →
    (E : ℝ)*y ≤ s → s ≤ ((E : ℝ)+1)*y → Poly E s y ≤ Poly D s x := by
  induction D with
  | zero =>
    intro E s x y hs hx hxy hED hDx hxD hEy hyE
    have hE : E=0 := by omega
    simp only [hE, Poly, Nat.cast_zero, zero_mul, sub_self, le_refl]
  | succ D ih =>
    intro E s x y hs hx hxy hED hDx hxD hEy hyE
    by_cases hEq : E=D+1
    · subst E
      exact poly_same hxy hxD
    · have hED' : E ≤ D := by omega
      have hDpos : (0 : ℝ) < (D : ℝ)+1 := by positivity
      let c := s/((D : ℝ)+1)
      have hc : 0 < c := div_pos hs hDpos
      have hcx : x ≤ c := by
        apply (le_div_iff₀ hDpos).mpr
        simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using hDx
      have hcy : c ≤ y := by
        apply (div_le_iff₀ hDpos).mpr
        have hEreal : (E : ℝ)+1 ≤ (D : ℝ)+1 := by exact_mod_cast Nat.succ_le_succ hED'
        have hh := mul_le_mul_of_nonneg_right hEreal (le_trans hx.le hxy)
        linarith only [hyE, hh]
      have hcmul : ((D : ℝ)+1)*c=s := by dsimp only [c]; field_simp
      have hrec := ih E s c y hs hc hcy hED' (by nlinarith only [hcmul, hc.le])
        (by linarith only [hcmul]) hEy hyE
      have htop := poly_same (D := D+1) hcx hxD
      change Poly (D+1) s (s/((D : ℝ)+1)) ≤ Poly (D+1) s x at htop
      rw [poly_boundary] at htop
      exact hrec.trans htop

theorem step_bounds {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) :
    (Step s x : ℝ)*x ≤ s ∧ s < ((Step s x : ℝ)+1)*x := by
  have hlo := Nat.floor_le (div_nonneg hs hx.le)
  have hhi := Nat.lt_floor_add_one (s/x)
  exact ⟨(le_div_iff₀ hx).mp hlo, (div_lt_iff₀ hx).mp hhi⟩

theorem w_antitone {s x y : ℝ} (hs : 0 < s) (hx : 0 < x) (hxy : x ≤ y) :
    w s y ≤ w s x := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hD := step_bounds hs.le hx
  have hE := step_bounds hs.le hy
  have hstep : Step s y ≤ Step s x := Nat.floor_mono (div_le_div_of_nonneg_left hs.le hx hxy)
  exact poly_cross (Step s x) (Step s y) s x y hs hx hxy hstep hD.1 hD.2.le hE.1 hE.2.le

theorem w_nonneg {s x : ℝ} (hs : 0 ≤ s) (hx : 0 < x) : 0 ≤ w s x := by
  have hb := step_bounds hs hx
  by_cases hD : Step s x=0
  · norm_num [w, hD]
  · have hDreal : (1 : ℝ) ≤ Step s x := by exact_mod_cast (by omega : 1 ≤ Step s x)
    have hfac : 0 ≤ s-((Step s x : ℝ)+1)*x/2 := by
      have hh := mul_le_mul_of_nonneg_right hDreal hx.le
      linarith only [hb.1, hh]
    have hp : 0 ≤ (Step s x : ℝ)*x*(s-((Step s x : ℝ)+1)*x/2) := by positivity
    unfold w
    nlinarith only [hp]

#print axioms w_antitone
#print axioms w_nonneg
end
end JSP233.StepWeightShape208
