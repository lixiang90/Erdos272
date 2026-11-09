module

public import Erdos272.Arithmetic.UniformRat208
public import Erdos272.Resources.UniformEnvelope208

@[expose] public section

/-! The frozen finite height test is executable over rationals and kernel-sound. -/
namespace JSP233.UniformDecision208
open UniformRat208 UniformEnvelope208 UniformActual208 UniformScale208 Set
set_option maxHeartbeats 0

def REnd (M z q : ℚ) : ℚ := q/z+7*M/25+1
def RDecision (M T z q : ℚ) : Prop := q≤RB T z M ∨0<z ∧
  q≤RP T z M ∧q≤RP (REnd M z q) z M ∧
  (3*z-1∈Icc T (REnd M z q) →q≤RP (3*z-1) z M) ∧
  ((5*z-2)/2∈Icc T (REnd M z q) →q≤RP ((5*z-2)/2) z M)
instance (M T z q : ℚ) : Decidable (RDecision M T z q) := by unfold RDecision;infer_instance
def check (M T z q : ℚ) : Bool := decide (RDecision M T z q)

@[simp] theorem end_cast (M z q : ℚ) : (REnd M z q : ℝ)=HeightEnd (M : ℝ) z q := by
  simp only [REnd,HeightEnd,Rat.cast_add,Rat.cast_div,Rat.cast_mul,Rat.cast_one,Rat.cast_ofNat]

theorem p_inequality {q y z M : ℚ} (hq : q≤RP y z M) : (q : ℝ)≤P (y : ℝ) z M := by
  rw [← P_cast]
  exact_mod_cast hq

theorem decision_cast {M T z q : ℚ} (hc : RDecision M T z q) :
    Decision (M : ℝ) T z q := by
  rcases hc with hb | ⟨hz,hqT,hqY,hc1,hc2⟩
  · left
    rw [← B_cast]
    exact_mod_cast hb
  · right
    refine ⟨by exact_mod_cast hz,p_inequality hqT,?_,?_,?_⟩
    · simpa only [end_cast] using p_inequality hqY
    · intro hh
      have hcut : ((3*z-1 : ℚ) : ℝ)=3*(z : ℝ)-1 := by
        simp only [Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_one]
      have hreal : ((3*z-1 : ℚ) : ℝ)∈Icc (T : ℝ) (REnd M z q : ℝ) := by
        simpa only [hcut,end_cast] using hh
      have hrat : 3*z-1∈Icc T (REnd M z q) := ⟨by exact_mod_cast hreal.1,by exact_mod_cast hreal.2⟩
      simpa only [hcut] using p_inequality (hc1 hrat)
    · intro hh
      have hcut : (((5*z-2)/2 : ℚ) : ℝ)=(5*(z : ℝ)-2)/2 := by
        simp only [Rat.cast_div,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat]
      have hreal : (((5*z-2)/2 : ℚ) : ℝ)∈Icc (T : ℝ) (REnd M z q : ℝ) := by
        simpa only [hcut,end_cast] using hh
      have hrat : (5*z-2)/2∈Icc T (REnd M z q) := ⟨by exact_mod_cast hreal.1,by exact_mod_cast hreal.2⟩
      simpa only [hcut] using p_inequality (hc2 hrat)

theorem check_sound {M T z q : ℚ} (hc : check M T z q=true) : Decision (M : ℝ) T z q := by
  exact decision_cast (of_decide_eq_true hc)

#print axioms decision_cast
#print axioms check_sound
end JSP233.UniformDecision208
