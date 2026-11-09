module

public import Erdos272.Resources.N291012.RootModel291012
public import Erdos272.Counting.UnitCount218

@[expose] public section

/-! The actual unit omitters already have their endpoint envelope before
any assertion that all retained omitters are intervals. -/
namespace JSP233.UnitAvoider291012
open StarCompletion APGeometry APCount41 DenseDeletion40
open RootModel291012 UnitCount218 UnitAvoider218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_avoid_unit_endpoint_count {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) :
    (AvoidUnitAP F (c : ℤ)).card≤L*(N-R+1) := by
  apply actual_unit_endpoint_count g.right_ground
  · intro S hS
    exact g.legal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1
  · intro S hS
    have ht := (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2.2.1
    exact Finset.card_pos.mp (by omega)
  · intro S hS
    obtain ⟨hU,_hcS⟩ := Finset.mem_filter.mp hS
    obtain ⟨_hSF,hAP,_htwo,hstep⟩ := Finset.mem_filter.mp hU
    obtain ⟨_hd,p,hp⟩ := actual_step hAP
    refine ⟨p,?_⟩
    simpa only [hstep,Nat.cast_one] using hp
  · intro S hS
    obtain ⟨hU,hcS⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSF,hAP,_htwo,_hstep⟩ := Finset.mem_filter.mp hU
    exact g.outside S (actual_ap_retained hSF hAP) hcS

theorem actual_avoid_unit_width_count {N c L R : ℕ}
    {F : Finset (Finset ℤ)} {P T : Finset ℤ}
    (g : Start N c L R F P T) :
    ((AvoidUnitAP F (c : ℤ)).card : ℝ) ≤
      ((L : ℝ)+(N-R))^2/4+((L : ℝ)+(N-R)) := by
  have hh := actual_avoid_unit_endpoint_count g
  have hc : ((AvoidUnitAP F (c : ℤ)).card : ℝ)≤(L : ℝ)*((N : ℝ)-R+1) := by
    have hhR : ((AvoidUnitAP F (c : ℤ)).card : ℝ)≤(L*(N-R+1) : ℕ) := by exact_mod_cast hh
    rw [Nat.cast_mul,Nat.cast_add,Nat.cast_sub g.right_ground,Nat.cast_one] at hhR
    exact hhR
  have hk : (0 : ℝ)≤(N : ℝ)-R := by
    have hRN : (R : ℝ)≤N := by exact_mod_cast g.right_ground
    linarith only [hRN]
  have hs := sq_nonneg ((L : ℝ)-((N : ℝ)-R))
  nlinarith only [hc,hk,hs]

#print axioms actual_avoid_unit_endpoint_count
#print axioms actual_avoid_unit_width_count
end
end JSP233.UnitAvoider291012
