import Erdos272.Resources.InitialProfile218
import Erdos272.Counting.UnitCount218

/-! The actual unit omitters already have their endpoint envelope before
any assertion that all retained omitters are intervals. -/
namespace JSP233.UnitAvoider218
open StarCompletion APGeometry APCount41 DenseDeletion40
open InitialProfile218 UnitCount218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_unit_endpoint_count {N L R : ℕ} {U : Finset (Finset ℤ)}
    (hRN : R≤N) (hground : ∀S∈U,S⊆Ground N)
    (hne : ∀S∈U,S.Nonempty)
    (hstep : ∀S∈U,∃p:ℤ,APAt 1 p S)
    (hout : ∀S∈U,(∃u∈S,u≤(L : ℤ)) ∧ ∃v∈S,(R : ℤ)≤v) :
    U.card≤L*(N-R+1) := by
  let X := {S // S∈U}
  let f : X→ℤ×ℤ := fun S => (Low S.val,High S.val)
  have hm : Set.MapsTo f (Finset.univ : Finset X)
      ((Finset.Icc (1 : ℤ) (L : ℤ)).product (Finset.Icc (R : ℤ) (N : ℤ))) := by
    intro S _hS
    have hLow := (mem_ground N (Low S.val)).mp
      (hground S.val S.property (low_spec (hne S.val S.property)).1)
    have hHigh := (mem_ground N (High S.val)).mp
      (hground S.val S.property (high_spec (hne S.val S.property)).1)
    obtain ⟨⟨u,hu,huL⟩,v,hv,hRv⟩ := hout S.val S.property
    have hLu := (low_spec (hne S.val S.property)).2 u hu
    have hvH := (high_spec (hne S.val S.property)).2 v hv
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hLow.1,hLu.trans huL⟩,
        Finset.mem_Icc.mpr ⟨hRv.trans hvH,hHigh.2⟩⟩
  have hi : Function.Injective f := by
    intro S T he
    obtain ⟨p,hp⟩ := hstep S.val S.property
    obtain ⟨q,hq⟩ := hstep T.val T.property
    apply Subtype.ext
    exact same_step_equal_of_endpoints (d := 1) (hne S.val S.property)
      (hne T.val T.property) hp hq (congrArg Prod.fst he) (congrArg Prod.snd he)
  have hleft : (Finset.Icc (1 : ℤ) (L : ℤ)).card=L := by
    rw [Int.card_Icc]
    omega
  have hright : (Finset.Icc (R : ℤ) (N : ℤ)).card=N-R+1 := by
    rw [Int.card_Icc]
    omega
  have hh := Finset.card_le_card_of_injOn f hm hi.injOn
  simpa [X,hleft,hright] using hh

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

#print axioms actual_unit_endpoint_count
#print axioms actual_avoid_unit_endpoint_count
#print axioms actual_avoid_unit_width_count
end
end JSP233.UnitAvoider218
