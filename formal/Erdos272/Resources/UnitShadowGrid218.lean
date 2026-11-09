module

public import Erdos272.Resources.UnitShadowScalar218
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-! A discrete first-moment proof for an actual finite grid. -/
namespace JSP233.UnitShadowGrid218
open UnitShadowScalar218
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem finite_index_moment {α : Type*} [DecidableEq α]
    (D : Finset α) (idx : α → ℕ) (n R : ℕ)
    (hidx : ∀ p ∈ D, idx p ∈ Finset.range n)
    (hfib : ∀ i < n, (D.filter fun p => idx p = i).card ≤ R) :
    (D.card : ℝ)^2 ≤ (R : ℝ) * ∑ p ∈ D, (2*(idx p : ℝ)+1) := by
  let f : ℕ → ℝ := fun i => ((D.filter fun p => idx p = i).card : ℝ)
  have hf : ∀ i < n, 0 ≤ f i ∧ f i ≤ R := by
    intro i hi
    constructor
    · dsimp only [f]; positivity
    · dsimp only [f]; exact_mod_cast hfib i hi
  have hcount : (D.card : ℝ) = ∑ i ∈ Finset.range n, f i := by
    dsimp only [f]
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hidx
  have hmoment : (∑ i ∈ Finset.range n, (2*(i : ℝ)+1)*f i) =
      ∑ p ∈ D, (2*(idx p : ℝ)+1) := by
    have hh := Finset.sum_fiberwise_of_maps_to' hidx (fun i : ℕ => 2*(i : ℝ)+1)
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using hh
  have hh := bounded_column_moment n f R (by positivity) hf
  rw [←hcount, hmoment] at hh
  exact hh

theorem rectangle_x_moment {D : Finset (ℕ × ℕ)} {L R : ℕ}
    (hD : D ⊆ (Finset.range L).product (Finset.range R)) :
    (D.card : ℝ)^2 ≤ (R : ℝ) * ∑ p ∈ D, (2*(p.1 : ℝ)+1) := by
  apply finite_index_moment D Prod.fst L R
  · intro p hp
    exact (Finset.mem_product.mp (hD hp)).1
  · intro i _hi
    have hs : D.filter (fun p => p.1=i) ⊆
        ({i} : Finset ℕ).product (Finset.range R) := by
      intro p hp
      obtain ⟨hpD, hpi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hpi, (Finset.mem_product.mp (hD hpD)).2⟩
    have hh := Finset.card_le_card hs
    simpa using hh

theorem rectangle_y_moment {D : Finset (ℕ × ℕ)} {L R : ℕ}
    (hD : D ⊆ (Finset.range L).product (Finset.range R)) :
    (D.card : ℝ)^2 ≤ (L : ℝ) * ∑ p ∈ D, (2*(p.2 : ℝ)+1) := by
  apply finite_index_moment D Prod.snd R L
  · intro p hp
    exact (Finset.mem_product.mp (hD hp)).2
  · intro i _hi
    have hs : D.filter (fun p => p.2=i) ⊆
        (Finset.range L).product ({i} : Finset ℕ) := by
      intro p hp
      obtain ⟨hpD, hpi⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp (hD hpD)).1, Finset.mem_singleton.mpr hpi⟩
    have hh := Finset.card_le_card hs
    simpa using hh

theorem actual_discrete_shadow_mass {D : Finset (ℕ × ℕ)} {L R : ℕ}
    {h y : ℝ} (hD : D ⊆ (Finset.range L).product (Finset.range R))
    (hy : 0 ≤ y) (hK : y^2 = D.card)
    (hshadow : 6*h = (L : ℝ)^3+(R : ℝ)^3-L-R+
      3*((∑ p ∈ D, (2*(p.1 : ℝ)+1))+(∑ p ∈ D, (2*(p.2 : ℝ)+1)))) :
    8*y^3 ≤ 6*h+L+R := by
  let X : ℝ := (∑ p ∈ D, (2*(p.1 : ℝ)+1))/2
  let Y : ℝ := (∑ p ∈ D, (2*(p.2 : ℝ)+1))/2
  have hx0 : 0 ≤ X := by dsimp [X]; positivity
  have hy0 : 0 ≤ Y := by dsimp [Y]; positivity
  have hx := rectangle_x_moment hD
  have hy' := rectangle_y_moment hD
  apply discrete_shadow_mass (L := (L : ℝ)) (R := (R : ℝ)) (K := (D.card : ℝ))
    (X := X) (Y := Y) (by positivity) (by positivity) hy hx0 hy0 hK
  · dsimp only [X]; nlinarith only [hx]
  · dsimp only [Y]; nlinarith only [hy']
  · dsimp only [X, Y]
    linarith only [hshadow]

#print axioms finite_index_moment
#print axioms rectangle_x_moment
#print axioms rectangle_y_moment
#print axioms actual_discrete_shadow_mass
end
end JSP233.UnitShadowGrid218
