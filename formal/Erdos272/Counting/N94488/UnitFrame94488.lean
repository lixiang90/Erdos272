module

public import Erdos272.Arithmetic.N94488.IntervalShadowFrame94488
public import Erdos272.Arithmetic.N291012.UnitShadowGeometry291012
public import Erdos272.Counting.N94488.RectangleMoment94488

@[expose] public section

namespace JSP233.UnitFrame94488
open StarCompletion APGeometry APCount41 UnitCount218
open APShadowCapacity16858 IntervalFamilyEndpoints16858
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_unit_frame {N : ℕ} {F : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) :
    ∃ (c : ℤ) (A B : ℕ), A+B ≤ N-1 ∧
      (∀ S ∈ UnitAP F, S ⊆ Finset.Icc (c-A) (c+B)) ∧
      Pairs c A B (UnitAP F) ⊆ (Finset.range A).product (Finset.range B) ∧
      ((UnitAP F).card : ℝ) ≤ (A : ℝ)+B+(Pairs c A B (UnitAP F)).card ∧
      (A : ℝ)^3+(B : ℝ)^3-A-B+
        6*(∑ p ∈ Pairs c A B (UnitAP F), ((p.1 : ℝ)+p.2+1)) ≤
          6*((APShadow (UnitAP F)).card : ℝ) := by
  have hsub : UnitAP F ⊆ F := Finset.filter_subset _ _
  have hlegal : Legal (Ground N) (UnitAP F) :=
    ⟨fun S hS => hF.1 S (hsub hS),
      fun S hS T hT hST => hF.2 S (hsub hS) T (hsub hT) hST⟩
  have htwo : ∀ S ∈ UnitAP F, 2 ≤ S.card :=
    fun S hS => (Finset.mem_filter.mp hS).2.2.1
  have hstep : ∀ S ∈ UnitAP F, ∃ p : ℤ, APAt (1 : ℤ) p S := by
    intro S hS
    obtain ⟨hSF, hAP, ht, hs⟩ := Finset.mem_filter.mp hS
    obtain ⟨hd, p, hp⟩ := actual_step hAP
    exact ⟨p, by simpa only [hs, Nat.cast_one] using hp⟩
  by_cases hne : (UnitAP F).Nonempty
  · obtain ⟨c, hc, hroot⟩ := actual_same_step_common_root hne hlegal
      (fun S hS => Finset.card_pos.mp (by have hh := htwo S hS; omega)) hstep
    obtain ⟨A, B, hsum, henv, hD, hcount, hshadow⟩ :=
      IntervalShadowFrame94488.actual_frame hc hlegal.1 hroot
        (fun S hS => by
          obtain ⟨p, hp⟩ := hstep S hS
          exact NonIntervalAP47.actual_step_one_interval hp) htwo
    exact ⟨c, A, B, hsum, henv, hD, hcount, hshadow⟩
  · have he : UnitAP F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨0, 0, 0, by omega, ?_, ?_, ?_, ?_⟩ <;>
      simp [he, Pairs, APShadow]

theorem frame_moment {A B : ℕ} {D : Finset (ℕ × ℕ)} {s x : ℝ}
    (hD : D ⊆ (Finset.range A).product (Finset.range B)) (hx : 0 ≤ x)
    (hshadow : (A : ℝ)^3+(B : ℝ)^3-A-B+
      6*(∑ p ∈ D, ((p.1 : ℝ)+p.2+1)) ≤ 6*s) :
    ((A : ℝ)+B)^3-6*((A : ℝ)*B-D.card)*((A : ℝ)+B-x)-x^3 ≤ 6*s+A+B := by
  have hm := RectangleMoment94488.rectangle_moment hD hx
  change (D.card : ℝ)*((A : ℝ)+B-x)+(A : ℝ)*B*(x-((A : ℝ)+B)/2)-x^3/6 ≤
    (∑ p ∈ D, ((p.1 : ℝ)+p.2+1)) at hm
  nlinarith only [hm, hshadow]

#print axioms actual_unit_frame
#print axioms frame_moment
end
end JSP233.UnitFrame94488
