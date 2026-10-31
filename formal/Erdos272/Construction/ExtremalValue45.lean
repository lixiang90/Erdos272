import Erdos272.Construction.Construction45
import Mathlib.Data.Finset.Lattice.Fold

/-! The actual extremal value of all legal finite families on Ground N.
The exact equality is reduced to the remaining universal upper bound, with
the matching all-positive-N lower construction proved rather than supplied. -/
namespace JSP233.ExtremalValue45
open StarCompletion
open scoped Classical
noncomputable section

def Families (N : ℕ) : Finset (Finset (Finset ℤ)) :=
  ((Ground N).powerset.powerset).filter (Legal (Ground N))

def Value (N : ℕ) : ℕ := (Families N).sup Finset.card

theorem mem_families (N : ℕ) (F : Finset (Finset ℤ)) :
    F∈Families N ↔ Legal (Ground N) F := by
  constructor
  · intro hF
    exact (Finset.mem_filter.mp hF).2
  · intro hF
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,hF⟩
    intro S hS
    exact Finset.mem_powerset.mpr (hF.1 S hS)

theorem families_nonempty (N : ℕ) : (Families N).Nonempty := by
  refine ⟨∅,(mem_families N ∅).mpr ?_⟩
  simp [Legal]

theorem actual_card_le_value {N : ℕ} {F : Finset (Finset ℤ)} (hF : Legal (Ground N) F) :
    F.card≤Value N := Finset.le_sup ((mem_families N F).mpr hF)

theorem actual_value_attained (N : ℕ) :
    ∃ F : Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=Value N := by
  obtain ⟨F,hF,hcard⟩ := Finset.exists_mem_eq_sup (Families N) (families_nonempty N) Finset.card
  exact ⟨F,(mem_families N F).mp hF,hcard.symm⟩

theorem actual_lower_bound (N : ℕ) (hN : 1≤N) : B N≤Value N := by
  obtain ⟨F,hF,hcard⟩ := Construction45.szabo_lower_construction N hN
  simpa only [hcard] using actual_card_le_value hF

theorem actual_upper_bound_iff (N b : ℕ) :
    Value N≤b ↔ ∀ F : Finset (Finset ℤ),Legal (Ground N) F→F.card≤b := by
  constructor
  · intro hv F hF
    exact (actual_card_le_value hF).trans hv
  · intro h
    apply Finset.sup_le
    intro F hF
    exact h F ((mem_families N F).mp hF)

theorem exact_value_iff_actual_upper (N : ℕ) (hN : 1≤N) :
    Value N=B N ↔ ∀ F : Finset (Finset ℤ),Legal (Ground N) F→F.card≤B N := by
  constructor
  · intro he
    exact (actual_upper_bound_iff N (B N)).mp he.le
  · intro h
    exact le_antisymm ((actual_upper_bound_iff N (B N)).mpr h) (actual_lower_bound N hN)

theorem actual_counterexample_iff (N b : ℕ) :
    b<Value N ↔ ∃ F : Finset (Finset ℤ),Legal (Ground N) F ∧ b<F.card := by
  constructor
  · intro h
    obtain ⟨F,hF,he⟩ := actual_value_attained N
    exact ⟨F,hF,he.symm ▸ h⟩
  · rintro ⟨F,hF,hh⟩
    exact hh.trans_le (actual_card_le_value hF)

#print axioms mem_families
#print axioms families_nonempty
#print axioms actual_card_le_value
#print axioms actual_value_attained
#print axioms actual_lower_bound
#print axioms actual_upper_bound_iff
#print axioms exact_value_iff_actual_upper
#print axioms actual_counterexample_iff
end
end JSP233.ExtremalValue45
