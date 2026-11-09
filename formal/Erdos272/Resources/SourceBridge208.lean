module

public import Erdos272.Counting.TripleCodes208
public import Erdos272.Arithmetic.TotientConvolution208

@[expose] public section

/-! # Exact unit source bounds for actual families

The chain runs from actual AP covers of actual triples, through the internally
proved integer AP extremal theorem and the totient convolution, to the exact
physical source function. A checked finite table can therefore be consumed
without assuming an unproved source-mass oracle.
-/
namespace JSP233.SourceBridge208
open StarCompletion PureSource208 IntrinsicTriples208 TripleCodes208 TotientConvolution208
open scoped Classical BigOperators
noncomputable section

/-- The longest AP is taken over subsets of the actual source itself. -/
def MaxAPSize (S : Finset ℤ) : ℕ :=
  (S.powerset.filter IsAP).sup Finset.card

def Defect (S : Finset ℤ) : ℕ := S.card - MaxAPSize S

theorem AP_card_le_max {S R : Finset ℤ} (hR : IsAP R) (hRS : R ⊆ S) :
    R.card ≤ MaxAPSize S := by
  apply Finset.le_sup
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hRS, hR⟩

theorem maxAPSize_le_card (S : Finset ℤ) : MaxAPSize S ≤ S.card := by
  apply Finset.sup_le
  intro R hR
  exact Finset.card_le_card (Finset.mem_powerset.mp (Finset.mem_filter.mp hR).1)

theorem two_le_maxAPSize {S : Finset ℤ} (hS : 2 ≤ S.card) : 2 ≤ MaxAPSize S := by
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  have hpair : ({a, b} : Finset ℤ) ⊆ S := by
    exact Finset.insert_subset_iff.mpr ⟨ha, Finset.singleton_subset_iff.mpr hb⟩
  simpa only [Finset.card_pair hab] using AP_card_le_max (pair_isAP a b) hpair

/-- Every actual source with the specified AP defect supplies the exact
integer triple mass used by the unit table. -/
theorem actual_physical_source {S : Finset ℤ} {e : ℕ}
    (he : 2 ≤ S.card - e)
    (hAP : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ S.card - e) :
    physicalK S.card e ≤ (Pool S).card := by
  have hmass := actual_intrinsic_lower hAP
  have hsplit := source_prefix_add_tail he
  omega

/-- This endpoint uses the actual longest AP and its actual defect; no
separate source-wise AP counting hypothesis is needed. -/
theorem actual_source_of_defect {S : Finset ℤ} {e : ℕ}
    (hS : 2 ≤ S.card) (he : e ≤ Defect S) :
    physicalK S.card e ≤ (Pool S).card := by
  have hmax := maxAPSize_le_card S
  have htwo := two_le_maxAPSize hS
  unfold Defect at he
  apply actual_physical_source (by omega)
  intro R hR hRS
  have hRmax := AP_card_le_max hR hRS
  omega

theorem actual_finiteMinimum_source {S : Finset ℤ} {e T H : ℕ}
    (hTH : T ≤ H) (hTS : T ≤ S.card) (hSH : S.card ≤ H)
    (he : 2 ≤ S.card - e)
    (hAP : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ S.card - e) :
    finiteMinimum T H e hTH ≤ (Pool S).card :=
  (finiteMinimum_le hTH hTS hSH).trans (actual_physical_source he hAP)

/-- A Lean-checked threshold is valid for every actual physical source
inside its finite size window, including sources with a larger defect. -/
theorem actual_checked_threshold {S : Finset ℤ} {e f b T H : ℕ}
    (hTH : T ≤ H) (hc : checkFloor T H e b = true)
    (hef : e ≤ f) (hTS : T ≤ S.card) (hSH : S.card ≤ H)
    (hf : 2 ≤ S.card - f)
    (hAP : ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ S.card - f) :
    b ≤ (Pool S).card :=
  (threshold_sound hTH hc hef hTS hSH).trans (actual_physical_source hf hAP)

/-- All checked sources consume one actual global pool. -/
theorem actual_family_threshold_count {Ω : Finset ℤ} {F : Finset (Finset ℤ)}
    (hF : Legal Ω F) {e b T H : ℕ} (hTH : T ≤ H)
    (hc : checkFloor T H e b = true)
    (f : Finset ℤ → ℕ)
    (hf : ∀ S ∈ F, e ≤ f S ∧ T ≤ S.card ∧ S.card ≤ H ∧ 2 ≤ S.card - f S)
    (hAP : ∀ S ∈ F, ∀ R : Finset ℤ, IsAP R → R ⊆ S → R.card ≤ S.card - f S) :
    b * F.card ≤ Ω.card.choose 3 := by
  apply actual_count_of_mass hF
  intro S hS
  obtain ⟨hef, hTS, hSH, htwo⟩ := hf S hS
  exact actual_checked_threshold hTH hc hef hTS hSH htwo (hAP S hS)

#print axioms actual_physical_source
#print axioms actual_source_of_defect
#print axioms actual_checked_threshold
#print axioms actual_family_threshold_count
end
end JSP233.SourceBridge208
