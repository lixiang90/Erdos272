import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Data.Nat.Choose.Basic
import Erdos272.Global.Global642498218
import Erdos272.Global.GlobalUpper53

/-! # JSP-000233 / Erdos #272: the formalized large-N result

All objects in the statements are defined below using only Lean/Mathlib.
Proofs reuse the project modules. For every N >= 642498,
`exact_value` proves `Value N = N.choose 2 + 1 + (N - 1) / 4`.
The universal upper bound and an attaining optimal family are also proved;
the lower bound holds for every positive N.

The remaining finite part is not assumed here. The all-positive-N problem
remains unfinished.
-/
namespace JSP233.PublicResults
open scoped Classical
noncomputable section

/-! ## Definitions of the original extremal problem -/

/-- The integer ground set {1, ..., N}. -/
def Ground (N : ℕ) : Finset ℤ :=
  (Finset.range N).image (fun i : ℕ => (i : ℤ) + 1)

/-- A nonempty finite arithmetic progression, including a singleton. -/
def IsAP (S : Finset ℤ) : Prop :=
  ∃ d p : ℤ, 0 < d ∧ ∃ lo hi : ℤ,
    (∀ x, x ∈ S ↔ lo ≤ x ∧ x ≤ hi ∧ d ∣ x - p) ∧ p ∈ S

/-- Distinct members have a nonempty arithmetic progression as intersection. -/
def Legal (Ω : Finset ℤ) (F : Finset (Finset ℤ)) : Prop :=
  (∀ S ∈ F, S ⊆ Ω) ∧
  (∀ S ∈ F, ∀ T ∈ F, S ≠ T → IsAP (S ∩ T))

/-- The conjectured value; natural-number division is floor division. -/
def B (N : ℕ) : ℕ := N.choose 2 + 1 + (N - 1) / 4

/-- All legal families of subsets of the actual ground set. -/
def Families (N : ℕ) : Finset (Finset (Finset ℤ)) :=
  ((Ground N).powerset.powerset).filter (Legal (Ground N))

/-- The maximum cardinality of a legal family. -/
def Value (N : ℕ) : ℕ := (Families N).sup Finset.card

/-! ## Proofs of the public results

The six definitions above are definitionally equal to the established model.
Lean checks that correspondence when applying the existing proof terms.
-/

theorem lower_bound (N : ℕ) (hN : 1≤N) : B N≤Value N :=
  ExtremalValue45.actual_lower_bound N hN

theorem upper_bound {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 642498≤N) (hF : Legal (Ground N) F) : F.card≤B N :=
  Global642498218.actual_original_upper_bound hN hF

theorem exact_value (N : ℕ) (hN : 642498≤N) : Value N=B N :=
  Global642498218.actual_value_eq_B N hN

theorem optimal_family (N : ℕ) (hN : 642498≤N) :
    ∃F:Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N ∧
      ∀G:Finset (Finset ℤ),Legal (Ground N) G→G.card≤F.card :=
  Global642498218.actual_optimal_family N hN

/-- The simpler large-N theorem presented in the accompanying paper.
This uses the earlier structural proof directly, independently of the
refined arithmetic certificates used for the smaller threshold above. -/
theorem paper_exact_value (N : ℕ) (hN : 2^49≤N) : Value N=B N :=
  GlobalUpper53.actual_value_eq_B N hN

#check @lower_bound
#check @upper_bound
#check @exact_value
#check @optimal_family
#check @paper_exact_value
#print axioms lower_bound
#print axioms upper_bound
#print axioms exact_value
#print axioms optimal_family
#print axioms paper_exact_value
end
end JSP233.PublicResults
