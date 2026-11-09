module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Erdos272.Foundation.ProofTactics

@[expose] public section

/-! An exact finite dual certificate for disjoint off-residue classes.
This local lemma concerns complete residue classes, not truncated AP traces.
The passage from actual traces to locally disjoint complete classes remains
a separate obligation; this module is not used in the global bound.
-/
namespace JSP233.OffResidueDensity118
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 20000

def weight (z : ℕ) : ℕ :=
  match Nat.gcd z 360 with
  | 1 => 10 | 2 => 9 | 3 => 6 | 4 => 20
  | 6 => 15 | 10 => 4 | 15 => 26 | 45 => 20
  | _ => 0

def codes : Finset (ℕ × ℕ) :=
  ({2, 3, 4, 5, 6, 8, 9, 10, 12} : Finset ℕ).biUnion
    (fun d => (Finset.range d).erase 0 |>.image (fun r => (d, r)))

def mass (c : ℕ × ℕ) : ℕ :=
  ∑ z ∈ Finset.range 360, if z % c.1 = c.2 then weight z else 0

theorem total_weight : (∑ z ∈ Finset.range 360, weight z) = 2640 := by
  decide

theorem code_mass : ∀ c ∈ codes, 8 * (360 / c.1) ≤ mass c := by
  decide

theorem disjoint_residue_budget (C : Finset (ℕ × ℕ))
    (hC : C ⊆ codes)
    (hdisjoint : ∀ z ∈ Finset.range 360,
      (C.filter (fun c => z % c.1 = c.2)).card ≤ 1) :
    ∑ c ∈ C, 360 / c.1 ≤ 330 := by
  have hsum := Finset.sum_le_sum (fun c hc => code_mass c (hC hc))
  have hlocal : ∀ z ∈ Finset.range 360,
      (∑ c ∈ C, if z % c.1 = c.2 then weight z else 0) ≤ weight z := by
    intro z hz
    classical
    have he : (∑ c ∈ C, if z % c.1 = c.2 then weight z else 0) =
        (C.filter (fun c => z % c.1 = c.2)).card * weight z := by
      rw [← Finset.sum_filter]
      simp
    rw [he]
    have hh := Nat.mul_le_mul_right (weight z) (hdisjoint z hz)
    simpa using hh
  have hb := Finset.sum_le_sum hlocal
  have he : (∑ c ∈ C, mass c) =
      ∑ z ∈ Finset.range 360, ∑ c ∈ C,
        if z % c.1 = c.2 then weight z else 0 := by
    unfold mass
    exact Finset.sum_comm
  rw [← he, total_weight] at hb
  rw [← Finset.mul_sum] at hsum
  omega

#print axioms total_weight
#print axioms code_mass
#print axioms disjoint_residue_budget
end JSP233.OffResidueDensity118
