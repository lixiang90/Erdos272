module

public import Erdos272.Geometry.N88404.PhaseCard88404
public import Erdos272.Counting.N20258.ResidueCells20258

@[expose] public section
namespace JSP233.PhaseCells20258
open StarCompletion AffineLine30 OrderedShadow88404 PhaseCard88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Intersecting several physical phase conditions on the affine image of a
closed shadow costs no upper error. The lower fee uses the product modulus. -/
theorem intersection {ι : Type*} [DecidableEq ι] {M d : ℕ} {T : Finset (Finset ℤ)}
    (carrier : T ⊆ (Ground M).powersetCard 3) (closed : Closed T) (hd : 0 < d)
    (J : Finset ι) (m : ι → ℕ) (positive : ∀ j ∈ J, 0 < m j)
    (pair : Set.Pairwise (↑J) (fun i j => Nat.Coprime (m i) (m j)))
    (coprime : ∀ j ∈ J, Nat.Coprime d (m j)) (c : ℤ) (r : ι → ℤ) :
    let q := ∏ j ∈ J, m j
    let I := (T.image (mapSet c (d : ℤ))).filter (fun Q => ∀ j ∈ J, AllPhase (m j) (r j) Q)
    (T.card : ℝ)/(q : ℝ)^3-3*(M : ℝ)^2/(2*(q : ℝ)^2) ≤ I.card ∧
      (I.card : ℝ) ≤ (T.card : ℝ)/(q : ℝ)^3 := by
  refine ⟨(affine_intersection_density carrier closed hd J m positive pair coprime c r).1,?_⟩
  obtain ⟨b,congr⟩ := AffineCRT88404.affine_crt J m positive pair d hd coprime c r
  have qpos : 0 < ∏ j ∈ J, m j := Finset.prod_pos positive
  rw [affine_intersection_card carrier hd J m c r b congr]
  apply (le_div_iff₀ (pow_pos (by exact_mod_cast qpos : (0 : ℝ) < (∏ j ∈ J, m j : ℕ)) 3)).mpr
  exact_mod_cast ResidueCells20258.upper_exact (r := b) qpos carrier closed

#print axioms intersection
end
end JSP233.PhaseCells20258
