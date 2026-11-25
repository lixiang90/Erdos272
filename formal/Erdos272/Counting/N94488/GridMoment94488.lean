module

public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.GridMoment94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Cost (p : ℕ × ℕ) : ℝ := (p.1 : ℝ)+p.2+1
def Moment (D : Finset (ℕ × ℕ)) : ℝ := ∑ p ∈ D, Cost p
def Triangle (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).biUnion (fun k => Finset.antidiagonal k)

theorem mem_triangle {p : ℕ × ℕ} {m : ℕ} :
    p ∈ Triangle m ↔ p.1+p.2 < m := by
  simp only [Triangle, Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  constructor
  · rintro ⟨k, hk, he⟩
    omega
  · intro hp
    exact ⟨p.1+p.2, hp, rfl⟩

theorem triangle_sum (m : ℕ) (x : ℝ) :
    (∑ p ∈ Triangle m, (x-Cost p)) =
      ∑ k ∈ Finset.range m, ((k : ℝ)+1)*(x-((k : ℝ)+1)) := by
  have hd : Set.PairwiseDisjoint (↑(Finset.range m) : Set ℕ)
      (fun k => (Finset.antidiagonal k : Finset (ℕ × ℕ))) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have h₁ := Finset.mem_antidiagonal.mp hpi
    have h₂ := Finset.mem_antidiagonal.mp hpj
    exact hij (by omega)
  rw [Triangle, Finset.sum_biUnion hd]
  apply Finset.sum_congr rfl
  intro k hk
  have hc : ∀ p ∈ (Finset.antidiagonal k : Finset (ℕ × ℕ)), Cost p = (k : ℝ)+1 := by
    intro p hp
    have he := Finset.mem_antidiagonal.mp hp
    dsimp only [Cost]
    exact_mod_cast (show p.1+p.2+1=k+1 by omega)
  calc
    _ = ∑ _p ∈ (Finset.antidiagonal k : Finset (ℕ × ℕ)), (x-((k : ℝ)+1)) := by
      exact Finset.sum_congr rfl (fun p hp => by rw [hc p hp])
    _ = _ := by simp; ring

theorem triangle_formula (m : ℕ) (x : ℝ) :
    (∑ p ∈ Triangle m, (x-Cost p)) =
      x*(m : ℝ)*((m : ℝ)+1)/2-(m : ℝ)*((m : ℝ)+1)*(2*(m : ℝ)+1)/6 := by
  rw [triangle_sum]
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem triangle_cubic {m : ℕ} {x : ℝ} (hm : (m : ℝ) ≤ x) :
    (∑ p ∈ Triangle m, (x-Cost p)) ≤ x^3/6 := by
  rw [triangle_formula]
  have hp := mul_nonneg (Nat.cast_nonneg (α := ℝ) m) (sq_nonneg (x-m-1/2))
  have hc := pow_nonneg (sub_nonneg.mpr hm) 3
  nlinarith only [hp, hc, Nat.cast_nonneg (α := ℝ) m]

theorem excess_bound {D : Finset (ℕ × ℕ)} {x : ℝ} {m : ℕ}
    (hm : (m : ℝ) ≤ x) (hx : x < (m : ℝ)+1) :
    (∑ p ∈ D, (x-Cost p)) ≤ ∑ p ∈ Triangle m, (x-Cost p) := by
  have hpoint : ∀ p ∈ D,
      x-Cost p ≤ if p ∈ Triangle m then x-Cost p else 0 := by
    intro p hp
    by_cases ht : p ∈ Triangle m
    · simp only [if_pos ht, le_refl]
    · have hn : m ≤ p.1+p.2 := by have hh := mem_triangle.not.mp ht; omega
      have hr : (m : ℝ)+1 ≤ Cost p := by
        dsimp only [Cost]
        exact_mod_cast (show m+1 ≤ p.1+p.2+1 by omega)
      simp only [if_neg ht]
      linarith only [hr, hx]
  have hs := Finset.sum_le_sum hpoint
  have he : D.filter (fun p => p ∈ Triangle m) = D ∩ Triangle m := by ext p; simp
  rw [← Finset.sum_filter, he] at hs
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
  intro p hp hnot
  have hn : p.1+p.2+1 ≤ m := by have hh := mem_triangle.mp hp; omega
  have hr : Cost p ≤ m := by dsimp only [Cost]; exact_mod_cast hn
  linarith only [hm, hr]

theorem grid_moment (D : Finset (ℕ × ℕ)) {x : ℝ} (hx : 0 ≤ x) :
    x*(D.card : ℝ)-x^3/6 ≤ Moment D := by
  let m := ⌊x⌋₊
  have hm : (m : ℝ) ≤ x := Nat.floor_le hx
  have hupper : x < (m : ℝ)+1 := Nat.lt_floor_add_one x
  have hb := (excess_bound (D := D) hm hupper).trans (triangle_cubic hm)
  have he : (∑ p ∈ D, (x-Cost p)) = x*(D.card : ℝ)-Moment D := by
    rw [Finset.sum_sub_distrib]
    simp [Moment, mul_comm]
  rw [he] at hb
  linarith only [hb]

#print axioms mem_triangle
#print axioms triangle_sum
#print axioms triangle_formula
#print axioms triangle_cubic
#print axioms excess_bound
#print axioms grid_moment
end
end JSP233.GridMoment94488
