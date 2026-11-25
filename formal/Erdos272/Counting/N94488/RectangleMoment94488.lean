module

public import Erdos272.Counting.N94488.GridMoment94488

@[expose] public section

namespace JSP233.RectangleMoment94488
open GridMoment94488
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def Rectangle (A B : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range A).product (Finset.range B)

def Reverse (A B : ℕ) (p : ℕ × ℕ) : ℕ × ℕ := (A-1-p.1, B-1-p.2)

theorem row_sum (a : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, (a+(j : ℝ)+1)) = (n : ℝ)*a+(n : ℝ)*((n : ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

theorem rectangle_sum (A B : ℕ) :
    Moment (Rectangle A B) = (A : ℝ)*B*((A : ℝ)+B)/2 := by
  unfold Moment Rectangle
  rw [Finset.product_eq_sprod, Finset.sum_product]
  simp only [Cost, Prod.fst, Prod.snd]
  induction A with
  | zero => simp
  | succ A ih =>
      rw [Finset.sum_range_succ, ih, row_sum]
      push_cast
      ring

theorem reverse_injective {A B : ℕ} {p q : ℕ × ℕ}
    (hp : p ∈ Rectangle A B) (hq : q ∈ Rectangle A B)
    (he : Reverse A B p = Reverse A B q) : p = q := by
  have hp' := Finset.mem_product.mp hp
  have hq' := Finset.mem_product.mp hq
  have hpA := Finset.mem_range.mp hp'.1
  have hpB := Finset.mem_range.mp hp'.2
  have hqA := Finset.mem_range.mp hq'.1
  have hqB := Finset.mem_range.mp hq'.2
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  dsimp only [Reverse] at hx hy
  apply Prod.ext <;> omega

theorem reverse_cost {A B : ℕ} {p : ℕ × ℕ} (hp : p ∈ Rectangle A B) :
    Cost (Reverse A B p) = (A : ℝ)+B-Cost p := by
  have hp' := Finset.mem_product.mp hp
  have hpA := Finset.mem_range.mp hp'.1
  have hpB := Finset.mem_range.mp hp'.2
  have hx : A-1-p.1+p.1+1 = A := by omega
  have hy : B-1-p.2+p.2+1 = B := by omega
  have hxR : ((A-1-p.1 : ℕ) : ℝ)+p.1+1 = A := by exact_mod_cast hx
  have hyR : ((B-1-p.2 : ℕ) : ℝ)+p.2+1 = B := by exact_mod_cast hy
  dsimp only [Cost, Reverse]
  linarith only [hxR, hyR]

theorem complement_moment {A B : ℕ} {D : Finset (ℕ × ℕ)}
    (hD : D ⊆ Rectangle A B) :
    ∃ E : Finset (ℕ × ℕ), (E.card : ℝ) = (A : ℝ)*B-D.card ∧
      Moment D = (D.card : ℝ)*((A : ℝ)+B)-(A : ℝ)*B*((A : ℝ)+B)/2+Moment E := by
  let C := Rectangle A B \ D
  let E := C.image (Reverse A B)
  have hi : Set.InjOn (Reverse A B) C := by
    intro p hp q hq he
    exact reverse_injective (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hq).1 he
  have hcard : C.card+D.card = A*B := by
    have hc := Finset.card_sdiff_add_card_eq_card hD
    simpa only [C, Rectangle, Finset.product_eq_sprod, Finset.card_product, Finset.card_range] using hc
  have hcardR : (C.card : ℝ)+D.card = (A : ℝ)*B := by exact_mod_cast hcard
  have hEcard : E.card = C.card := Finset.card_image_of_injOn hi
  have hEcardR : (E.card : ℝ) = (A : ℝ)*B-D.card := by
    have he : (E.card : ℝ) = C.card := by exact_mod_cast hEcard
    linarith only [he, hcardR]
  have hmoment : Moment E = (C.card : ℝ)*((A : ℝ)+B)-Moment C := by
    dsimp only [Moment, E]
    rw [Finset.sum_image hi]
    have hh : (∑ p ∈ C, Cost (Reverse A B p)) =
        ∑ p ∈ C, ((A : ℝ)+B-Cost p) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact reverse_cost (Finset.mem_sdiff.mp hp).1
    rw [hh, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hsplit : Moment C+Moment D = Moment (Rectangle A B) := by
    exact Finset.sum_sdiff hD
  rw [rectangle_sum] at hsplit
  have hCcard : (C.card : ℝ) = (A : ℝ)*B-D.card := by linarith only [hcardR]
  rw [hCcard] at hmoment
  refine ⟨E, hEcardR, ?_⟩
  nlinarith only [hmoment, hsplit]

theorem rectangle_moment {A B : ℕ} {D : Finset (ℕ × ℕ)} {x : ℝ}
    (hD : D ⊆ Rectangle A B) (hx : 0 ≤ x) :
    (D.card : ℝ)*((A : ℝ)+B-x)+(A : ℝ)*B*(x-((A : ℝ)+B)/2)-x^3/6 ≤ Moment D := by
  obtain ⟨E, hc, hm⟩ := complement_moment hD
  have hg := grid_moment E hx
  rw [hc] at hg
  nlinarith only [hg, hm]

#print axioms row_sum
#print axioms rectangle_sum
#print axioms reverse_injective
#print axioms reverse_cost
#print axioms complement_moment
#print axioms rectangle_moment
end
end JSP233.RectangleMoment94488
