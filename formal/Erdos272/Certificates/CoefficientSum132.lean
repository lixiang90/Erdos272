import Erdos272.Arithmetic.ScaleWindow132

namespace JSP233.CoefficientSum132
open PairWindow131 ScaleWindow132

theorem forall₂_append {α β : Type*} {R : α → β → Prop}
    {xs ys : List α} {us vs : List β}
    (h : List.Forall₂ R xs us) (h' : List.Forall₂ R ys vs) :
    List.Forall₂ R (xs ++ ys) (us ++ vs) := by
  induction h with
  | nil => exact h'
  | cons h _ ih => exact .cons h ih

theorem sumCoeff_append (xs ys : List Coeff) :
    sumCoeff (xs ++ ys) = addCoeff (sumCoeff xs) (sumCoeff ys) := by
  induction xs with
  | nil =>
    cases h : sumCoeff ys
    simp [sumCoeff, addCoeff, zeroCoeff, h]
  | cons c cs ih =>
    rw [List.cons_append, sumCoeff, ih]
    simp only [sumCoeff, addCoeff]
    congr 1 <;> exact (add_assoc _ _ _).symm

end JSP233.CoefficientSum132
