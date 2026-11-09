module

public import Erdos272.Arithmetic.ResidualAggregate208
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

namespace JSP233.CappedWeights209
open ResidualAggregate208 ResidualWeights208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

def Capped (c : ℕ) (B : ℕ→ℝ) (H : ℝ) (b : ℕ) : ℝ := if b≤c then B b else H

theorem capped_price {c e : ℕ} (hc : 1≤c) (hce : c<e) (B : ℕ→ℝ) (H : ℝ) :
    Price e (Capped c B H)=
      (∑ b∈Finset.Icc 2 c,B b/((b : ℝ)*(b-1)))+H/(c : ℝ) := by
  have he : e-1+1=e := by omega
  have hi := inverse_telescope (by omega : 0<c) (by omega : c≤e-1)
  rw [he] at hi
  have hset : Finset.Ico 2 e=Finset.Ico 2 (c+1)∪Finset.Ico (c+1) e := by
    ext b
    simp only [Finset.mem_Ico,Finset.mem_union]
    omega
  have hdis : Disjoint (Finset.Ico 2 (c+1)) (Finset.Ico (c+1) e) := by
    apply Finset.disjoint_left.mpr
    intro b hb ht
    have := Finset.mem_Ico.mp hb
    have := Finset.mem_Ico.mp ht
    omega
  have hlo : (∑ b∈Finset.Ico 2 (c+1),Capped c B H b/((b : ℝ)*(b-1)))=
      ∑ b∈Finset.Icc 2 c,B b/((b : ℝ)*(b-1)) := by
    have heq : Finset.Ico 2 (c+1)=Finset.Icc 2 c := by ext b; simp only [Finset.mem_Ico,Finset.mem_Icc]; omega
    rw [heq]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Capped,if_pos (Finset.mem_Icc.mp hb).2]
  have hhi : (∑ b∈Finset.Ico (c+1) e,Capped c B H b/((b : ℝ)*(b-1)))=
      H*∑ b∈Finset.Ico (c+1) e,1/((b : ℝ)*(b-1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    rw [Capped,if_neg (by have := (Finset.mem_Ico.mp hb).1; omega : ¬b≤c)]
    ring
  unfold Price
  rw [hset,Finset.sum_union hdis,hlo,hhi,Capped,if_neg (by omega : ¬e≤c)]
  linear_combination -H*hi

theorem actual_capped_payment {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α→Finset β) {c e : ℕ}
    (B : ℕ→ℝ) (H : ℝ) (hc : 1≤c) (hce : c<e)
    (hsub : ∀ S∈F,piece S⊆Ω) (hpos : ∀ S∈F,0<(piece S).card)
    (hsmall : ∀ S∈F,(piece S).card<e)
    (hshort : ∀ x∈Ω,∀b,2≤b → b≤c →
      (Cumulative F piece x b : ℝ)≤(Ω.card : ℝ)*B b)
    (htail : ∀ x∈Ω,∀b,c<b → b≤e →
      (Cumulative F piece x b : ℝ)≤(Ω.card : ℝ)*H) :
    (F.card : ℝ)≤(Ω.card : ℝ)^2*
      ((∑ b∈Finset.Icc 2 c,B b/((b : ℝ)*(b-1)))+H/(c : ℝ)) := by
  have hcap : ∀x∈Ω,∀b,2≤b → b≤e →
      (Cumulative F piece x b : ℝ)≤(Ω.card : ℝ)*Capped c B H b+0 := by
    intro x hx b hb hbe
    rw [add_zero,Capped]
    split_ifs with hbc
    · exact hshort x hx b hb hbc
    · exact htail x hx b (by omega) hbe
  have hh := actual_quadratic_payment F Ω piece e (Capped c B H) 0
    (by omega : 2≤e) hsub hpos hsmall hcap
  rw [capped_price hc hce B H,mul_zero,add_zero] at hh
  exact hh

#print axioms capped_price
#print axioms actual_capped_payment
end
end JSP233.CappedWeights209
