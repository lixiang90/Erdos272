import Erdos272.Resources.ResidualWeights208

namespace JSP233.ResidualAggregate208
open ResidualWeights208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

def Price (e : ℕ) (A : ℕ → ℝ) : ℝ :=
  A e/((e-1 : ℕ) : ℝ)+∑ b ∈ Finset.Ico 2 e, A b/((b : ℝ)*(b-1))

theorem coefficient_sum {e : ℕ} (he : 2 ≤ e) :
    1/((e-1 : ℕ) : ℝ)+∑ b ∈ Finset.Ico 2 e, 1/((b : ℝ)*(b-1))=1 := by
  have hi := inverse_cumulative (f := 1) (e := e) (by omega) (by omega)
  norm_num only [Nat.cast_one,div_one] at hi
  have hs : (∑ b ∈ Finset.Ico 2 e, if 1 < b then 1/((b : ℝ)*(b-1)) else 0)=
      ∑ b ∈ Finset.Ico 2 e, 1/((b : ℝ)*(b-1)) := by
    apply Finset.sum_congr rfl
    intro b hb
    rw [if_pos (by have := (Finset.mem_Ico.mp hb).1; omega)]
  rw [hs] at hi
  exact hi.symm

theorem price_affine (N C : ℝ) (A : ℕ → ℝ) {e : ℕ} (he : 2 ≤ e) :
    Price e (fun b => N*A b+C)=N*Price e A+C := by
  have hc := coefficient_sum he
  unfold Price
  simp_rw [add_div,mul_div_assoc]
  rw [Finset.sum_add_distrib,← Finset.mul_sum]
  have hsum : (∑ b ∈ Finset.Ico 2 e, C/((b : ℝ)*(b-1)))=
      C*∑ b ∈ Finset.Ico 2 e, 1/((b : ℝ)*(b-1)) := by rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b hb; ring
  rw [hsum]
  linear_combination C*hc

theorem actual_quadratic_payment {α β : Type*} [DecidableEq α] [DecidableEq β]
    (F : Finset α) (Ω : Finset β) (piece : α → Finset β) (e : ℕ) (A : ℕ → ℝ) (C : ℝ)
    (he : 2 ≤ e) (hsub : ∀ S ∈ F, piece S ⊆ Ω)
    (hpos : ∀ S ∈ F, 0 < (piece S).card)
    (hsmall : ∀ S ∈ F, (piece S).card < e)
    (hcap : ∀ x ∈ Ω, ∀ b, 2 ≤ b → b ≤ e →
      (Cumulative F piece x b : ℝ) ≤ (Ω.card : ℝ)*A b+C) :
    (F.card : ℝ) ≤ (Ω.card : ℝ)^2*Price e A+(Ω.card : ℝ)*C := by
  have hp := cumulative_source_bound F Ω piece e (fun b => (Ω.card : ℝ)*A b+C)
    he hsub hpos hsmall hcap
  change (F.card : ℝ) ≤ (Ω.card : ℝ)*Price e (fun b => (Ω.card : ℝ)*A b+C) at hp
  rw [price_affine _ _ _ he] at hp
  convert hp using 1 <;> ring

#print axioms coefficient_sum
#print axioms price_affine
#print axioms actual_quadratic_payment
end
end JSP233.ResidualAggregate208
