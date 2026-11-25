module

public import Erdos272.Counting.N88404.InclusionExclusion88404

@[expose] public section

namespace JSP233.SieveBound88404
open InclusionExclusion88404
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem error_product_sum {ι : Type*} (J : Finset ι) (u : ι→ℝ) :
    (∑K∈J.powerset, (1+(-1 : ℝ)^K.card/2)*(∏j∈K, u j))=
      (∏j∈J, (1+u j))+(1/2 : ℝ)*(∏j∈J, (1-u j)) := by
  calc
    _ = (∑K∈J.powerset, ∏j∈K, u j)+
        (1/2 : ℝ)*(∑K∈J.powerset, (-1 : ℝ)^K.card*(∏j∈K, u j)) := by
      rw [Finset.mul_sum, ←Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun K _ => by ring)
    _ = _ := by rw [←Finset.prod_one_add, signed_product_sum]

theorem sieve_lower {α ι : Type*} [DecidableEq α] [DecidableEq ι]
    (R : Finset α) (P : ι→α→Prop) (J : Finset ι) (u v : ι→ℝ) (C : ℝ)
    (hu : ∀j∈J, 0≤u j)
    (hbounds : ∀K⊆J, K.Nonempty →
      (R.card : ℝ)*(∏j∈K, v j)-(3/2 : ℝ)*C*(∏j∈K, u j) ≤ (Intersect R P K).card ∧
      ((Intersect R P K).card : ℝ) ≤
        (R.card : ℝ)*(∏j∈K, v j)+(1/2 : ℝ)*C*(∏j∈K, u j)) :
    (R.card : ℝ)*(∏j∈J, (1-v j))-
      C*((∏j∈J, (1+u j))+(1/2 : ℝ)*(∏j∈J, (1-u j))-3/2)
        ≤ (Avoid R P J).card := by
  have hterm : ∀K∈J.powerset,
      (-1 : ℝ)^K.card*((R.card : ℝ)*(∏j∈K, v j))-
        C*(1+(-1 : ℝ)^K.card/2)*(∏j∈K, u j)+
        (if K=∅ then (3/2 : ℝ)*C else 0) ≤
      (-1 : ℝ)^K.card*((Intersect R P K).card : ℝ) := by
    intro K hK
    by_cases he : K=∅
    · subst K
      simp [intersect_empty] <;> linarith
    · have h := hbounds K (Finset.mem_powerset.mp hK) (Finset.nonempty_iff_ne_empty.mpr he)
      rcases neg_one_pow_eq_or ℝ K.card with hs | hs
      · rw [hs, if_neg he]
        nlinarith only [h.1]
      · rw [hs, if_neg he]
        nlinarith only [h.2]
  have hcentre :
      (∑K∈J.powerset, (-1 : ℝ)^K.card*((R.card : ℝ)*(∏j∈K, v j)))=
        (R.card : ℝ)*(∏j∈J, (1-v j)) := by
    calc
      _ = (R.card : ℝ)*(∑K∈J.powerset, (-1 : ℝ)^K.card*(∏j∈K, v j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun K _ => by ring)
      _ = _ := by rw [signed_product_sum]
  have herror :
      (∑K∈J.powerset, C*(1+(-1 : ℝ)^K.card/2)*(∏j∈K, u j))=
        C*((∏j∈J, (1+u j))+(1/2 : ℝ)*(∏j∈J, (1-u j))) := by
    calc
      _ = C*(∑K∈J.powerset, (1+(-1 : ℝ)^K.card/2)*(∏j∈K, u j)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun K _ => by ring)
      _ = _ := by rw [error_product_sum]
  have hcorrection :
      (∑K∈J.powerset, if K=∅ then (3/2 : ℝ)*C else 0)=(3/2 : ℝ)*C := by simp
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hcentre, herror, hcorrection,
    ←card_avoid_formula R P J] at hsum
  nlinarith only [hsum]

#print axioms error_product_sum
#print axioms sieve_lower
end
end JSP233.SieveBound88404
