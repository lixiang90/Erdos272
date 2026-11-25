module

public import Mathlib.Data.Finset.Card
public import Erdos272.Foundation.ProofTactics

@[expose] public section
namespace JSP233.Bonferroni20258
set_option autoImplicit false
variable {α : Type*} [DecidableEq α]

/-- Keep only the points outside every listed set. -/
def remaining : List (Finset α) → Finset α → Finset α
  | [], T => T
  | A::rest, T => remaining rest T \ A

/-- The alternating sum of intersections of at most the given order. -/
def truncated : List (Finset α) → ℕ → Finset α → ℤ
  | [], _, T => T.card
  | _::_, 0, T => T.card
  | A::rest, k+1, T => truncated rest (k+1) T - truncated rest k (T ∩ A)

private theorem intersection (sets : List (Finset α)) (T A : Finset α) :
    remaining sets (T ∩ A) = remaining sets T ∩ A := by
  induction sets with
  | nil => rfl
  | cons B sets ih =>
    ext x
    simp only [remaining,ih,Finset.mem_sdiff,Finset.mem_inter]
    tauto

private theorem zero (sets : List (Finset α)) (T : Finset α) :
    truncated sets 0 T=T.card := by cases sets <;> rfl

/-- Upper, lower, upper, lower at orders zero through three. No assumption
on independence, on the sizes of the intersections, or on the number of sets. -/
theorem alternating (sets : List (Finset α)) (T : Finset α) :
    ((remaining sets T).card : ℤ) ≤ truncated sets 0 T ∧
    truncated sets 1 T ≤ (remaining sets T).card ∧
    ((remaining sets T).card : ℤ) ≤ truncated sets 2 T ∧
    truncated sets 3 T ≤ (remaining sets T).card := by
  induction sets generalizing T with
  | nil => simp [remaining,truncated]
  | cons A sets ih =>
    obtain ⟨z,l,u,t⟩ := ih T
    obtain ⟨zi,li,ui,_⟩ := ih (T ∩ A)
    have partition := Finset.card_sdiff_add_card_inter (remaining sets T) A
    rw [←intersection] at partition
    rw [zero] at z
    change ((remaining sets T \ A).card : ℤ) ≤ T.card ∧
      truncated sets 1 T-truncated sets 0 (T ∩ A) ≤ (remaining sets T \ A).card ∧
      ((remaining sets T \ A).card : ℤ) ≤ truncated sets 2 T-truncated sets 1 (T ∩ A) ∧
      truncated sets 3 T-truncated sets 2 (T ∩ A) ≤ (remaining sets T \ A).card
    omega

theorem third_lower (sets : List (Finset α)) (T : Finset α) :
    truncated sets 3 T ≤ (remaining sets T).card := (alternating sets T).2.2.2

#print axioms third_lower
end JSP233.Bonferroni20258
