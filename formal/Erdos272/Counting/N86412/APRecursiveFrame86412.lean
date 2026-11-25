module

public import Erdos272.Counting.N86412.APSegments86412
public import Erdos272.Counting.N86412.APBlockArithmetic86412

@[expose] public section

namespace JSP233.APRecursiveFrame86412
open ActualAPCount208 APSegments86412 APBlockArithmetic86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem exists_recursive_frame {S : Finset ℤ} {q : ℕ}
    (hq : 4≤q) (hqs : q<S.card) :
    ∃ T A : Finset ℤ, IsInitial S T ∧ IsInitial T A ∧
      A.card=EndLeft S.card q ∧ (S\T).card=EndRight S.card q ∧
      3≤(T\A).card ∧ q≤T.card ∧ q≤(S\A).card := by
  have harith := recursive_end_cuts hq (by omega : q+1≤S.card)
  obtain ⟨T, hT, hTc⟩ := exists_initial_card S
    (Nat.sub_le S.card (EndRight S.card q))
  obtain ⟨A, hA, hAc⟩ := exists_initial_card T
    (by omega : EndLeft S.card q≤T.card)
  have hCA := Finset.card_sdiff_add_card_eq_card hT.1
  have hBA := Finset.card_sdiff_add_card_eq_card hA.1
  have hUA := Finset.card_sdiff_add_card_eq_card (initial_trans hT hA).1
  have hcN : EndRight S.card q≤S.card := Nat.div_le_self S.card q
  exact ⟨T, A, hT, hA, hAc, by omega, by omega, by omega, by omega⟩

#print axioms exists_recursive_frame
end
end JSP233.APRecursiveFrame86412
