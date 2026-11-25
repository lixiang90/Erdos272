module

public import Erdos272.Counting.N86412.APThreeShape86412
public import Erdos272.Counting.N86412.APRecursiveFrame86412

@[expose] public section

namespace JSP233.APOptimalShape86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412
open APSegments86412 APBlockArithmetic86412 APRecursiveFrame86412
open APThreeShape86412 GapShape86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem optimal_shape (q : ℕ) (S : Finset ℤ) (hq : 3≤q) (hqs : q<S.card)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) :
    ∃ d : ℤ, 0<d ∧ GapShape S d := by
  induction q using Nat.strong_induction_on generalizing S with
  | h q ih =>
    by_cases hq3 : q=3
    · subst q
      exact optimal_three_shape (by omega) heq
    have hq4 : 4≤q := by omega
    obtain ⟨T, A, hT, hA, hAc, hCc, hBc, hTc, hUc⟩ := exists_recursive_frame hq4 hqs
    have harith := recursive_end_cuts hq4 (by omega : q+1≤S.card)
    have hbA : BalancedTail S.card q A.card := by
      simpa only [hAc] using harith.2.2.1
    have hbC : BalancedTail S.card q (S\T).card := by
      simpa only [hCc] using harith.2.2.2.1
    have hoptT := (split_saturation (by omega : 2≤q) hT hbC heq).1
    have hoptU := suffix_optimal (by omega : 2≤q) (initial_trans hT hA) hbA heq
    obtain ⟨d₁, hd₁, hs₁⟩ := ih (q-1) (by omega) T (by omega) (by omega) hoptT
    obtain ⟨d₂, hd₂, hs₂⟩ := ih (q-1) (by omega) (S\A) (by omega) (by omega) hoptU
    have hane : A.Nonempty := Finset.card_pos.mp (by omega)
    have hcne : (S\T).Nonempty := Finset.card_pos.mp (by omega)
    have hglue := glue hT hA hane hcne hBc hs₁ hs₂ hd₁ hd₂
    exact ⟨d₁, hd₁, hglue.2⟩

#print axioms optimal_shape
end
end JSP233.APOptimalShape86412
