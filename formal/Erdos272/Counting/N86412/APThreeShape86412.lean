module

public import Erdos272.Counting.N86412.APMiddle86412
public import Erdos272.Counting.N86412.APOneEnd86412
public import Erdos272.Geometry.N86412.APReflectionFrame86412

@[expose] public section

namespace JSP233.APThreeShape86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412
open APReflection86412 APReconstruction86412 APSegments86412 APBlockArithmetic86412
open OrderedFinite86412 APMiddle86412 APOneEnd86412 APReflectionFrame86412 GapShape86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem optimal_three_shape {S : Finset ℤ} (hS : 4≤S.card)
    (heq : (Codes S 3).card=intervalMultiplicity S.card 3) :
    ∃ d : ℤ, 0<d ∧ GapShape S d := by
  obtain ⟨T, A, hT, hA, hAc, hBc, hCc, a, d, hd, hgrid⟩ := three_blocks_grid hS heq
  rcases three_blocks hS with ⟨hsum, hb2, ha1, hc1, haLo, haHi, hcLo, hcHi, hbA, hbC⟩
  have hTc : T.card=Left3 S.card+Middle3 S.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hA.1
    omega
  have hUc : (S\A).card=Middle3 S.card+Right3 S.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (initial_trans hT hA).1
    omega
  have hbA3 : BalancedTail S.card 3 A.card := by simpa only [hAc] using hbA
  have hbC3 : BalancedTail S.card 3 (S\T).card := by simpa only [hCc] using hbC
  have hbAL2 : BalancedTail T.card 2 A.card := by
    rw [hTc, hAc]
    exact (balanced_two_parts (by omega : Left3 S.card≤Middle3 S.card+1)
      (by omega : Middle3 S.card≤Left3 S.card+1)).1
  have hbBL2 : BalancedTail T.card 2 (T\A).card := by
    rw [hTc, hBc]
    exact (balanced_two_parts (by omega : Left3 S.card≤Middle3 S.card+1)
      (by omega : Middle3 S.card≤Left3 S.card+1)).2
  have hoptT : (Codes T 2).card=intervalMultiplicity T.card 2 :=
    (split_saturation (by decide : 2≤3) hT hbC3 heq).1
  have hoptU : (Codes (S\A) 2).card=intervalMultiplicity (S\A).card 2 :=
    suffix_optimal (by decide : 2≤3) (initial_trans hT hA) hbA3 heq
  have hleft : LeftGapShape T d :=
    left_half_shape hT hA hb2 hd (by simpa only [hBc] using hgrid)
      (by omega) hbAL2 hbBL2 hbA3 hoptT heq
  have hframe := reflected_frame hT hA
  have hRgrid := reflected_middle_grid hT hA (by simpa only [hBc] using hgrid)
  have hbAR2 : BalancedTail (NegSet (S\A)).card 2 (NegSet (S\T)).card := by
    rw [card_negset, card_negset, hUc, hCc]
    exact (balanced_two_parts (by omega : Middle3 S.card≤Right3 S.card+1)
      (by omega : Right3 S.card≤Middle3 S.card+1)).2
  have hbBR2 : BalancedTail (NegSet (S\A)).card 2
      (NegSet (S\A)\NegSet (S\T)).card := by
    rw [hframe.2.2, card_negset, card_negset, hUc, hBc]
    exact (balanced_two_parts (by omega : Middle3 S.card≤Right3 S.card+1)
      (by omega : Right3 S.card≤Middle3 S.card+1)).1
  have hbAR3 : BalancedTail (NegSet S).card 3 (NegSet (S\T)).card := by
    simpa only [card_negset] using hbC3
  have hoptR := optimal_reflection (by decide : 1≤2) hoptU
  have hoptS := optimal_reflection (by decide : 1≤3) heq
  have hrightNeg : LeftGapShape (NegSet (S\A)) d :=
    left_half_shape hframe.1 hframe.2.1 hb2 hd hRgrid
      (by simpa only [card_negset, hCc] using hcHi)
      hbAR2 hbBR2 hbAR3 hoptR hoptS
  have hright : RightGapShape (S\A) d := left_reflection hrightNeg
  refine ⟨d, hd, one_sided_glue hT hA ?_ hleft hright⟩
  apply Finset.card_pos.mp
  omega

#print axioms optimal_three_shape
end
end JSP233.APThreeShape86412
