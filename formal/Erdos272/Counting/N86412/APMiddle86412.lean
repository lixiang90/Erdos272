module

public import Erdos272.Counting.N86412.APGaps86412
public import Erdos272.Counting.N86412.APSegments86412
public import Erdos272.Counting.N86412.APBlockArithmetic86412
public import Erdos272.Counting.N86412.OrderedFinite86412

@[expose] public section

namespace JSP233.APMiddle86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412
open APReconstruction86412 APGaps86412 APSegments86412 APBlockArithmetic86412
open OrderedFinite86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem middle_equal_gaps {S T A : Finset ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A)
    (hbC : BalancedTail S.card 3 (S\T).card)
    (hbA : BalancedTail S.card 3 A.card)
    (hbLeft : BalancedTail T.card 2 (T\A).card)
    (hbRight : BalancedTail (S\A).card 2 (T\A).card)
    (heq : (Codes S 3).card=intervalMultiplicity S.card 3)
    {x y z : ℤ} (hx : x∈T\A) (hy : y∈T\A) (hz : z∈T\A)
    (hxy : x<y) (hyz : y<z)
    (hgap1 : ∀ t∈T\A, x<t → t<y → False)
    (hgap2 : ∀ t∈T\A, y<t → t<z → False) : y-x=z-y := by
  have hoptT : (Codes T 2).card=intervalMultiplicity T.card 2 :=
    (split_saturation (by decide : 2≤3) hT hbC heq).1
  have hoptU : (Codes (S\A) 2).card=intervalMultiplicity (S\A).card 2 :=
    suffix_optimal (by decide : 2≤3) (initial_trans hT hA) hbA heq
  have hleft := tail_gap_nondecreasing hA hbLeft hoptT hx hy hz hxy hyz hgap1
  have hright := initial_gap_nonincreasing (difference_initial hT hA) hbRight hoptU
    hx hy hz hxy hyz hgap2
  exact le_antisymm hleft hright

theorem middle_grid {S T A : Finset ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A)
    (hbC : BalancedTail S.card 3 (S\T).card)
    (hbA : BalancedTail S.card 3 A.card)
    (hbLeft : BalancedTail T.card 2 (T\A).card)
    (hbRight : BalancedTail (S\A).card 2 (T\A).card)
    (hB : 2≤(T\A).card)
    (heq : (Codes S 3).card=intervalMultiplicity S.card 3) :
    ∃ a d : ℤ, 0<d ∧ T\A=Grid a d (T\A).card := by
  apply equal_consecutive_gaps hB
  intro x hx y hy z hz hxy hyz hgap1 hgap2
  exact middle_equal_gaps hT hA hbC hbA hbLeft hbRight heq hx hy hz hxy hyz hgap1 hgap2

theorem exists_three_blocks (S : Finset ℤ) (hS : 4≤S.card) :
    ∃ T A : Finset ℤ, IsInitial S T ∧ IsInitial T A ∧
      A.card=Left3 S.card ∧ (T\A).card=Middle3 S.card ∧
      (S\T).card=Right3 S.card := by
  have hsize := three_blocks hS
  obtain ⟨T, hT, hTc⟩ := exists_initial_card S
    (by omega : Left3 S.card+Middle3 S.card≤S.card)
  obtain ⟨A, hA, hAc⟩ := exists_initial_card T
    (by omega : Left3 S.card≤T.card)
  have hBT := Finset.card_sdiff_add_card_eq_card hA.1
  have hCT := Finset.card_sdiff_add_card_eq_card hT.1
  exact ⟨T, A, hT, hA, hAc, by omega, by omega⟩

theorem three_blocks_grid {S : Finset ℤ} (hS : 4≤S.card)
    (heq : (Codes S 3).card=intervalMultiplicity S.card 3) :
    ∃ T A : Finset ℤ, IsInitial S T ∧ IsInitial T A ∧
      A.card=Left3 S.card ∧ (T\A).card=Middle3 S.card ∧
      (S\T).card=Right3 S.card ∧
      ∃ a d : ℤ, 0<d ∧ T\A=Grid a d (Middle3 S.card) := by
  obtain ⟨T, A, hT, hA, hAc, hBc, hCc⟩ := exists_three_blocks S hS
  have hsize := three_blocks hS
  have hTc : T.card=Left3 S.card+Middle3 S.card := by
    have hh := Finset.card_sdiff_add_card_eq_card hA.1
    omega
  have hUc : (S\A).card=Middle3 S.card+Right3 S.card := by
    have hh := Finset.card_sdiff_add_card_eq_card (initial_trans hT hA).1
    omega
  have hleft : BalancedTail T.card 2 (T\A).card := by
    rw [hTc, hBc]
    exact (balanced_two_parts (by omega : Left3 S.card≤Middle3 S.card+1)
      (by omega : Middle3 S.card≤Left3 S.card+1)).2
  have hright : BalancedTail (S\A).card 2 (T\A).card := by
    rw [hUc, hBc]
    exact (balanced_two_parts (by omega : Middle3 S.card≤Right3 S.card+1)
      (by omega : Right3 S.card≤Middle3 S.card+1)).1
  have hbA : BalancedTail S.card 3 A.card := by simpa only [hAc] using hsize.2.2.2.2.2.2.2.2.1
  have hbC : BalancedTail S.card 3 (S\T).card := by simpa only [hCc] using hsize.2.2.2.2.2.2.2.2.2
  obtain ⟨a, d, hd, hg⟩ := middle_grid hT hA hbC hbA hleft hright (by omega) heq
  exact ⟨T, A, hT, hA, hAc, hBc, hCc, a, d, hd, by simpa only [hBc] using hg⟩

#print axioms middle_equal_gaps
#print axioms middle_grid
#print axioms exists_three_blocks
#print axioms three_blocks_grid
end
end JSP233.APMiddle86412
