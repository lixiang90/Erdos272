module

public import Erdos272.Counting.N86412.APSplit86412
public import Erdos272.Geometry.N86412.APReflection86412

@[expose] public section

namespace JSP233.APReconstruction86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412 APReflection86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem neg_initial_complement {S A : Finset ℤ} (hA : IsInitial S A) :
    IsInitial (NegSet S) (NegSet (S\A)) := by
  constructor
  · intro x hx
    exact mem_negset.mpr (Finset.mem_sdiff.mp (mem_negset.mp hx)).1
  · intro x hx y hy hxy
    have hxS := mem_negset.mp hx
    obtain ⟨hyS, hyA⟩ := Finset.mem_sdiff.mp (mem_negset.mp hy)
    apply mem_negset.mpr
    refine Finset.mem_sdiff.mpr ⟨hxS, ?_⟩
    intro hxA
    exact hyA (hA.2 (-y) hyS (-x) hxA (by omega))

theorem neg_complement {S A : Finset ℤ} (hA : A⊆S) :
    NegSet S\NegSet (S\A)=NegSet A := by
  ext x
  simp only [Finset.mem_sdiff, mem_negset]
  constructor
  · rintro ⟨hxS, hnot⟩
    by_contra hxA
    exact hnot ⟨hxS, hxA⟩
  · intro hxA
    exact ⟨hA hxA, fun hh => hh.2 hxA⟩

theorem tail_pair_start {S T : Finset ℤ} {q : ℕ} (hq : 2≤q)
    (hT : IsInitial S T) (hb : BalancedTail S.card q (S\T).card)
    (heq : (Codes S q).card=intervalMultiplicity S.card q)
    {x y : ℤ} (hx : x∈S\T) (hy : y∈S\T) (hxy : x<y) :
    y-(q : ℤ)*(y-x)∈S := by
  have hs := split_saturation hq hT hb heq
  have hp := hs.2.1 (x,y) (mem_orderedPairs.mpr ⟨hx, hy, hxy⟩)
  have hh := (mem_codes.mp hp).2.2.2 q le_rfl
  simpa only [Point] using hh

theorem initial_pair_end {S A : Finset ℤ} {q : ℕ} (hq : 2≤q)
    (hA : IsInitial S A) (hb : BalancedTail S.card q A.card)
    (heq : (Codes S q).card=intervalMultiplicity S.card q)
    {x y : ℤ} (hx : x∈A) (hy : y∈A) (hxy : x<y) :
    x+(q : ℤ)*(y-x)∈S := by
  have hcomp := neg_complement hA.1
  have hcompCard : (NegSet S\NegSet (S\A)).card=A.card := by
    rw [hcomp, card_negset]
  have hbN : BalancedTail (NegSet S).card q (NegSet S\NegSet (S\A)).card := by
    simpa only [card_negset, hcompCard] using hb
  have heN := optimal_reflection (by omega : 1≤q) heq
  have hs := split_saturation hq (neg_initial_complement hA) hbN heN
  have hp : (-y,-x)∈OrderedPairs (NegSet S\NegSet (S\A)) := by
    rw [hcomp]
    apply mem_orderedPairs.mpr
    refine ⟨?_, ?_, by omega⟩
    · apply mem_negset.mpr
      simpa only [neg_neg] using hy
    · apply mem_negset.mpr
      simpa only [neg_neg] using hx
  have hc := hs.2.1 (-y,-x) hp
  have hh := mem_negset.mp ((mem_codes.mp hc).2.2.2 q le_rfl)
  convert hh using 1 <;> dsimp only [Point] <;> ring

#print axioms neg_initial_complement
#print axioms neg_complement
#print axioms tail_pair_start
#print axioms initial_pair_end
end
end JSP233.APReconstruction86412
