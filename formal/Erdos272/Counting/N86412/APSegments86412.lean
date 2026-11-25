module

public import Erdos272.Counting.N86412.APReconstruction86412

@[expose] public section

namespace JSP233.APSegments86412
open ActualAPCount208 APInterval208 PureSource208 APBalanced86412 APSplit86412
open APReflection86412 APReconstruction86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem initial_trans {S T A : Finset ℤ} (hT : IsInitial S T) (hA : IsInitial T A) :
    IsInitial S A := by
  refine ⟨hA.1.trans hT.1, ?_⟩
  intro x hx y hy hxy
  exact hA.2 x (hT.2 x hx y (hA.1 hy) hxy) y hy hxy

theorem initial_before {S A : Finset ℤ} (hA : IsInitial S A)
    {x y : ℤ} (hx : x∈A) (hy : y∈S\A) : x<y := by
  by_contra hh
  exact (Finset.mem_sdiff.mp hy).2
    (hA.2 y (Finset.mem_sdiff.mp hy).1 x hx (by omega))

theorem difference_initial {S T A : Finset ℤ} (hT : IsInitial S T)
    (hA : IsInitial T A) : IsInitial (S\A) (T\A) := by
  constructor
  · intro x hx
    obtain ⟨hxT, hxA⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hT.1 hxT, hxA⟩
  · intro x hx y hy hxy
    obtain ⟨hxS, hxA⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hyT, hyA⟩ := Finset.mem_sdiff.mp hy
    exact Finset.mem_sdiff.mpr ⟨hT.2 x hxS y hyT hxy, hxA⟩

theorem difference_complement {S T A : Finset ℤ} (hA : A⊆T) :
    (S\A)\(T\A)=S\T := by
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxS, hxA⟩, hnot⟩
    exact ⟨hxS, fun hxT => hnot ⟨hxT, hxA⟩⟩
  · rintro ⟨hxS, hxT⟩
    exact ⟨⟨hxS, fun hxA => hxT (hA hxA)⟩, fun hh => hxT hh.1⟩

theorem suffix_optimal {S A : Finset ℤ} {q : ℕ} (hq : 2≤q)
    (hA : IsInitial S A) (hb : BalancedTail S.card q A.card)
    (heq : (Codes S q).card=intervalMultiplicity S.card q) :
    (Codes (S\A) (q-1)).card=intervalMultiplicity (S\A).card (q-1) := by
  have hcomp := neg_complement hA.1
  have hcompCard : (NegSet S\NegSet (S\A)).card=A.card := by
    rw [hcomp, card_negset]
  have hbN : BalancedTail (NegSet S).card q (NegSet S\NegSet (S\A)).card := by
    simpa only [card_negset, hcompCard] using hb
  have heN := optimal_reflection (by omega : 1≤q) heq
  have hs := (split_saturation hq (neg_initial_complement hA) hbN heN).1
  simpa only [count_reflection (by omega : 1≤q-1), card_negset] using hs

#print axioms initial_trans
#print axioms initial_before
#print axioms difference_initial
#print axioms difference_complement
#print axioms suffix_optimal
end
end JSP233.APSegments86412
