module

public import Erdos272.Counting.N86412.APSegments86412
public import Erdos272.Geometry.N86412.APGridGeometry86412

@[expose] public section

namespace JSP233.APReflectionFrame86412
open ActualAPCount208 APReflection86412 APReconstruction86412 APSegments86412
open OrderedFinite86412 APGridGeometry86412
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem neg_difference (S A : Finset ℤ) :
    NegSet (S\A)=NegSet S\NegSet A := by
  ext x
  simp only [mem_negset, Finset.mem_sdiff]

theorem middle_complement {S T A : Finset ℤ} (hT : T⊆S) :
    (S\A)\(S\T)=T\A := by
  ext x
  simp only [Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxS, hxA⟩, hnot⟩
    exact ⟨by tauto, hxA⟩
  · rintro ⟨hxT, hxA⟩
    exact ⟨⟨hT hxT, hxA⟩, fun hh => hh.2 hxT⟩

theorem reflected_frame {S T A : Finset ℤ}
    (hT : IsInitial S T) (hA : IsInitial T A) :
    IsInitial (NegSet S) (NegSet (S\A)) ∧
      IsInitial (NegSet (S\A)) (NegSet (S\T)) ∧
      NegSet (S\A)\NegSet (S\T)=NegSet (T\A) := by
  refine ⟨neg_initial_complement (initial_trans hT hA), ?_, ?_⟩
  · have hh := neg_initial_complement (difference_initial hT hA)
    simpa only [difference_complement hA.1] using hh
  · rw [← neg_difference, middle_complement hT.1]

theorem reflected_middle_grid {S T A : Finset ℤ} {a d : ℤ} {b : ℕ}
    (hT : IsInitial S T) (hA : IsInitial T A)
    (hB : T\A=Grid a d b) :
    NegSet (S\A)\NegSet (S\T)=Grid (-a-((b : ℤ)-1)*d) d b := by
  rw [(reflected_frame hT hA).2.2, hB, neg_grid]

#print axioms neg_difference
#print axioms middle_complement
#print axioms reflected_frame
#print axioms reflected_middle_grid
end
end JSP233.APReflectionFrame86412
