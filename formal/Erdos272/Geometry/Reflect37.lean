module

public import Erdos272.Resources.TraceWitnessCodes36

@[expose] public section

/-! Integer reflection preserves actual AP cores and intrinsic witness pairs. -/
namespace JSP233.Reflect37
open StarCompletion LongTerminal35 TraceWitnessCodes36
open scoped Classical
noncomputable section

def Reflect (S : Finset ℤ) : Finset ℤ := S.image (fun x => -x)

theorem mem_reflect (S : Finset ℤ) (x : ℤ) : x∈Reflect S ↔ -x∈S := by
  simp only [Reflect,Finset.mem_image]
  constructor
  · rintro ⟨y,hy,he⟩
    have hh : -x=y := by omega
    simpa only [hh] using hy
  · intro hx
    exact ⟨-x,hx,by simp⟩

theorem reflect_involutive (S : Finset ℤ) : Reflect (Reflect S)=S := by
  ext x
  simp only [mem_reflect,neg_neg]

theorem reflect_injective : Function.Injective Reflect := by
  intro S T h
  have hh := congrArg Reflect h
  simpa only [reflect_involutive] using hh

theorem reflect_card (S : Finset ℤ) : (Reflect S).card=S.card := by
  exact Finset.card_image_of_injective _ neg_injective

theorem reflect_right_card (S : Finset ℤ) (c : ℤ) :
    ((Reflect S).filter (fun x => -c<x)).card=(S.filter (fun x => x<c)).card := by
  have he : (Reflect S).filter (fun x => -c<x)=Reflect (S.filter (fun x => x<c)) := by
    ext x
    simp only [Finset.mem_filter,mem_reflect]
    constructor
    · rintro ⟨hx,hlt⟩
      exact ⟨hx,by omega⟩
    · rintro ⟨hx,hlt⟩
      exact ⟨hx,by omega⟩
  rw [he,reflect_card]

theorem reflect_subset {S T : Finset ℤ} : Reflect S⊆Reflect T ↔ S⊆T := by
  constructor
  · intro h x hx
    have hh := h ((mem_reflect S (-x)).mpr (by simpa using hx))
    simpa only [mem_reflect,neg_neg] using hh
  · intro h x hx
    exact (mem_reflect T x).mpr (h ((mem_reflect S x).mp hx))

theorem reflect_insert (c : ℤ) (Q : Finset ℤ) :
    Reflect (insert c Q)=insert (-c) (Reflect Q) := by
  simp only [Reflect,Finset.image_insert]

theorem reflect_sdiff (S T : Finset ℤ) : Reflect (S\T)=Reflect S\Reflect T := by
  ext x
  simp only [mem_reflect,Finset.mem_sdiff]

theorem reflect_isAP {S : Finset ℤ} (hS : IsAP S) : IsAP (Reflect S) := by
  obtain ⟨d,p,hd,lo,hi,hrep,hp⟩ := hS
  refine ⟨d,-p,hd,-hi,-lo,?_,?_⟩
  · intro x
    rw [mem_reflect,hrep]
    have he : -x-p=-(x-(-p)) := by ring
    rw [he,dvd_neg]
    constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨by omega,by omega,h3⟩
  · apply (mem_reflect S (-p)).mpr
    simpa using hp

theorem reflect_isAP_iff (S : Finset ℤ) : IsAP (Reflect S) ↔ IsAP S := by
  constructor
  · intro h
    simpa only [reflect_involutive] using reflect_isAP h
  · exact reflect_isAP

theorem reflect_intrinsic {c : ℤ} {S Q : Finset ℤ} (hQ : IntrinsicPair c S Q) :
    IntrinsicPair (-c) (Reflect S) (Reflect Q) := by
  refine ⟨by simpa only [reflect_card] using hQ.1,?_,reflect_subset.mpr hQ.2.2.1,?_⟩
  · simpa only [mem_reflect,neg_neg] using hQ.2.1
  · rintro ⟨T,hT,hcode,hTS⟩
    apply hQ.2.2.2
    refine ⟨Reflect T,reflect_isAP hT,?_,?_⟩
    · have hh := reflect_subset.mpr hcode
      simpa only [reflect_insert,neg_neg,reflect_involutive] using hh
    · have hh := reflect_subset.mpr hTS
      simpa only [reflect_involutive] using hh

theorem reflect_intrinsic_iff (c : ℤ) (S Q : Finset ℤ) :
    IntrinsicPair (-c) (Reflect S) (Reflect Q) ↔ IntrinsicPair c S Q := by
  constructor
  · intro h
    simpa only [neg_neg,reflect_involutive] using reflect_intrinsic h
  · exact reflect_intrinsic

theorem structural_reflect (c : ℤ) (S : Finset ℤ) :
    StructuralPairs (-c) (Reflect S)=(StructuralPairs c S).image Reflect := by
  ext Q
  constructor
  · intro hQ
    have hi := reflect_intrinsic (structural_pair_mem.mp hQ)
    have hh : Reflect Q∈StructuralPairs c S := by
      apply structural_pair_mem.mpr
      simpa only [neg_neg,reflect_involutive] using hi
    exact Finset.mem_image.mpr ⟨Reflect Q,hh,reflect_involutive Q⟩
  · intro hQ
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hQ
    exact structural_pair_mem.mpr (reflect_intrinsic (structural_pair_mem.mp hT))

theorem structural_reflect_card (c : ℤ) (S : Finset ℤ) :
    (StructuralPairs (-c) (Reflect S)).card=(StructuralPairs c S).card := by
  rw [structural_reflect,Finset.card_image_of_injective _ reflect_injective]

theorem far_reflect {S : Finset ℤ} {K : ℕ}
    (hfar : ∀ U⊆S,IsAP U → K≤(S\U).card) :
    ∀ U⊆Reflect S,IsAP U → K≤(Reflect S\U).card := by
  intro U hU hAP
  have hUS : Reflect U⊆S := by
    have hh := reflect_subset.mpr hU
    simpa only [reflect_involutive] using hh
  have hh := hfar (Reflect U) hUS (reflect_isAP hAP)
  have he : (Reflect S\U).card=(S\Reflect U).card := by
    have hf := congrArg Finset.card (reflect_sdiff S (Reflect U))
    simpa only [reflect_card,reflect_involutive] using hf.symm
  rw [he]
  exact hh

#print axioms mem_reflect
#print axioms reflect_involutive
#print axioms reflect_injective
#print axioms reflect_card
#print axioms reflect_right_card
#print axioms reflect_subset
#print axioms reflect_insert
#print axioms reflect_sdiff
#print axioms reflect_isAP
#print axioms reflect_isAP_iff
#print axioms reflect_intrinsic
#print axioms reflect_intrinsic_iff
#print axioms structural_reflect
#print axioms structural_reflect_card
#print axioms far_reflect
end
end JSP233.Reflect37
