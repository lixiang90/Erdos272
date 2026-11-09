module

public import Erdos272.Geometry.Reflect37
public import Erdos272.Global.DenseDeletion40

@[expose] public section

/-! Reflection of the complete physical family, including native deletion. -/
namespace JSP233.FamilyReflect43
open StarCompletion LongTerminal35 TraceWitnessCodes36
open scoped Classical
noncomputable section

def Point (N : ℕ) (x : ℤ) : ℤ := (N:ℤ)+1-x
def Set (N : ℕ) (S : Finset ℤ) : Finset ℤ := S.image (Point N)
def Family (N : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) := F.image (Set N)

theorem point_involutive (N : ℕ) (x : ℤ) : Point N (Point N x)=x := by
  dsimp [Point]
  omega

theorem point_injective (N : ℕ) : Function.Injective (Point N) := by
  intro x y he
  have hh := congrArg (Point N) he
  simpa only [point_involutive] using hh

theorem mem_set (N : ℕ) (S : Finset ℤ) (x : ℤ) : x∈Set N S ↔ Point N x∈S := by
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    rw [←he,point_involutive]
    exact hy
  · intro hx
    exact Finset.mem_image.mpr ⟨Point N x,hx,point_involutive N x⟩

theorem set_involutive (N : ℕ) (S : Finset ℤ) : Set N (Set N S)=S := by
  ext x
  simp only [mem_set,point_involutive]

theorem set_injective (N : ℕ) : Function.Injective (Set N) := by
  intro S T he
  have hh := congrArg (Set N) he
  simpa only [set_involutive] using hh

theorem set_card (N : ℕ) (S : Finset ℤ) : (Set N S).card=S.card :=
  Finset.card_image_of_injective _ (point_injective N)

theorem set_subset (N : ℕ) {S T : Finset ℤ} : Set N S⊆Set N T ↔ S⊆T := by
  constructor
  · intro hh x hx
    have h := hh ((mem_set N S (Point N x)).mpr (by simpa only [point_involutive] using hx))
    simpa only [mem_set,point_involutive] using h
  · intro hh x hx
    exact (mem_set N T x).mpr (hh ((mem_set N S x).mp hx))

theorem set_inter (N : ℕ) (S T : Finset ℤ) : Set N (S∩T)=Set N S∩Set N T := by
  ext x
  simp only [mem_set,Finset.mem_inter]

theorem set_sdiff (N : ℕ) (S T : Finset ℤ) : Set N (S\T)=Set N S\Set N T := by
  ext x
  simp only [mem_set,Finset.mem_sdiff]

theorem set_insert (N : ℕ) (c : ℤ) (Q : Finset ℤ) :
    Set N (insert c Q)=insert (Point N c) (Set N Q) := by
  exact Finset.image_insert _ _ _

theorem point_ground (N : ℕ) (x : ℤ) : Point N x∈Ground N ↔ x∈Ground N := by
  simp only [mem_ground]
  dsimp [Point]
  omega

theorem set_ground (N : ℕ) : Set N (Ground N)=Ground N := by
  ext x
  rw [mem_set,point_ground]

theorem set_eq_shift_reflect (N : ℕ) (S : Finset ℤ) :
    Set N S=PrivatePairExistence.Shift (Reflect37.Reflect S) (-((N:ℤ)+1)) := by
  ext x
  rw [mem_set,PrivatePairExistence.mem_shift_iff,Reflect37.mem_reflect]
  have he : Point N x=-(x+ -((N:ℤ)+1)) := by dsimp [Point]; ring
  rw [he]

theorem set_isAP_iff (N : ℕ) (S : Finset ℤ) : IsAP (Set N S) ↔ IsAP S := by
  rw [set_eq_shift_reflect,PrivatePairExistence.isAP_shift_iff,Reflect37.reflect_isAP_iff]

theorem set_intrinsic_iff (N : ℕ) (c : ℤ) (S Q : Finset ℤ) :
    IntrinsicPair (Point N c) (Set N S) (Set N Q) ↔ IntrinsicPair c S Q := by
  have forward : ∀ (c : ℤ) (S Q : Finset ℤ), IntrinsicPair c S Q →
      IntrinsicPair (Point N c) (Set N S) (Set N Q) := by
    intro c S Q hQ
    refine ⟨by simpa only [set_card] using hQ.1,?_,(set_subset N).mpr hQ.2.2.1,?_⟩
    · simpa only [mem_set,point_involutive] using hQ.2.1
    · rintro ⟨T,hAP,hcode,hsub⟩
      apply hQ.2.2.2
      refine ⟨Set N T,(set_isAP_iff N T).mpr hAP,?_,?_⟩
      · have hh := (set_subset N).mpr hcode
        simpa only [set_insert,point_involutive,set_involutive] using hh
      · have hh := (set_subset N).mpr hsub
        simpa only [set_involutive] using hh
  constructor
  · intro hh
    simpa only [point_involutive,set_involutive] using forward _ _ _ hh
  · exact forward _ _ _

theorem structural_set (N : ℕ) (c : ℤ) (S : Finset ℤ) :
    StructuralPairs (Point N c) (Set N S)=(StructuralPairs c S).image (Set N) := by
  ext Q
  constructor
  · intro hQ
    have hh := (set_intrinsic_iff N c S (Set N Q)).mp (by
      simpa only [set_involutive] using structural_pair_mem.mp hQ)
    exact Finset.mem_image.mpr ⟨Set N Q,structural_pair_mem.mpr hh,set_involutive N Q⟩
  · intro hQ
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hQ
    exact structural_pair_mem.mpr ((set_intrinsic_iff N c S T).mpr (structural_pair_mem.mp hT))

theorem structural_set_card (N : ℕ) (c : ℤ) (S : Finset ℤ) :
    (StructuralPairs (Point N c) (Set N S)).card=(StructuralPairs c S).card := by
  rw [structural_set,Finset.card_image_of_injective _ (set_injective N)]

theorem mem_family (N : ℕ) (F : Finset (Finset ℤ)) (S : Finset ℤ) :
    S∈Family N F ↔ Set N S∈F := by
  constructor
  · intro hS
    obtain ⟨T,hT,he⟩ := Finset.mem_image.mp hS
    rw [←he,set_involutive]
    exact hT
  · intro hS
    exact Finset.mem_image.mpr ⟨Set N S,hS,set_involutive N S⟩

theorem family_involutive (N : ℕ) (F : Finset (Finset ℤ)) : Family N (Family N F)=F := by
  ext S
  simp only [mem_family,set_involutive]

theorem family_card (N : ℕ) (F : Finset (Finset ℤ)) : (Family N F).card=F.card :=
  Finset.card_image_of_injective _ (set_injective N)

theorem family_sdiff (N : ℕ) (F H : Finset (Finset ℤ)) :
    Family N (F\H)=Family N F\Family N H := by
  ext S
  simp only [mem_family,Finset.mem_sdiff]

theorem family_legal_iff (N : ℕ) (F : Finset (Finset ℤ)) :
    Legal (Ground N) (Family N F) ↔ Legal (Ground N) F := by
  have forward : ∀ H : Finset (Finset ℤ), Legal (Ground N) H → Legal (Ground N) (Family N H) := by
    intro H hH
    constructor
    · intro S hS
      obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
      rw [←set_ground N]
      exact (set_subset N).mpr (hH.1 T hT)
    · intro S hS T hT hne
      obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨B,hB,rfl⟩ := Finset.mem_image.mp hT
      rw [←set_inter]
      exact (set_isAP_iff N (A∩B)).mpr (hH.2 A hA B hB (fun he=>hne (congrArg (Set N) he)))
  constructor
  · intro h
    simpa only [family_involutive] using forward _ h
  · exact forward F

theorem family_rooted_iff (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Rooted (Family N F) (Point N c) ↔ Rooted F c := by
  constructor
  · intro h S hS
    have hh := h (Set N S) (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
    simpa only [mem_set,point_involutive] using hh
  · intro h S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    exact (mem_set N T (Point N c)).mpr (by simpa only [point_involutive] using h T hT)

theorem family_allAP_iff (N : ℕ) (F : Finset (Finset ℤ)) :
    (∀ S∈Family N F,IsAP S) ↔ ∀ S∈F,IsAP S := by
  constructor
  · intro h S hS
    exact (set_isAP_iff N S).mp (h _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩))
  · intro h S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    exact (set_isAP_iff N T).mpr (h T hT)

theorem family_all_crooked_iff (N : ℕ) (F : Finset (Finset ℤ)) :
    (∀ S∈Family N F,¬IsAP S) ↔ ∀ S∈F,¬IsAP S := by
  constructor
  · intro h S hS
    simpa only [set_isAP_iff] using h _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
  · intro h S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    simpa only [set_isAP_iff] using h T hT

theorem family_crooked_root_iff (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    (∀ S∈Family N F,¬IsAP S → Point N c∈S) ↔ (∀ S∈F,¬IsAP S → c∈S) := by
  constructor
  · intro h S hS hbad
    have hh := h _ (Finset.mem_image.mpr ⟨S,hS,rfl⟩) (by simpa only [set_isAP_iff] using hbad)
    simpa only [mem_set,point_involutive] using hh
  · intro h S hS hbad
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    apply (mem_set N T (Point N c)).mpr
    simpa only [point_involutive] using h T hT (by simpa only [set_isAP_iff] using hbad)

theorem family_rootPart (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Family N (RootPart F c)=RootPart (Family N F) (Point N c) := by
  ext S
  simp only [mem_family,RootPart,Finset.mem_filter,mem_set]

theorem family_avoiders (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    Family N (Avoiders F c)=Avoiders (Family N F) (Point N c) := by
  ext S
  simp only [mem_family,Avoiders,Finset.mem_filter,mem_set]

theorem family_deleted (N r : ℕ) (F : Finset (Finset ℤ)) :
    Family N (DenseDeletion40.Deleted N r F)=DenseDeletion40.Deleted N r (Family N F) := by
  ext S
  simp only [mem_family,DenseDeletion40.Deleted,Finset.mem_filter,set_isAP_iff,set_card]

theorem family_retained (N r : ℕ) (F : Finset (Finset ℤ)) :
    Family N (DenseDeletion40.Retained N r F)=DenseDeletion40.Retained N r (Family N F) := by
  rw [DenseDeletion40.Retained,family_sdiff,family_deleted]
  rfl

theorem rootPart_card (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    (RootPart (Family N F) (Point N c)).card=(RootPart F c).card := by
  rw [←family_rootPart,family_card]

theorem avoiders_card (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ) :
    (Avoiders (Family N F) (Point N c)).card=(Avoiders F c).card := by
  rw [←family_avoiders,family_card]

theorem deleted_card (N r : ℕ) (F : Finset (Finset ℤ)) :
    (DenseDeletion40.Deleted N r (Family N F)).card=(DenseDeletion40.Deleted N r F).card := by
  rw [←family_deleted,family_card]

theorem retained_card (N r : ℕ) (F : Finset (Finset ℤ)) :
    (DenseDeletion40.Retained N r (Family N F)).card=(DenseDeletion40.Retained N r F).card := by
  rw [←family_retained,family_card]

theorem actual_left_avoider_to_right {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    {P : Finset ℤ} (hP : P∈F) (hcP : c∉P) (hleft : ∀ x∈P,x<c) :
    Set N P∈Avoiders (Family N F) (Point N c) ∧ ∀ x∈Set N P,Point N c<x := by
  constructor
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨P,hP,rfl⟩,?_⟩
    simpa only [mem_set,point_involutive] using hcP
  · intro x hx
    have hh := hleft (Point N x) ((mem_set N P x).mp hx)
    dsimp [Point] at hh ⊢
    omega

theorem actual_one_sided_right_orientation (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hlegal : Legal (Ground N) F) (hc : c∈Ground N)
    (hroot : ∀ S∈F,¬IsAP S → c∈S)
    (hcase : Rooted F c ∨ ∃ P∈F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)) :
    ∃ H : Finset (Finset ℤ), (H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      ∃ d∈Ground N,(∀ S∈H,¬IsAP S → d∈S) ∧
        (Rooted H d ∨ ∃ P∈Avoiders H d,∀ x∈P,d<x) := by
  rcases hcase with hcommon | ⟨P,hP,hcP,hleft|hright⟩
  · exact ⟨F,Or.inl rfl,hlegal,rfl,c,hc,hroot,Or.inl hcommon⟩
  · refine ⟨Family N F,Or.inr rfl,(family_legal_iff N F).mpr hlegal,family_card N F,
      Point N c,(point_ground N c).mpr hc,(family_crooked_root_iff N F c).mpr hroot,Or.inr ?_⟩
    have hh := actual_left_avoider_to_right (N:=N) hP hcP hleft
    exact ⟨Set N P,hh.1,hh.2⟩
  · refine ⟨F,Or.inl rfl,hlegal,rfl,c,hc,hroot,Or.inr ?_⟩
    exact ⟨P,Finset.mem_filter.mpr ⟨hP,hcP⟩,hright⟩

theorem actual_retained_right_orientation (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hlegal : Legal (Ground N) F) (hc : c∈Ground N)
    (hroot : ∀ S∈DenseDeletion40.Retained N r F,¬IsAP S → c∈S)
    (hcase : Rooted (DenseDeletion40.Retained N r F) c ∨
      ∃ P∈DenseDeletion40.Retained N r F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)) :
    ∃ H : Finset (Finset ℤ), (H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (DenseDeletion40.Deleted N r H).card=(DenseDeletion40.Deleted N r F).card ∧
      (DenseDeletion40.Retained N r H).card=(DenseDeletion40.Retained N r F).card ∧
      ∃ d∈Ground N,(∀ S∈DenseDeletion40.Retained N r H,¬IsAP S → d∈S) ∧
        (Rooted (DenseDeletion40.Retained N r H) d ∨
          ∃ P∈Avoiders (DenseDeletion40.Retained N r H) d,∀ x∈P,d<x) := by
  obtain ⟨G,hG,hLG,hcard,d,hd,hrootG,hcaseG⟩ := actual_one_sided_right_orientation N
    (DenseDeletion40.Retained N r F) c (DenseDeletion40.actual_retained_legal hlegal) hc hroot hcase
  rcases hG with he | he
  · subst G
    exact ⟨F,Or.inl rfl,hlegal,rfl,rfl,rfl,d,hd,hrootG,hcaseG⟩
  · refine ⟨Family N F,Or.inr rfl,(family_legal_iff N F).mpr hlegal,family_card N F,?_,?_,d,hd,?_,?_⟩
    · rw [←family_deleted,family_card]
    · rw [←family_retained,family_card]
    · simpa only [he,family_retained] using hrootG
    · simpa only [he,family_retained] using hcaseG

#print axioms point_involutive
#print axioms point_injective
#print axioms mem_set
#print axioms set_involutive
#print axioms set_injective
#print axioms set_card
#print axioms set_subset
#print axioms set_inter
#print axioms set_sdiff
#print axioms set_insert
#print axioms point_ground
#print axioms set_ground
#print axioms set_eq_shift_reflect
#print axioms set_isAP_iff
#print axioms set_intrinsic_iff
#print axioms structural_set
#print axioms structural_set_card
#print axioms mem_family
#print axioms family_involutive
#print axioms family_card
#print axioms family_sdiff
#print axioms family_legal_iff
#print axioms family_rooted_iff
#print axioms family_allAP_iff
#print axioms family_all_crooked_iff
#print axioms family_crooked_root_iff
#print axioms family_rootPart
#print axioms family_avoiders
#print axioms family_deleted
#print axioms family_retained
#print axioms rootPart_card
#print axioms avoiders_card
#print axioms deleted_card
#print axioms retained_card
#print axioms actual_left_avoider_to_right
#print axioms actual_one_sided_right_orientation
#print axioms actual_retained_right_orientation
end
end JSP233.FamilyReflect43
