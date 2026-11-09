module

public import Erdos272.Geometry.FamilyReflect43

@[expose] public section

/-! Extremal physical endpoints chosen from actual avoiding members. -/
namespace JSP233.OutsideEnvelope43
open StarCompletion FamilyReflect43
open scoped Classical
noncomputable section

def First (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.min' h else 0
def Last (S : Finset ℤ) : ℤ := if h : S.Nonempty then S.max' h else 0

theorem first_spec {S : Finset ℤ} (hne : S.Nonempty) :
    First S∈S ∧ ∀ x∈S,First S≤x := by
  simp only [First,dif_pos hne]
  exact ⟨Finset.min'_mem S hne,fun x hx=>Finset.min'_le S x hx⟩

theorem last_spec {S : Finset ℤ} (hne : S.Nonempty) :
    Last S∈S ∧ ∀ x∈S,x≤Last S := by
  simp only [Last,dif_pos hne]
  exact ⟨Finset.max'_mem S hne,fun x hx=>Finset.le_max' S x hx⟩

theorem actual_member_nonempty {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hcard : 2≤F.card) {S : Finset ℤ} (hS : S∈F) : S.Nonempty := by
  have hp : 0<(F.erase S).card := by rw [Finset.card_erase_of_mem hS]; omega
  obtain ⟨T,hT⟩ := Finset.card_pos.mp hp
  obtain ⟨hTS,hTF⟩ := Finset.mem_erase.mp hT
  have hi := hlegal.2 S hS T hTF hTS.symm
  exact (isAP_nonempty hi).mono Finset.inter_subset_left

theorem actual_inter_nonempty {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) {S T : Finset ℤ} (hS : S∈F) (hT : T∈F)
    (hne : S.Nonempty) : (S∩T).Nonempty := by
  by_cases he : S=T
  · subst T
    simpa only [Finset.inter_self] using hne
  · exact isAP_nonempty (hlegal.2 S hS T hT he)

theorem actual_outside_member_envelope {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hlegal : Legal (Ground N) F) (hcard : 2≤F.card)
    (hright : ∃ P∈Avoiders F c,∀ x∈P,c<x) :
    ∃ L R : ℕ, c<(L:ℤ) ∧ L≤R ∧ R≤N ∧
      (∃ P∈Avoiders F c,∀ x∈P,(L:ℤ)≤x) ∧
      (∃ T∈Avoiders F c,∀ x∈T,x≤(R:ℤ)) ∧
      ∀ S∈Avoiders F c,
        (∃ a∈S,a≤(L:ℤ) ∧ ∀ x∈S,a≤x) ∧
        ∃ b∈S,(R:ℤ)≤b ∧ ∀ x∈S,x≤b := by
  let A := Avoiders F c
  have hAF : A⊆F := Finset.filter_subset _ _
  have hne : ∀ S∈A,S.Nonempty := fun S hS=>actual_member_nonempty hlegal hcard (hAF hS)
  obtain ⟨P₀,hP₀,hright₀⟩ := hright
  have hA : A.Nonempty := ⟨P₀,hP₀⟩
  obtain ⟨P,hP,hmax⟩ := Finset.exists_max_image A First hA
  obtain ⟨T,hT,hmin⟩ := Finset.exists_min_image A Last hA
  let L := First P
  let R := Last T
  have hLc : c<L := (hright₀ _ (first_spec (hne P₀ hP₀)).1).trans_le (hmax P₀ hP₀)
  have hLmem : L∈P := (first_spec (hne P hP)).1
  have hRmem : R∈T := (last_spec (hne T hT)).1
  have hLN := (mem_ground N L).mp (hlegal.1 P (hAF hP) hLmem)
  have hRN := (mem_ground N R).mp (hlegal.1 T (hAF hT) hRmem)
  obtain ⟨x,hx⟩ := actual_inter_nonempty hlegal (hAF hP) (hAF hT) (hne P hP)
  obtain ⟨hxP,hxT⟩ := Finset.mem_inter.mp hx
  have hLR : L≤R := ((first_spec (hne P hP)).2 x hxP).trans ((last_spec (hne T hT)).2 x hxT)
  have hLcast : (L.toNat:ℤ)=L := by omega
  have hRcast : (R.toNat:ℤ)=R := by omega
  refine ⟨L.toNat,R.toNat,by omega,by omega,by omega,?_,?_,?_⟩
  · refine ⟨P,hP,?_⟩
    intro x hx
    rw [hLcast]
    exact (first_spec (hne P hP)).2 x hx
  · refine ⟨T,hT,?_⟩
    intro x hx
    rw [hRcast]
    exact (last_spec (hne T hT)).2 x hx
  · intro S hS
    constructor
    · refine ⟨First S,(first_spec (hne S hS)).1,?_,(first_spec (hne S hS)).2⟩
      rw [hLcast]
      exact hmax S hS
    · refine ⟨Last S,(last_spec (hne S hS)).1,?_,(last_spec (hne S hS)).2⟩
      rw [hRcast]
      exact hmin S hS

theorem actual_retained_outside_envelope (N r : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hlegal : Legal (Ground N) F) (hc : c∈Ground N)
    (hcard : 2≤(DenseDeletion40.Retained N r F).card)
    (hroot : ∀ S∈DenseDeletion40.Retained N r F,¬IsAP S → c∈S)
    (hcase : Rooted (DenseDeletion40.Retained N r F) c ∨
      ∃ P∈DenseDeletion40.Retained N r F,c∉P ∧ ((∀ x∈P,x<c) ∨ ∀ x∈P,c<x)) :
    ∃ H : Finset (Finset ℤ), (H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (DenseDeletion40.Deleted N r H).card=(DenseDeletion40.Deleted N r F).card ∧
      (DenseDeletion40.Retained N r H).card=(DenseDeletion40.Retained N r F).card ∧
      ∃ d∈Ground N,(∀ S∈DenseDeletion40.Retained N r H,¬IsAP S → d∈S) ∧
        (Rooted (DenseDeletion40.Retained N r H) d ∨
          ∃ L R : ℕ,d<(L:ℤ) ∧ L≤R ∧ R≤N ∧
            (∃ P∈Avoiders (DenseDeletion40.Retained N r H) d,∀ x∈P,(L:ℤ)≤x) ∧
            (∃ T∈Avoiders (DenseDeletion40.Retained N r H) d,∀ x∈T,x≤(R:ℤ)) ∧
            ∀ S∈Avoiders (DenseDeletion40.Retained N r H) d,
              (∃ a∈S,a≤(L:ℤ) ∧ ∀ x∈S,a≤x) ∧
              ∃ b∈S,(R:ℤ)≤b ∧ ∀ x∈S,x≤b) := by
  obtain ⟨H,hH,hLH,hHF,hEH,hGH,d,hd,hrootH,hcaseH⟩ :=
    actual_retained_right_orientation N r F c hlegal hc hroot hcase
  refine ⟨H,hH,hLH,hHF,hEH,hGH,d,hd,hrootH,?_⟩
  rcases hcaseH with hcommon | hright
  · exact Or.inl hcommon
  · apply Or.inr
    exact actual_outside_member_envelope (DenseDeletion40.actual_retained_legal hLH)
      (by simpa only [hGH] using hcard) hright

#print axioms first_spec
#print axioms last_spec
#print axioms actual_member_nonempty
#print axioms actual_inter_nonempty
#print axioms actual_outside_member_envelope
#print axioms actual_retained_outside_envelope
end
end JSP233.OutsideEnvelope43
