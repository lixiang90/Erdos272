import Erdos272.Foundation.APGeometry
import Erdos272.Foundation.JSP233
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
import Erdos272.Construction.ConstructionGeometry45

/-! Szabo's actual all-N lower construction.  The finite family is explicit;
no supplied validity, injectivity, or cardinality premises are used. -/
namespace JSP233.Construction45
open StarCompletion APGeometry
open scoped Classical
noncomputable section

def Center (N : ℕ) : ℤ := ((N+1)/2:ℕ)
def Scales (N : ℕ) : Finset ℕ := Finset.Icc 1 ((N-1)/4)
def Codes (N q : ℕ) : Finset (ℕ×Fin q) := (Scales N).product Finset.univ
def BadMember (m d : ℤ) (i : Fin 2) : Finset ℤ :=
  if i.val=0 then {m-2*d,m,m+d} else {m-d,m,m+2*d}
def LargeMember (m d : ℤ) (i : Fin 3) : Finset ℤ :=
  if i.val=0 then {m-2*d,m-d,m,m+d,m+2*d}
  else if i.val=1 then {m-2*d,m-d,m,m+d} else {m-d,m,m+d,m+2*d}
def Triples (N : ℕ) : Finset (Finset ℤ) :=
  ((Ground N).erase (Center N)).powersetCard 2 |>.image (insert (Center N))
def Removed (N : ℕ) : Finset (Finset ℤ) :=
  (Codes N 2).image (fun k=>BadMember (Center N) k.1 k.2)
def Large (N : ℕ) : Finset (Finset ℤ) :=
  (Codes N 3).image (fun k=>LargeMember (Center N) k.1 k.2)
def RetainedTriples (N : ℕ) : Finset (Finset ℤ) := Triples N\Removed N
def Family (N : ℕ) : Finset (Finset ℤ) :=
  (PairStar (Ground N) (Center N)∪RetainedTriples N)∪Large N

theorem center_mem (N : ℕ) (hN : 1≤N) : Center N∈Ground N := by
  rw [mem_ground]
  dsimp [Center]
  omega

theorem scale_bounds {N d : ℕ} (hd : d∈Scales N) :
    0<(d:ℤ) ∧ 2*(d:ℤ)<Center N ∧ Center N+2*(d:ℤ)≤(N:ℤ) := by
  have hh := Finset.mem_Icc.mp hd
  dsimp [Center]
  dsimp [Scales] at hd
  omega

theorem bad_extrema (m d : ℤ) (i : Fin 2) (hd : 0<d) :
    let a:=if i.val=0 then m-2*d else m-d
    let b:=if i.val=0 then m+d else m+2*d
    a∈BadMember m d i ∧ b∈BadMember m d i ∧
      ∀ x∈BadMember m d i,a≤x ∧ x≤b := by
  fin_cases i <;> dsimp [BadMember]
  all_goals refine ⟨by simp,by simp,?_⟩
  all_goals intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx;omega

theorem large_extrema (m d : ℤ) (i : Fin 3) (hd : 0<d) :
    let a:=if i.val=2 then m-d else m-2*d
    let b:=if i.val=1 then m+d else m+2*d
    a∈LargeMember m d i ∧ b∈LargeMember m d i ∧
      ∀ x∈LargeMember m d i,a≤x ∧ x≤b := by
  fin_cases i <;> dsimp [LargeMember]
  all_goals refine ⟨by simp,by simp,?_⟩
  all_goals intro x hx;simp only [Finset.mem_insert,Finset.mem_singleton] at hx;omega

theorem endpoints_of_equal {S T : Finset ℤ} {a b x y : ℤ}
    (hS : a∈S ∧ b∈S ∧ ∀ z∈S,a≤z ∧ z≤b)
    (hT : x∈T ∧ y∈T ∧ ∀ z∈T,x≤z ∧ z≤y) (he : S=T) : a=x ∧ b=y := by
  subst T
  exact ⟨le_antisymm (hS.2.2 x hT.1).1 (hT.2.2 a hS.1).1,
    le_antisymm (hT.2.2 b hS.2.1).2 (hS.2.2 y hT.2.1).2⟩

theorem bad_code_injective {m : ℤ} {d e : ℕ} {i j : Fin 2}
    (hd : 0<d) (he : 0<e) (hh : BadMember m d i=BadMember m e j) : d=e ∧ i=j := by
  have hp := endpoints_of_equal (bad_extrema m d i (by exact_mod_cast hd))
    (bad_extrema m e j (by exact_mod_cast he)) hh
  fin_cases i <;> fin_cases j <;> norm_num at hp ⊢ <;> omega

theorem large_code_injective {m : ℤ} {d e : ℕ} {i j : Fin 3}
    (hd : 0<d) (he : 0<e) (hh : LargeMember m d i=LargeMember m e j) : d=e ∧ i=j := by
  have hp := endpoints_of_equal (large_extrema m d i (by exact_mod_cast hd))
    (large_extrema m e j (by exact_mod_cast he)) hh
  fin_cases i <;> fin_cases j <;> norm_num at hp ⊢ <;> omega

theorem bad_member_card (m d : ℤ) (i : Fin 2) (hd : 0<d) : (BadMember m d i).card=3 := by
  have h1 : m-2*d≠m := by omega
  have h2 : m-2*d≠m+d := by omega
  have h3 : m≠m+d := by omega
  have h4 : m-d≠m := by omega
  have h5 : m-d≠m+2*d := by omega
  have h6 : m≠m+2*d := by omega
  fin_cases i <;> simp [BadMember,h1,h2,h3,h4,h5,h6]

theorem large_member_card (m d : ℤ) (i : Fin 3) (hd : 0<d) :
    (LargeMember m d i).card=if i.val=0 then 5 else 4 := by
  have h1 : m-2*d≠m-d := by omega
  have h2 : m-2*d≠m := by omega
  have h3 : m-2*d≠m+d := by omega
  have h4 : m-2*d≠m+2*d := by omega
  have h5 : m-d≠m := by omega
  have h6 : m-d≠m+d := by omega
  have h7 : m-d≠m+2*d := by omega
  have h8 : m≠m+d := by omega
  have h9 : m≠m+2*d := by omega
  have h10 : m+d≠m+2*d := by omega
  fin_cases i <;> simp [LargeMember,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10]

theorem codes_card (N q : ℕ) : (Codes N q).card=((N-1)/4)*q := by
  simp [Codes,Scales,Nat.card_Icc]

theorem removed_card (N : ℕ) : (Removed N).card=2*((N-1)/4) := by
  rw [Removed,Finset.card_image_of_injOn,codes_card,Nat.mul_comm]
  intro a ha b hb heq
  have ha' := Finset.mem_Icc.mp (Finset.mem_product.mp ha).1
  have hb' := Finset.mem_Icc.mp (Finset.mem_product.mp hb).1
  exact Prod.ext (bad_code_injective (by omega) (by omega) heq).1
    (bad_code_injective (by omega) (by omega) heq).2

theorem large_card (N : ℕ) : (Large N).card=3*((N-1)/4) := by
  rw [Large,Finset.card_image_of_injOn,codes_card,Nat.mul_comm]
  intro a ha b hb heq
  have ha' := Finset.mem_Icc.mp (Finset.mem_product.mp ha).1
  have hb' := Finset.mem_Icc.mp (Finset.mem_product.mp hb).1
  exact Prod.ext (large_code_injective (by omega) (by omega) heq).1
    (large_code_injective (by omega) (by omega) heq).2

theorem mem_triples_iff (N : ℕ) {S : Finset ℤ} (hN : 1≤N) :
    S∈Triples N ↔ S⊆Ground N ∧ Center N∈S ∧ S.card=3 := by
  constructor
  · intro hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨hT,hcard⟩ := Finset.mem_powersetCard.mp hT
    have hn : Center N∉T := by
      intro hh
      exact (Finset.mem_erase.mp (hT hh)).1 rfl
    refine ⟨Finset.insert_subset (center_mem N hN) (fun x hx=>(Finset.mem_erase.mp (hT hx)).2),
      by simp,?_⟩
    simp [Finset.card_insert_of_notMem hn,hcard]
  · rintro ⟨hS,hm,hcard⟩
    apply Finset.mem_image.mpr
    refine ⟨S.erase (Center N),Finset.mem_powersetCard.mpr ⟨?_,?_⟩,Finset.insert_erase hm⟩
    · intro x hx
      have hh := Finset.mem_erase.mp hx
      exact Finset.mem_erase.mpr ⟨hh.1,hS hh.2⟩
    · rw [Finset.card_erase_of_mem hm,hcard]

theorem triples_card (N : ℕ) (hN : 1≤N) : (Triples N).card=(N-1).choose 2 := by
  unfold Triples
  rw [Finset.card_image_of_injOn,Finset.card_powersetCard,
    Finset.card_erase_of_mem (center_mem N hN),ground_card]
  intro A hA B hB he
  have ha := (Finset.mem_powersetCard.mp hA).1
  have hb := (Finset.mem_powersetCard.mp hB).1
  have hna : Center N∉A := by intro h;exact (Finset.mem_erase.mp (ha h)).1 rfl
  have hnb : Center N∉B := by intro h;exact (Finset.mem_erase.mp (hb h)).1 rfl
  have herr := congrArg (fun S : Finset ℤ=>S.erase (Center N)) he
  simpa only [Finset.erase_insert hna,Finset.erase_insert hnb] using herr

theorem bad_member_properties {N d : ℕ} (hd : d∈Scales N) (i : Fin 2) :
    BadMember (Center N) d i⊆Ground N ∧ Center N∈BadMember (Center N) d i ∧
      (BadMember (Center N) d i).card=3 := by
  obtain ⟨hd0,hlo,hhi⟩ := scale_bounds hd
  refine ⟨?_,?_,bad_member_card _ _ _ hd0⟩
  · intro x hx
    rw [mem_ground]
    fin_cases i <;> dsimp [BadMember] at hx
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at hx;omega
  · fin_cases i <;> simp [BadMember]

theorem large_member_properties {N d : ℕ} (hd : d∈Scales N) (i : Fin 3) :
    LargeMember (Center N) d i⊆Ground N ∧ Center N∈LargeMember (Center N) d i ∧
      4≤(LargeMember (Center N) d i).card := by
  obtain ⟨hd0,hlo,hhi⟩ := scale_bounds hd
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [mem_ground]
    fin_cases i <;> dsimp [LargeMember] at hx
    all_goals simp only [Finset.mem_insert,Finset.mem_singleton] at hx;omega
  · fin_cases i <;> simp [LargeMember]
  · rw [large_member_card _ _ _ hd0]
    split <;> omega

theorem removed_subset_triples (N : ℕ) (hN : 1≤N) : Removed N⊆Triples N := by
  intro S hS
  obtain ⟨⟨d,i⟩,hd,rfl⟩ := Finset.mem_image.mp hS
  exact (mem_triples_iff N hN).mpr (bad_member_properties (Finset.mem_product.mp hd).1 i)

theorem small_properties {N : ℕ} (hN : 1≤N) {S : Finset ℤ}
    (hS : S∈PairStar (Ground N) (Center N)) :
    S⊆Ground N ∧ Center N∈S ∧ S.card≤2 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hS
  refine ⟨?_,by simp,Finset.card_le_two⟩
  intro y hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hy
  rcases hy with rfl|rfl
  · exact center_mem N hN
  · exact hx

theorem retained_triple_properties {N : ℕ} (hN : 1≤N) {S : Finset ℤ}
    (hS : S∈RetainedTriples N) : S⊆Ground N ∧ Center N∈S ∧ S.card=3 :=
  (mem_triples_iff N hN).mp (Finset.mem_sdiff.mp hS).1

theorem large_properties {N : ℕ} {S : Finset ℤ} (hS : S∈Large N) :
    S⊆Ground N ∧ Center N∈S ∧ 4≤S.card := by
  obtain ⟨⟨d,i⟩,hd,rfl⟩ := Finset.mem_image.mp hS
  exact large_member_properties (Finset.mem_product.mp hd).1 i

theorem family_ground_and_root (N : ℕ) (hN : 1≤N) :
    (∀ S∈Family N,S⊆Ground N) ∧ Rooted (Family N) (Center N) := by
  have hh : ∀ S∈Family N,S⊆Ground N ∧ Center N∈S := by
    intro S hS
    rcases Finset.mem_union.mp hS with hS|hS
    · rcases Finset.mem_union.mp hS with hS|hS
      · exact ⟨(small_properties hN hS).1,(small_properties hN hS).2.1⟩
      · exact ⟨(retained_triple_properties hN hS).1,(retained_triple_properties hN hS).2.1⟩
    · exact ⟨(large_properties hS).1,(large_properties hS).2.1⟩
  exact ⟨fun S hS=>(hh S hS).1,fun S hS=>(hh S hS).2⟩

theorem small_retained_disjoint (N : ℕ) (hN : 1≤N) :
    Disjoint (PairStar (Ground N) (Center N)) (RetainedTriples N) := by
  apply Finset.disjoint_left.mpr
  intro S hs ht
  have h2 := (small_properties hN hs).2.2
  have h3 := (retained_triple_properties hN ht).2.2
  omega

theorem small_retained_large_disjoint (N : ℕ) (hN : 1≤N) :
    Disjoint (PairStar (Ground N) (Center N)∪RetainedTriples N) (Large N) := by
  apply Finset.disjoint_left.mpr
  intro S hs ht
  have h4 := (large_properties ht).2.2
  rcases Finset.mem_union.mp hs with hs|hs
  · have h2 := (small_properties hN hs).2.2
    omega
  · have h3 := (retained_triple_properties hN hs).2.2
    omega

theorem retained_triples_card (N : ℕ) (hN : 1≤N) :
    (RetainedTriples N).card+2*((N-1)/4)=(N-1).choose 2 := by
  have hc := Finset.card_sdiff_add_card_eq_card (removed_subset_triples N hN)
  simpa only [RetainedTriples,removed_card,triples_card N hN] using hc

theorem actual_family_card (N : ℕ) (hN : 1≤N) : (Family N).card=B N := by
  have ht := retained_triples_card N hN
  have hchoose := Nat.choose_succ_succ' (N-1) 1
  have hn : N-1+1=N := by omega
  rw [hn] at hchoose
  norm_num only [Nat.reduceAdd,Nat.choose_one_right] at hchoose
  rw [Family,Finset.card_union_of_disjoint (small_retained_large_disjoint N hN),
    Finset.card_union_of_disjoint (small_retained_disjoint N hN),pairStar_card,ground_card,large_card]
  unfold B
  omega

theorem triple_intersection_alternative {S T : Finset ℤ} (hS : S.card=3) :
    (S∩T).card≤2 ∨ S⊆T := by
  by_cases hh : (S∩T).card≤2
  · exact Or.inl hh
  · have he : S∩T=S := Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    exact Or.inr (he ▸ Finset.inter_subset_right)

theorem distinct_triples_inter_card {S T : Finset ℤ} (hS : S.card=3) (hT : T.card=3)
    (hne : S≠T) : (S∩T).card≤2 := by
  rcases triple_intersection_alternative hS with h|h
  · exact h
  · exact False.elim (hne (Finset.eq_of_subset_of_card_le h (by omega)))

theorem actual_small_inter_isAP {N : ℕ} (hN : 1≤N) {S T : Finset ℤ}
    (hS : S∈PairStar (Ground N) (Center N)) (hT : T∈Family N) : IsAP (S∩T) := by
  have hs := small_properties hN hS
  have ht := (family_ground_and_root N hN).2 T hT
  exact nonempty_card_le_two_isAP ⟨Center N,Finset.mem_inter.mpr ⟨hs.2.1,ht⟩⟩
    ((Finset.card_le_card Finset.inter_subset_left).trans hs.2.2)

theorem actual_retained_triples_inter_isAP {N : ℕ} (hN : 1≤N) {S T : Finset ℤ}
    (hS : S∈RetainedTriples N) (hT : T∈RetainedTriples N) (hne : S≠T) : IsAP (S∩T) := by
  have hs := retained_triple_properties hN hS
  have ht := retained_triple_properties hN hT
  exact nonempty_card_le_two_isAP ⟨Center N,Finset.mem_inter.mpr ⟨hs.2.1,ht.2.1⟩⟩
    (distinct_triples_inter_card hs.2.2 ht.2.2 hne)

theorem large_member_subset_window (m d : ℤ) (i : Fin 3) :
    LargeMember m d i⊆ConstructionGeometry45.Window m d := by
  fin_cases i <;> dsimp [LargeMember]
  · exact Finset.Subset.refl _
  · exact ConstructionGeometry45.left_four_subset_window m d
  · exact ConstructionGeometry45.right_four_subset_window m d

theorem large_member_isAP (m d : ℤ) (i : Fin 3) (hd : 0<d) : IsAP (LargeMember m d i) := by
  fin_cases i <;> dsimp [LargeMember]
  · exact ConstructionGeometry45.window_isAP m d hd
  · exact ConstructionGeometry45.left_four_isAP m d hd
  · exact ConstructionGeometry45.right_four_isAP m d hd

theorem actual_large_isAP {N : ℕ} {S : Finset ℤ} (hS : S∈Large N) : IsAP S := by
  obtain ⟨⟨d,i⟩,hd,rfl⟩ := Finset.mem_image.mp hS
  exact large_member_isAP _ _ i (scale_bounds (Finset.mem_product.mp hd).1).1

theorem actual_retained_triple_in_window_isAP {N d : ℕ} (hN : 1≤N) (hd : d∈Scales N)
    {S : Finset ℤ} (hS : S∈RetainedTriples N)
    (hsub : S⊆ConstructionGeometry45.Window (Center N) d) : IsAP S := by
  have hs := retained_triple_properties hN hS
  have hbad := (Finset.mem_sdiff.mp hS).2
  have hL : BadMember (Center N) d 0∈Removed N := Finset.mem_image.mpr
    ⟨(d,0),Finset.mem_product.mpr ⟨hd,by simp⟩,rfl⟩
  have hR : BadMember (Center N) d 1∈Removed N := Finset.mem_image.mpr
    ⟨(d,1),Finset.mem_product.mpr ⟨hd,by simp⟩,rfl⟩
  apply ConstructionGeometry45.actual_centered_triple_isAP (Center N) d (scale_bounds hd).1
    S hs.2.1 hs.2.2 hsub
  · intro he
    have he' : S=BadMember (Center N) d 0 := he
    exact hbad (he'.symm ▸ hL)
  · intro he
    have he' : S=BadMember (Center N) d 1 := he
    exact hbad (he'.symm ▸ hR)

theorem actual_triple_large_inter_isAP {N : ℕ} (hN : 1≤N) {S T : Finset ℤ}
    (hS : S∈RetainedTriples N) (hT : T∈Large N) : IsAP (S∩T) := by
  have hs := retained_triple_properties hN hS
  have ht := large_properties hT
  rcases triple_intersection_alternative hs.2.2 with hsmall|hsub
  · exact nonempty_card_le_two_isAP ⟨Center N,Finset.mem_inter.mpr ⟨hs.2.1,ht.2.1⟩⟩ hsmall
  · have he : S∩T=S := Finset.inter_eq_left.mpr hsub
    rw [he]
    obtain ⟨⟨d,i⟩,hd,rfl⟩ := Finset.mem_image.mp hT
    exact actual_retained_triple_in_window_isAP hN (Finset.mem_product.mp hd).1 hS
      (hsub.trans (large_member_subset_window _ _ i))

theorem actual_large_inter_isAP {N : ℕ} {S T : Finset ℤ}
    (hS : S∈Large N) (hT : T∈Large N) : IsAP (S∩T) :=
  isAP_inter_of_nonempty (actual_large_isAP hS) (actual_large_isAP hT)
    ⟨Center N,Finset.mem_inter.mpr ⟨(large_properties hS).2.1,(large_properties hT).2.1⟩⟩

theorem actual_family_legal (N : ℕ) (hN : 1≤N) : Legal (Ground N) (Family N) := by
  refine ⟨(family_ground_and_root N hN).1,?_⟩
  intro S hS T hT hne
  have hSF := hS
  have hTF := hT
  rcases Finset.mem_union.mp hS with hS|hS
  · rcases Finset.mem_union.mp hS with hS|hS
    · exact actual_small_inter_isAP hN hS hTF
    · rcases Finset.mem_union.mp hT with hT|hT
      · rcases Finset.mem_union.mp hT with hT|hT
        · simpa only [Finset.inter_comm] using actual_small_inter_isAP hN hT hSF
        · exact actual_retained_triples_inter_isAP hN hS hT hne
      · exact actual_triple_large_inter_isAP hN hS hT
  · rcases Finset.mem_union.mp hT with hT|hT
    · rcases Finset.mem_union.mp hT with hT|hT
      · simpa only [Finset.inter_comm] using actual_small_inter_isAP hN hT hSF
      · simpa only [Finset.inter_comm] using actual_triple_large_inter_isAP hN hT hS
    · exact actual_large_inter_isAP hS hT

theorem szabo_lower_construction (N : ℕ) (hN : 1≤N) :
    ∃ F : Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N :=
  ⟨Family N,actual_family_legal N hN,actual_family_card N hN⟩

theorem szabo_lower_construction_all : ∀ N : ℕ,1≤N →
    ∃ F : Finset (Finset ℤ),Legal (Ground N) F ∧ F.card=B N := szabo_lower_construction

#print axioms center_mem
#print axioms scale_bounds
#print axioms bad_extrema
#print axioms large_extrema
#print axioms endpoints_of_equal
#print axioms bad_code_injective
#print axioms large_code_injective
#print axioms bad_member_card
#print axioms large_member_card
#print axioms codes_card
#print axioms removed_card
#print axioms large_card
#print axioms mem_triples_iff
#print axioms triples_card
#print axioms bad_member_properties
#print axioms large_member_properties
#print axioms removed_subset_triples
#print axioms small_properties
#print axioms retained_triple_properties
#print axioms large_properties
#print axioms family_ground_and_root
#print axioms small_retained_disjoint
#print axioms small_retained_large_disjoint
#print axioms retained_triples_card
#print axioms actual_family_card
#print axioms triple_intersection_alternative
#print axioms distinct_triples_inter_card
#print axioms actual_small_inter_isAP
#print axioms actual_retained_triples_inter_isAP
#print axioms large_member_subset_window
#print axioms large_member_isAP
#print axioms actual_large_isAP
#print axioms actual_retained_triple_in_window_isAP
#print axioms actual_triple_large_inter_isAP
#print axioms actual_large_inter_isAP
#print axioms actual_family_legal
#print axioms szabo_lower_construction
#print axioms szabo_lower_construction_all

end
end JSP233.Construction45
