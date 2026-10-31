import Erdos272.Counting.PairShadowBudget218
import Erdos272.Counting.NonIntervalAP47

/-! Actual endpoint pairs and the two actual side shadows give a linear
bound for every common-root interval family. -/
namespace JSP233.PairShadowGeometry218
open StarCompletion APGeometry APCount41 WitnessInterval43 LongTerminal35
open PairShadowBudget218 NonIntervalAP47
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_interval_pair_shadow {N : ℕ} {c : ℤ} {U : Finset (Finset ℤ)}
    (hcN : c∈Ground N) (hground : ∀S∈U,S⊆Ground N)
    (hroot : ∀S∈U,c∈S) (hi : ∀S∈U,IsInterval S)
    (htwo : ∀S∈U,2≤S.card) :
    2*(U.card : ℝ)-(5/2 : ℝ)*(N-1) ≤ (PairShadow U c).card := by
  let X := {S // S∈U}
  have hex : ∀S:X,∃a b:ℤ,S.val=Finset.Icc a b := fun S => hi S.val S.property
  choose a b hrep using hex
  have hab : ∀S:X,a S≤c ∧ c≤b S := fun S =>
    Finset.mem_Icc.mp (hrep S ▸ hroot S.val S.property)
  have hablt : ∀S:X,a S<b S := by
    intro S
    by_contra hh
    have he : a S=b S := by have hh' := hab S; omega
    have ht := htwo S.val S.property
    rw [hrep S,he,Finset.Icc_self,Finset.card_singleton] at ht
    omega
  have haS : ∀S:X,a S∈S.val := by
    intro S; rw [hrep S]; exact Finset.mem_Icc.mpr ⟨le_rfl,(hablt S).le⟩
  have hbS : ∀S:X,b S∈S.val := by
    intro S; rw [hrep S]; exact Finset.mem_Icc.mpr ⟨(hablt S).le,le_rfl⟩
  obtain ⟨u,v,huc,hcv,hl,hr,hall⟩ := rooted_interval_envelope hroot hi
  let L := Finset.Ico u c
  let R := Finset.Ioc c v
  have hbounds : ∀S:X,u≤a S ∧ b S≤v := by
    intro S
    obtain ⟨a',b',hua,_hac,_hcb,hbv,he⟩ := hall S.val S.property
    have hsub : S.val⊆Finset.Icc u v := by
      rw [he]; intro x hx
      exact Finset.mem_Icc.mpr ⟨hua.trans (Finset.mem_Icc.mp hx).1,
        (Finset.mem_Icc.mp hx).2.trans hbv⟩
    exact ⟨(Finset.mem_Icc.mp (hsub (haS S))).1,
      (Finset.mem_Icc.mp (hsub (hbS S))).2⟩
  have hLsub : L⊆(Ground N).erase c := by
    intro x hx
    have hxI := Finset.mem_Ico.mp hx
    refine Finset.mem_erase.mpr ⟨by omega,?_⟩
    rcases hl with he | ⟨T,hTU,_hAP,hcover⟩
    · omega
    · exact hground T hTU (hcover (Finset.mem_Icc.mpr ⟨hxI.1,hxI.2.le⟩))
  have hRsub : R⊆(Ground N).erase c := by
    intro x hx
    have hxI := Finset.mem_Ioc.mp hx
    refine Finset.mem_erase.mpr ⟨by omega,?_⟩
    rcases hr with he | ⟨T,hTU,_hAP,hcover⟩
    · omega
    · exact hground T hTU (hcover (Finset.mem_Icc.mpr ⟨hxI.1.le,hxI.2⟩))
  have hLR : Disjoint L R := by
    apply Finset.disjoint_left.mpr
    intro x hxL hxR
    have h1 := (Finset.mem_Ico.mp hxL).2
    have h2 := (Finset.mem_Ioc.mp hxR).1
    omega
  have hsum : L.card+R.card≤N-1 := by
    have hh := Finset.card_le_card (Finset.union_subset hLsub hRsub)
    simpa only [Finset.card_union_of_disjoint hLR,Finset.card_erase_of_mem hcN,ground_card] using hh
  let E := (Finset.univ : Finset X).filter fun S => a S<c ∧ c<b S
  let A := (Finset.univ : Finset X).filter fun S => ¬(a S<c ∧ c<b S)
  let q : X→Finset ℤ := fun S => {a S,b S}
  let J := E.image q
  have hEi : Set.InjOn q E := by
    intro S hS T hT he
    have he' := ordered_pair_injective (hablt S) (hablt T) he
    apply Subtype.ext
    rw [hrep S,hrep T,he'.1,he'.2]
  have hJcard : J.card=E.card := Finset.card_image_of_injOn hEi
  have hJcross : J⊆CrossPairs L R := by
    intro W hW
    obtain ⟨S,hSE,rfl⟩ := Finset.mem_image.mp hW
    have hS := (Finset.mem_filter.mp hSE).2
    exact Finset.mem_image.mpr ⟨(a S,b S),Finset.mem_product.mpr
      ⟨Finset.mem_Ico.mpr ⟨(hbounds S).1,hS.1⟩,
        Finset.mem_Ioc.mpr ⟨hS.2,(hbounds S).2⟩⟩,rfl⟩
  have hEarea : E.card≤L.card*R.card := by
    rw [←hJcard]
    exact (Finset.card_le_card hJcross).trans (cross_pairs_card_le L R)
  have hJshadow : J⊆PairShadow U c := by
    intro W hW
    obtain ⟨S,hSE,rfl⟩ := Finset.mem_image.mp hW
    have hS := (Finset.mem_filter.mp hSE).2
    apply Finset.mem_biUnion.mpr
    refine ⟨S.val,S.property,Finset.mem_powersetCard.mpr ⟨?_,?_⟩⟩
    · intro x hx
      simp only [q,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact Finset.mem_erase.mpr ⟨by omega,haS S⟩
      · exact Finset.mem_erase.mpr ⟨by omega,hbS S⟩
    · dsimp only [q]
      exact Finset.card_pair_eq_two_iff.mpr (ne_of_lt (hablt S))
  have hLS : L.powersetCard 2⊆PairShadow U c := by
    intro W hW
    obtain ⟨hWL,hcard⟩ := Finset.mem_powersetCard.mp hW
    rcases hl with he | ⟨T,hTU,_hAP,hcover⟩
    · have hh := Finset.card_le_card hWL
      simp only [L,he,Finset.Ico_self,Finset.card_empty,hcard] at hh
      omega
    · apply Finset.mem_biUnion.mpr
      refine ⟨T,hTU,Finset.mem_powersetCard.mpr ⟨?_,hcard⟩⟩
      intro x hx
      have hxL := Finset.mem_Ico.mp (hWL hx)
      exact Finset.mem_erase.mpr ⟨by omega,hcover (Finset.mem_Icc.mpr ⟨hxL.1,hxL.2.le⟩)⟩
  have hRS : R.powersetCard 2⊆PairShadow U c := by
    intro W hW
    obtain ⟨hWR,hcard⟩ := Finset.mem_powersetCard.mp hW
    rcases hr with he | ⟨T,hTU,_hAP,hcover⟩
    · have hh := Finset.card_le_card hWR
      simp only [R,he,Finset.Ioc_self,Finset.card_empty,hcard] at hh
      omega
    · apply Finset.mem_biUnion.mpr
      refine ⟨T,hTU,Finset.mem_powersetCard.mpr ⟨?_,hcard⟩⟩
      intro x hx
      have hxR := Finset.mem_Ioc.mp (hWR hx)
      exact Finset.mem_erase.mpr ⟨by omega,hcover (Finset.mem_Icc.mpr ⟨hxR.1.le,hxR.2⟩)⟩
  have hPP : Disjoint (L.powersetCard 2) (R.powersetCard 2) := by
    apply Finset.disjoint_left.mpr
    intro W hWL hWR
    obtain ⟨hWL,hcard⟩ := Finset.mem_powersetCard.mp hWL
    have hWR := (Finset.mem_powersetCard.mp hWR).1
    obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega : 0<W.card)
    exact Finset.disjoint_left.mp hLR (hWL hx) (hWR hx)
  have hLJ : Disjoint (L.powersetCard 2) J := by
    apply Finset.disjoint_left.mpr
    intro W hWL hWJ
    obtain ⟨S,hSE,rfl⟩ := Finset.mem_image.mp hWJ
    have hS := (Finset.mem_filter.mp hSE).2
    have hh := (Finset.mem_powersetCard.mp hWL).1 (by simp [q] : b S∈q S)
    have hh' := (Finset.mem_Ico.mp hh).2
    omega
  have hRJ : Disjoint (R.powersetCard 2) J := by
    apply Finset.disjoint_left.mpr
    intro W hWR hWJ
    obtain ⟨S,hSE,rfl⟩ := Finset.mem_image.mp hWJ
    have hS := (Finset.mem_filter.mp hSE).2
    have hh := (Finset.mem_powersetCard.mp hWR).1 (by simp [q] : a S∈q S)
    have hh' := (Finset.mem_Ioc.mp hh).1
    omega
  have hshadow : L.card.choose 2+R.card.choose 2+E.card≤(PairShadow U c).card := by
    have hs := Finset.card_le_card
      (Finset.union_subset (Finset.union_subset hLS hRS) hJshadow)
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hLJ,hRJ⟩),
      Finset.card_union_of_disjoint hPP,Finset.card_powersetCard,Finset.card_powersetCard,hJcard] at hs
    exact hs
  let axis : X→ℤ := fun S => if a S<c then a S else b S
  have haxis : ∀S∈A,(a S<c ∧ b S=c) ∨ (a S=c ∧ c<b S) := by
    intro S hS
    have hn := (Finset.mem_filter.mp hS).2
    have hh := hab S
    have hlt := hablt S
    by_cases h : a S<c
    · exact Or.inl ⟨h,by omega⟩
    · exact Or.inr ⟨by omega,by omega⟩
  have hAxmap : Set.MapsTo axis A ((Ground N).erase c) := by
    intro S hS
    rcases haxis S hS with hs | hs
    · simp only [axis,if_pos hs.1]
      exact Finset.mem_erase.mpr ⟨by omega,hground S.val S.property (haS S)⟩
    · simp only [axis,if_neg (by omega : ¬a S<c)]
      exact Finset.mem_erase.mpr ⟨by omega,hground S.val S.property (hbS S)⟩
  have hAxi : Set.InjOn axis A := by
    intro S hS T hT he
    rcases haxis S hS with hs | hs <;> rcases haxis T hT with ht | ht
    · simp only [axis,if_pos hs.1,if_pos ht.1] at he
      apply Subtype.ext
      rw [hrep S,hrep T,he,hs.2,ht.2]
    · simp only [axis,if_pos hs.1,if_neg (by omega : ¬a T<c)] at he
      omega
    · simp only [axis,if_neg (by omega : ¬a S<c),if_pos ht.1] at he
      omega
    · simp only [axis,if_neg (by omega : ¬a S<c),if_neg (by omega : ¬a T<c)] at he
      apply Subtype.ext
      rw [hrep S,hrep T,hs.1,ht.1,he]
  have hAxis : A.card≤N-1 := by
    have hh := Finset.card_le_card_of_injOn axis hAxmap hAxi
    simpa only [Finset.card_erase_of_mem hcN,ground_card] using hh
  have hsplit : E.card+A.card=U.card := by
    have hh := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset X))
      (fun S => a S<c ∧ c<b S)
    simpa only [Finset.card_univ,Fintype.card_coe,X] using hh
  have hN : 1≤N := by have hh := (mem_ground N c).mp hcN; omega
  have hsumR : (L.card : ℝ)+R.card≤(N : ℝ)-1 := by exact_mod_cast hsum
  have hAxisR : (A.card : ℝ)≤(N : ℝ)-1 := by exact_mod_cast hAxis
  have hsplitR : (E.card : ℝ)+A.card=U.card := by exact_mod_cast hsplit
  have hEareaR : (E.card : ℝ)≤(L.card : ℝ)*R.card := by exact_mod_cast hEarea
  have hshadowR : (L.card.choose 2 : ℝ)+(R.card.choose 2 : ℝ)+E.card≤(PairShadow U c).card := by
    exact_mod_cast hshadow
  rw [Nat.cast_choose_two,Nat.cast_choose_two] at hshadowR
  have hsquare := sq_nonneg ((L.card : ℝ)-R.card)
  nlinarith only [hsumR,hAxisR,hsplitR,hEareaR,hshadowR,hsquare]

theorem actual_root_unit_pair_shadow {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hc : c∈Ground N) (hF : Legal (Ground N) F) :
    2*((RootUnitAP F c).card : ℝ)-(5/2 : ℝ)*(N-1) ≤
      (PairShadow (RootUnitAP F c) c).card := by
  apply actual_interval_pair_shadow hc
  · intro S hS
    exact hF.1 S (Finset.mem_filter.mp hS).1
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.1
  · intro S hS
    obtain ⟨_,_hc,hAP,_htwo,hstep⟩ := Finset.mem_filter.mp hS
    obtain ⟨_,p,hp⟩ := actual_step hAP
    rw [hstep] at hp
    exact actual_step_one_interval hp
  · intro S hS
    exact (Finset.mem_filter.mp hS).2.2.2.1

#print axioms actual_interval_pair_shadow
#print axioms actual_root_unit_pair_shadow
end
end JSP233.PairShadowGeometry218
