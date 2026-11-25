module

public import Erdos272.Counting.N80470.RootedShort80470

@[expose] public section

namespace JSP233.TwoEndShort67702
open StarCompletion APGeometry APCount41 ShortAP208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000

theorem actual_rooted_two_interval {L R : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hLR : L≤R) (hcL : c<(L : ℤ))
    (htwo : ∀ S∈F,S.card=2) (hroot : ∀ S∈F,c∈S)
    (hleft : ∀ S∈F,∃z∈S,(L : ℤ)≤z)
    (hright : ∀ S∈F,∃z∈S,z≠c ∧ z≤(R : ℤ)) : F.card≤R-L+1 := by
  let X := {S // S∈F}
  have hex : ∀ S:X,∃a : ℤ,S.val={c,a} ∧ a≠c ∧ a∈Finset.Icc (L : ℤ) R := by
    intro S
    obtain ⟨a,b,hab,he⟩ := Finset.card_eq_two.mp (htwo S.val S.property)
    have hc : c=a ∨ c=b := by simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hroot S.val S.property
    have hh : ∀a : ℤ,S.val={c,a} → a≠c → a∈Finset.Icc (L : ℤ) R := by
      intro a ha hne
      obtain ⟨z,hz,hLz⟩ := hleft S.val S.property
      rw [ha] at hz
      have hza : z=a := by simp only [Finset.mem_insert,Finset.mem_singleton] at hz;omega
      obtain ⟨v,hv,hvc,hvR⟩ := hright S.val S.property
      have hav : a≤(R : ℤ) := by
        rw [ha] at hv
        simp only [Finset.mem_insert,Finset.mem_singleton] at hv
        omega
      exact Finset.mem_Icc.mpr ⟨by omega,hav⟩
    rcases hc with rfl | rfl
    · exact ⟨b,he,hab.symm,hh b he hab.symm⟩
    · have he' : S.val={c,a} := by simpa only [Finset.pair_comm] using he
      exact ⟨a,he',hab,hh a he' hab⟩
  choose a ha using hex
  have hmaps : Set.MapsTo a (Finset.univ : Finset X) (Finset.Icc (L : ℤ) R) :=
    fun S _=>(ha S).2.2
  have hinj : Function.Injective a := by
    intro S T he
    apply Subtype.ext
    rw [(ha S).1,(ha T).1,he]
  have hh := Finset.card_le_card_of_injOn a hmaps hinj.injOn
  have hc : (Finset.Icc (L : ℤ) R).card=R-L+1 := by rw [Int.card_Icc];omega
  simpa only [Finset.card_univ,X,Fintype.card_coe,hc] using hh

theorem actual_three_positions {N L c : ℕ} {F : Finset (Finset ℤ)}
    (hc : (c : ℤ)∈Ground N) (hcL : c<L) (hLN : L≤N)
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hthree : ∀ S∈F,S.card=3) (hroot : ∀ S∈F,(c : ℤ)∈S)
    (hleft : ∀ S∈F,∃z∈S,(L : ℤ)≤z) :
    (F.card : ℝ)≤((N : ℝ)-L)/2+c := by
  let C (i : ℕ) := F.filter (fun S=>RootPosition (c : ℤ) S=i)
  have hdata := fun S hS=>actual_root_position (hsub S hS) (hAP S hS)
    (by rw [hthree S hS];omega) (hroot S hS)
  have hend : ∀ S∈F,(1 : ℤ)≤Low S ∧ High S≤(N : ℤ) := by
    intro S hS
    have hn := isAP_nonempty (hAP S hS)
    exact ⟨((mem_ground N _).mp (hsub S hS (low_spec hn).1)).1,
      ((mem_ground N _).mp (hsub S hS (high_spec hn).1)).2⟩
  have hmaps : Set.MapsTo Step (C 0 : Set (Finset ℤ))
      (Finset.Icc ((L-c+1)/2) ((N-c)/2)) := by
    intro S hS
    obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
    obtain ⟨hd,hi,hs,he⟩ := hdata S hSF
    rw [hSi] at hs
    rw [hthree S hSF] at he
    norm_num at hs he
    obtain ⟨z,hz,hLz⟩ := hleft S hSF
    have hzH := (high_spec (isAP_nonempty (hAP S hSF))).2 z hz
    have hHN := (hend S hSF).2
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  have hinj : Set.InjOn Step (C 0 : Set (Finset ℤ)) := by
    intro S hS T hT hd
    obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
    obtain ⟨hTF,hTi⟩ := Finset.mem_filter.mp hT
    have hs := (hdata S hSF).2.2.1
    have ht := (hdata T hTF).2.2.1
    rw [hSi] at hs
    rw [hTi] at ht
    norm_num at hs ht
    rw [actual_AP_range (hAP S hSF),actual_AP_range (hAP T hTF),hthree S hSF,hthree T hTF,hs,ht,hd]
  have h0 := Finset.card_le_card_of_injOn Step hmaps hinj
  have h0n : 2*(C 0).card≤N-L+2 := by rw [Nat.card_Icc] at h0;omega
  have h1 : (C 1).card≤c-1 := by
    apply actual_rooted_three_position_count
      (fun S hS=>hsub S (Finset.mem_filter.mp hS).1)
      (fun S hS=>hAP S (Finset.mem_filter.mp hS).1)
      (fun S hS=>hthree S (Finset.mem_filter.mp hS).1)
      (fun S hS=>hroot S (Finset.mem_filter.mp hS).1)
      (fun S hS=>(Finset.mem_filter.mp hS).2)
    intro S hS
    obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
    have hs := (hdata S hSF).2.2.1
    rw [hSi] at hs
    norm_num at hs
    have hl := (hend S hSF).1
    omega
  have h2 : C 2=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSF,hSi⟩ := Finset.mem_filter.mp hS
    obtain ⟨hd,hi,hs,he⟩ := hdata S hSF
    rw [hSi] at hs
    rw [hthree S hSF] at he
    norm_num at hs he
    obtain ⟨z,hz,hLz⟩ := hleft S hSF
    have hzH := (high_spec (isAP_nonempty (hAP S hSF))).2 z hz
    omega
  have hpart : F.card=∑i∈Finset.range 3,(C i).card :=
    Finset.card_eq_sum_card_fiberwise (show Set.MapsTo (RootPosition (c : ℤ))
      (F : Set (Finset ℤ)) (Finset.range 3) from fun S hS=>
        Finset.mem_range.mpr (by have hh:=(hdata S hS).2.1;rw [hthree S hS] at hh;exact hh))
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,h2,Finset.card_empty,Nat.add_zero] at hpart
  have hc1 : 1≤c := by have hh:=(mem_ground N (c : ℤ)).mp hc;omega
  have h0r : 2*((C 0).card : ℝ)≤(N : ℝ)-L+2 := by
    have hh : 2*((C 0).card : ℝ)≤((N-L+2 : ℕ) : ℝ) := by exact_mod_cast h0n
    simpa only [Nat.cast_add,Nat.cast_sub hLN,Nat.cast_ofNat] using hh
  have h1r : ((C 1).card : ℝ)≤(c : ℝ)-1 := by
    have hh : ((C 1).card : ℝ)≤((c-1 : ℕ) : ℝ) := by exact_mod_cast h1
    simpa only [Nat.cast_sub hc1,Nat.cast_one] using hh
  have hpr : (F.card : ℝ)=((C 0).card : ℝ)+(C 1).card := by exact_mod_cast hpart
  linarith only [h0r,h1r,hpr]

theorem actual_small_count {N L R c : ℕ} {F : Finset (Finset ℤ)}
    (hc : (c : ℤ)∈Ground N) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hsub : ∀ S∈F,S⊆Ground N) (hAP : ∀ S∈F,IsAP S)
    (hsmall : ∀ S∈F,S.card≤3) (hroot : ∀ S∈F,(c : ℤ)∈S)
    (hleft : ∀ S∈F,∃z∈S,(L : ℤ)≤z)
    (hright : ∀ S∈F,∃z∈S,z≠(c : ℤ)∧z≤(R : ℤ)) :
    (F.card : ℝ)≤(3/2 : ℝ)*N-(L : ℝ)/2-((L : ℝ)+((N : ℝ)-R))+c+1 := by
  let C (i : ℕ) := F.filter (fun S=>S.card=i)
  have h1 : (C 1).card≤0 := by
    have hz : C 1=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      obtain ⟨hSF,hSc⟩ := Finset.mem_filter.mp hS
      have he := singleton_of_root_card_le_one (hroot S hSF) (by omega : S.card≤1)
      obtain ⟨z,hz,hLz⟩ := hleft S hSF
      rw [he,Finset.mem_singleton] at hz
      have hcLZ : (c : ℤ)<L := by exact_mod_cast hcL
      omega
    simp only [hz,Finset.card_empty,le_refl]
  have h2 := actual_rooted_two_interval hLR (by exact_mod_cast hcL)
    (F:=C 2) (fun S hS=>(Finset.mem_filter.mp hS).2)
    (fun S hS=>hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hleft S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hright S (Finset.mem_filter.mp hS).1)
  have h3 := actual_three_positions hc hcL (hLR.trans hRN)
    (F:=C 3) (fun S hS=>hsub S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hAP S (Finset.mem_filter.mp hS).1)
    (fun S hS=>(Finset.mem_filter.mp hS).2)
    (fun S hS=>hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS=>hleft S (Finset.mem_filter.mp hS).1)
  have hcover : F⊆C 1∪C 2∪C 3 := by
    intro S hS
    have hp : 0<S.card := Finset.card_pos.mpr ⟨c,hroot S hS⟩
    have hu := hsmall S hS
    simp only [Finset.mem_union,C,Finset.mem_filter,hS,true_and]
    omega
  have hh := (Finset.card_le_card hcover).trans
    ((Finset.card_union_le (C 1∪C 2) (C 3)).trans
      (Nat.add_le_add_right (Finset.card_union_le (C 1) (C 2)) _))
  have hhR : (F.card : ℝ)≤(C 1).card+(C 2).card+(C 3).card := by exact_mod_cast hh
  have h1R : ((C 1).card : ℝ)≤0 := by exact_mod_cast h1
  have h2R : ((C 2).card : ℝ)≤(R : ℝ)-L+1 := by
    have hr : ((C 2).card : ℝ)≤((R-L+1 : ℕ) : ℝ) := by exact_mod_cast h2
    simpa only [Nat.cast_add,Nat.cast_sub hLR,Nat.cast_one] using hr
  linarith only [hhR,h1R,h2R,h3]

#print axioms actual_rooted_two_interval
#print axioms actual_three_positions
#print axioms actual_small_count
end
end JSP233.TwoEndShort67702
