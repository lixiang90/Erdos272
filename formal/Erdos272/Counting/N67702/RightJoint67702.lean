module

public import Erdos272.Counting.N67702.RightRows67702

@[expose] public section

namespace JSP233.RightJoint67702
open StarCompletion APGeometry PrivatePairExistence LongTerminal35 WitnessInterval43
open RightJoint50
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

theorem actual_CQ_EP_joint {N c L R : ℕ} {F C E : Finset (Finset ℤ)}
    (hcL : c < L) (hLR : L ≤ R) (hRN : R ≤ N) (hF : Legal (Ground N) F)
    (hCF : C ⊆ F) (hEF : E ⊆ F) (hc : ∀ S ∈ C, (c:ℤ)∈S)
    (x p j q : Finset ℤ → ℤ)
    (hC : ∀ S ∈ C, (c:ℤ)<x S ∧ x S<(L:ℤ) ∧ (R:ℤ)<p S ∧ p S≤(N:ℤ) ∧
      IntrinsicPair (c:ℤ) S {x S,p S} ∧
      (S ∩ Finset.Icc (x S) (p S) = {x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S))))
    (hE : ∀ S ∈ E, (c:ℤ)<j S ∧ j S≤(L:ℤ) ∧ (R:ℤ)<q S ∧ q S≤(N:ℤ) ∧ S = Finset.Icc (j S) (q S)) :
    C.card+E.card+1 ≤ (L-c)*(N-R)+(L-c) := by
  classical
  let I := Finset.Ioc (c:ℤ) (L:ℤ)
  let HC (i : ℤ) := C.filter (fun S => x S = i)
  let Hat (i : ℤ) := (HC i).filter (fun S => S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  let Bar (i : ℤ) := (HC i).filter (fun S => ¬S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  let ER (i : ℤ) := E.filter (fun S => j S = i)
  let Active := I.filter (fun i => (ER i).Nonempty)
  have hHCC : ∀ i, HC i ⊆ C := fun i => Finset.filter_subset _ _
  have hHatHC : ∀ i, Hat i ⊆ HC i := fun i => Finset.filter_subset _ _
  have hBarHC : ∀ i, Bar i ⊆ HC i := fun i => Finset.filter_subset _ _
  have hERE : ∀ i, ER i ⊆ E := fun i => Finset.filter_subset _ _
  have hHCspec : ∀ i, ∀ S ∈ HC i, (R:ℤ)<p S ∧ p S≤(N:ℤ) ∧ IntrinsicPair (c:ℤ) S {i,p S} := by
    intro i S hS
    obtain ⟨hSC,hxi⟩ := Finset.mem_filter.mp hS
    have hh := hC S hSC
    exact ⟨hh.2.2.1,hh.2.2.2.1,by simpa only [hxi] using hh.2.2.2.2.1⟩
  have hHCcard : ∀ i, (HC i).card ≤ N-R := by
    intro i
    have hh := actual_witness_row_card hF ((hHCC i).trans hCF)
      (fun S hS => hc S (hHCC i hS)) (fun S => p S.val)
      (fun S => (hHCspec i S.val S.property).2.2)
      (fun S => Finset.mem_Icc.mpr
        ⟨(hHCspec i S.val S.property).1,(hHCspec i S.val S.property).2.1⟩)
    simp only [Int.card_Icc] at hh
    omega
  have hpartition : ∀ i, (Hat i).card+(Bar i).card = (HC i).card := by
    intro i
    exact Finset.card_filter_add_card_filter_not (s := HC i)
      (fun S => S ∩ Finset.Icc (x S) (p S) = {x S,p S})
  have hcuts : ∀ i ∈ Active, ∃ l:ℤ, (R:ℤ)<l ∧ l≤N ∧
      (∃ T ∈ ER i, T = Finset.Icc i l) ∧ (Bar i).card+(ER i).card≤((N:ℤ)-l+1).toNat := by
    intro i hi
    obtain ⟨hiI,hne⟩ := Finset.mem_filter.mp hi
    have hci : (c:ℤ)< i := (Finset.mem_Ioc.mp hiI).1
    apply actual_bar_interval_row_cut hci (by have hh:=(Finset.mem_Ioc.mp hiI).2;exact hh.trans (by exact_mod_cast hLR)) hF (((hBarHC i).trans (hHCC i)).trans hCF)
      ((hERE i).trans hEF) (fun S hS => hc S (hHCC i (hBarHC i hS))) (fun S => p S.val)
      (fun S => (hHCspec i S.val (hBarHC i S.property)).2.2)
      (fun S => ⟨(hHCspec i S.val (hBarHC i S.property)).1,
        (hHCspec i S.val (hBarHC i S.property)).2.1⟩) ?_ ?_ hne
    · intro S
      have hSi := hBarHC i S.property
      have hxi := (Finset.mem_filter.mp hSi).2
      have hcases := (hC S.val (hHCC i hSi)).2.2.2.2.2
      have hcrooked := hcases.resolve_left (Finset.mem_filter.mp S.property).2
      simpa only [hxi] using hcrooked
    · intro S hS
      obtain ⟨hSE,hji⟩ := Finset.mem_filter.mp hS
      have hh := hE S hSE
      exact ⟨q S,hh.2.2.1,hh.2.2.2.1,by simpa only [hji] using hh.2.2.2.2⟩
  have hBarE : ∀ i ∈ Active, (Bar i).card+(ER i).card ≤ N-R := by
    intro i hi
    obtain ⟨l,hRl,hlN,_hT,hcut⟩ := hcuts i hi
    omega
  have hcross : ∀ u ∈ Active, ∀ v ∈ Active, u < v →
      (Hat u).card+((Bar v).card+(ER v).card) ≤ (N-R)+1 := by
    intro u _hu v hv huv
    obtain ⟨l,hRl,hlN,⟨T,hT,hTrep⟩,hcut⟩ := hcuts v hv
    have hHatBound : (Hat u).card ≤ (Finset.Icc ((R:ℤ)+1) l).card := by
      apply actual_witness_row_card hF (((hHatHC u).trans (hHCC u)).trans hCF)
        (fun S hS => hc S (hHCC u (hHatHC u hS))) (fun S => p S.val)
        (fun S => (hHCspec u S.val (hHatHC u S.property)).2.2)
      intro S
      have hSC := hHCC u (hHatHC u S.property)
      have hxu := (Finset.mem_filter.mp (hHatHC u S.property)).2
      have hcrop : S.val ∩ Finset.Icc u (p S.val) = {u,p S.val} := by
        simpa only [hxu] using (Finset.mem_filter.mp S.property).2
      have hmet : (S.val∩Finset.Icc v l).Nonempty := by
        have hcv : (c:ℤ)<v := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hv).1).1
        have hcT : (c:ℤ)∉T := by rw [hTrep];simp only [Finset.mem_Icc];omega
        have hST : S.val≠T := by intro he;exact hcT (he ▸ hc S.val hSC)
        have ha := hF.2 S.val (hCF hSC) T (hEF (hERE v hT)) hST
        obtain ⟨d,a,_,ha⟩ := (isAP_iff_exists_APAt _).mp ha
        exact ⟨a,by simpa only [hTrep] using ha⟩
      have hpl := actual_pair_crop_meets_later_interval hcrop hmet huv
      exact Finset.mem_Icc.mpr ⟨(hHCspec u S.val (hHatHC u S.property)).1,hpl⟩
    simp only [Int.card_Icc] at hHatBound
    omega
  have hinactive : ∀ i ∈ I \ Active, (Hat i).card+((Bar i).card+(ER i).card) ≤ N-R := by
    intro i hi
    obtain ⟨hiI,hiA⟩ := Finset.mem_sdiff.mp hi
    have hnone : ¬(ER i).Nonempty := by
      intro hn
      exact hiA (Finset.mem_filter.mpr ⟨hiI,hn⟩)
    have hz : ER i = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
    have hpart := hpartition i
    have hbound := hHCcard i
    simp only [hz,Finset.card_empty]
    omega
  have hCmaps : Set.MapsTo x (C : Set (Finset ℤ)) (I : Set ℤ) := by
    intro S hS
    have hh := hC S hS
    exact Finset.mem_Ioc.mpr ⟨hh.1,hh.2.1.le⟩
  have hEmaps : Set.MapsTo j (E : Set (Finset ℤ)) (I : Set ℤ) := by
    intro S hS
    have hh := hE S hS
    exact Finset.mem_Ioc.mpr ⟨hh.1,hh.2.1⟩
  have hCcount : C.card = ∑ i ∈ I, (HC i).card := Finset.card_eq_sum_card_fiberwise hCmaps
  have hEcount : E.card = ∑ i ∈ I, (ER i).card := Finset.card_eq_sum_card_fiberwise hEmaps
  have hsum : (∑ i ∈ I, ((Hat i).card+((Bar i).card+(ER i).card))) = C.card+E.card := by
    calc
      _ = ∑ i ∈ I, ((HC i).card+(ER i).card) := by
        apply Finset.sum_congr rfl
        intro i _hi
        have hh := hpartition i
        omega
      _ = (∑ i ∈ I, (HC i).card)+(∑ i ∈ I, (ER i).card) := Finset.sum_add_distrib
      _ = C.card+E.card := by rw [← hCcount,← hEcount]
  have hlastI : (L : ℤ) ∈ I := by
    apply Finset.mem_Ioc.mpr
    exact ⟨by exact_mod_cast hcL,le_rfl⟩
  have hlastHC : HC (L : ℤ)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨hSC,hx⟩ := Finset.mem_filter.mp hS
    have hh := (hC S hSC).2.1
    rw [hx] at hh
    exact lt_irrefl _ hh
  have hlastHat : Hat (L : ℤ)=∅ := by
    dsimp only [Hat]
    rw [hlastHC,Finset.filter_empty]
  have hlastBar : Bar (L : ℤ)=∅ := by
    dsimp only [Bar]
    rw [hlastHC,Finset.filter_empty]
  let A := insert (L : ℤ) Active
  have hAI : A ⊆ I := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hlastI
    · exact (Finset.mem_filter.mp hi).1
  have hJ : ∀ i∈A, (Bar i).card+(ER i).card≤N-R := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · by_cases ha : (L : ℤ)∈Active
      · exact hBarE _ ha
      · have hh := hinactive (L : ℤ) (Finset.mem_sdiff.mpr ⟨hlastI,ha⟩)
        simpa only [hlastHat,Finset.card_empty,Nat.zero_add] using hh
    · exact hBarE i hi
  have hcrossA : ∀ u∈A, ∀ v∈A, u<v →
      (Hat u).card+((Bar v).card+(ER v).card)≤N-R+1 := by
    intro u hu v hv huv
    rcases Finset.mem_insert.mp hu with rfl | hu
    · have hvL := (Finset.mem_Ioc.mp (hAI hv)).2
      omega
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : (L : ℤ)∈Active
      · exact hcross u hu (L : ℤ) ha huv
      · have hn : ¬(ER (L : ℤ)).Nonempty := by
          intro he
          exact ha (Finset.mem_filter.mpr ⟨hlastI,he⟩)
        have hz := Finset.not_nonempty_iff_eq_empty.mp hn
        have hh := (Finset.card_le_card (hHatHC u)).trans (hHCcard u)
        simpa only [hlastBar,hz,Finset.card_empty,Nat.zero_add,Nat.add_zero] using
          hh.trans (Nat.le_succ (N-R))
    · exact hcross u hu v hv huv
  have hinactiveA : ∀ i∈I\A, (Hat i).card+((Bar i).card+(ER i).card)≤N-R := by
    intro i hi
    obtain ⟨hiI,hiA⟩ := Finset.mem_sdiff.mp hi
    exact hinactive i (Finset.mem_sdiff.mpr
      ⟨hiI,fun h => hiA (Finset.mem_insert_of_mem h)⟩)
  have htotal := RightRows67702.total_last_zero hAI
    (fun i => (Hat i).card) (fun i => (Bar i).card+(ER i).card)
    (N-R) (L : ℤ) (Finset.mem_insert_self _ _)
    (fun i hi => (Finset.mem_Ioc.mp hi).2)
    (by simp only [hlastHat,Finset.card_empty]) hJ hcrossA hinactiveA
  rw [hsum] at htotal
  have hIcard : I.card=L-c := by simp only [I,Int.card_Ioc];omega
  rw [hIcard] at htotal
  exact htotal

#print axioms actual_CQ_EP_joint
end
end JSP233.RightJoint67702
