import Erdos272.Global.APPrepare49
import Erdos272.Counting.CornerJoint49
namespace JSP233.RightJoint50
open StarCompletion APGeometry PrivatePairExistence LongTerminal35 WitnessInterval43
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 5000000

theorem ordered_row_sum_le_max_tail (A : Finset ℤ) (H J : ℤ → ℕ) (X : ℕ) :
    (∀ i ∈ A, J i ≤ X+1) →
    (∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1) →
    ∀ t ∈ A, (∀ i ∈ A, i ≤ t) →
      (∑ i ∈ A, (H i+J i)) ≤ A.card*(X+1)+H t := by
  induction A using Finset.induction_on_max with
  | empty => simp
  | @insert a A hmax ih =>
    intro hJ hcross t ht htop
    have haA : a ∉ A := by intro ha; exact (lt_irrefl a) (hmax a ha)
    have hat : a ≤ t := htop a (Finset.mem_insert_self _ _)
    have hta : t = a := by
      rcases Finset.mem_insert.mp ht with heq | htA
      · exact heq
      · have hlt := hmax t htA
        omega
    subst t
    by_cases hne : A.Nonempty
    · let m := A.max' hne
      have hmA : m ∈ A := Finset.max'_mem A hne
      have hmmax : ∀ i ∈ A, i ≤ m := fun i hi => Finset.le_max' A i hi
      have hih := ih (fun i hi => hJ i (Finset.mem_insert_of_mem hi))
        (fun i hi j hj hij => hcross i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij) m hmA hmmax
      have hstep := hcross m (Finset.mem_insert_of_mem hmA) a
        (Finset.mem_insert_self _ _) (hmax m hmA)
      rw [Finset.sum_insert haA,Finset.card_insert_of_notMem haA]
      nlinarith only [hih,hstep]
    · have hAempty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      have hJa := hJ a (Finset.mem_insert_self _ _)
      simpa [hAempty,Nat.add_comm] using Nat.add_le_add_left hJa (H a)

theorem ordered_row_sum_le (A : Finset ℤ) (H J : ℤ → ℕ) (X : ℕ)
    (hH : ∀ i ∈ A, H i ≤ X) (hJ : ∀ i ∈ A, J i ≤ X)
    (hcross : ∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1) :
    (∑ i ∈ A, (H i+J i)) ≤ A.card*(X+1)+X := by
  by_cases hne : A.Nonempty
  · let t := A.max' hne
    have ht : t ∈ A := Finset.max'_mem A hne
    have hh := ordered_row_sum_le_max_tail A H J X
      (fun i hi => (hJ i hi).trans (Nat.le_succ X)) hcross t ht
      (fun i hi => Finset.le_max' A i hi)
    exact hh.trans (Nat.add_le_add_left (hH t ht) _)
  · have hz : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp only [hz,Finset.sum_empty,Finset.card_empty,Nat.zero_mul,Nat.zero_add,Nat.zero_le]

theorem ordered_row_total_le {I A : Finset ℤ} (hAI : A ⊆ I) (H J : ℤ → ℕ) (X : ℕ)
    (hH : ∀ i ∈ A, H i ≤ X) (hJ : ∀ i ∈ A, J i ≤ X)
    (hcross : ∀ i ∈ A, ∀ j ∈ A, i < j → H i+J j ≤ X+1)
    (hinactive : ∀ i ∈ I \ A, H i+J i ≤ X) :
    (∑ i ∈ I, (H i+J i)) ≤ I.card*X+I.card+X := by
  have hactive := ordered_row_sum_le A H J X hH hJ hcross
  have hrest : (∑ i ∈ I \ A, (H i+J i)) ≤ (I \ A).card*X := by
    simpa using Finset.sum_le_sum hinactive
  have hsum := Finset.sum_sdiff hAI (f := fun i => H i+J i)
  have hcards := Finset.card_sdiff_add_card_eq_card hAI
  have hAcard := Finset.card_le_card hAI
  nlinarith only [hactive,hrest,hsum,hcards,hAcard]


theorem actual_pair_crop_meets_later_interval {S : Finset ℤ} {i p j l : ℤ}
    (hcrop : S∩Finset.Icc i p={i,p}) (hmet : (S∩Finset.Icc j l).Nonempty)
    (hij : i<j) : p≤l := by
  by_contra hn
  obtain ⟨z,hz⟩ := hmet
  obtain ⟨hzS,hzI⟩ := Finset.mem_inter.mp hz
  obtain ⟨hjz,hzl⟩ := Finset.mem_Icc.mp hzI
  have hzCrop : z∈S∩Finset.Icc i p :=
    Finset.mem_inter.mpr ⟨hzS,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩
  rw [hcrop] at hzCrop
  simp only [Finset.mem_insert,Finset.mem_singleton] at hzCrop
  omega

theorem actual_crooked_crop_end_lt {S : Finset ℤ} {i p f : ℤ}
    (hbad : ¬IsAP (S∩Finset.Icc i p)) (hip : i≤p) (hi : i∈S)
    (hAP : IsAP (S∩Finset.Icc i f)) : f<p := by
  by_contra hn
  have hne : ((S∩Finset.Icc i f)∩Finset.Icc i p).Nonempty := by
    exact ⟨i,Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr
      ⟨hi,Finset.mem_Icc.mpr ⟨le_rfl,by omega⟩⟩,Finset.mem_Icc.mpr ⟨le_rfl,hip⟩⟩⟩
  have hh := isAP_inter_of_nonempty hAP (integer_interval_isAP i p hip) hne
  have heq : (S∩Finset.Icc i f)∩Finset.Icc i p=S∩Finset.Icc i p := by
    ext x
    simp only [Finset.mem_inter,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hS,hix,_⟩,_,hxp⟩
      exact ⟨hS,hix,hxp⟩
    · rintro ⟨hS,hix,hxp⟩
      exact ⟨⟨hS,hix,hxp.trans (by omega)⟩,hix,hxp⟩
  exact hbad (heq ▸ hh)

theorem actual_witness_row_card {N : ℕ} {c i u v : ℤ} {F H : Finset (Finset ℤ)}
    (hF : Legal (Ground N) F) (hHF : H⊆F) (hc : ∀S∈H,c∈S)
    (p : {S // S∈H}→ℤ) (hW : ∀S,IntrinsicPair c S.val {i,p S})
    (hp : ∀S,p S∈Finset.Icc u v) : H.card≤(Finset.Icc u v).card := by
  have hinj : Function.Injective p := by
    intro S T heq
    apply Subtype.ext
    apply actual_intrinsic_member_eq hF (hHF S.property) (hHF T.property)
      (hc S.val S.property) (hc T.val T.property) (hW S)
    rw [heq]
    exact (hW T).2.2.1
  have hh := Finset.card_le_card_of_injOn p
    (show Set.MapsTo p ((Finset.univ:Finset {S // S∈H}):Set {S // S∈H})
      (Finset.Icc u v:Set ℤ) from fun S _=>hp S) hinj.injOn
  simpa only [Finset.card_univ,Fintype.card_coe] using hh

theorem actual_interval_row_card {i u v : ℤ} {E : Finset (Finset ℤ)}
    (hrep : ∀S∈E,∃q∈Finset.Icc u v,S=Finset.Icc i q) :
    E.card≤(Finset.Icc u v).card := by
  have hsub : E⊆(Finset.Icc u v).image (fun q=>Finset.Icc i q) := by
    intro S hS
    obtain ⟨q,hq,hS⟩ := hrep S hS
    exact Finset.mem_image.mpr ⟨q,hq,hS.symm⟩
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

theorem actual_bar_interval_row_cut {N R : ℕ} {c j : ℤ} {F C E : Finset (Finset ℤ)}
    (hcj : c<j) (hjR : j≤(R:ℤ)) (hF : Legal (Ground N) F) (hCF : C ⊆ F) (hEF : E ⊆ F)
    (hc : ∀ S ∈ C, c ∈ S) (p : {S // S ∈ C} → ℤ)
    (hW : ∀ S, IntrinsicPair c S.val {j,p S})
    (hp : ∀ S, (R:ℤ)<p S ∧ p S≤N)
    (hCrop : ∀ S, ¬IsAP (S.val ∩ Finset.Icc j (p S)))
    (hrep : ∀ I ∈ E, ∃ f : ℤ, (R:ℤ)<f ∧ f≤N ∧ I = Finset.Icc j f)
    (hEne : E.Nonempty) :
    ∃ l : ℤ, (R:ℤ)<l ∧ l≤N ∧ (∃ I ∈ E, I = Finset.Icc j l) ∧
      C.card+E.card≤((N:ℤ)-l+1).toNat := by
  classical
  let Y := {I // I ∈ E}
  have hparam : ∀ I : Y, ∃ f : ℤ, (R:ℤ)<f ∧ f≤N ∧ I.val = Finset.Icc j f :=
    fun I => hrep I.val I.property
  choose q hRq hqN hqrep using hparam
  have hY : (Finset.univ : Finset Y).Nonempty := by
    obtain ⟨I,hI⟩ := hEne
    exact ⟨⟨I,hI⟩,Finset.mem_univ _⟩
  obtain ⟨I₀,_hI₀,hminq⟩ := Finset.exists_min_image Finset.univ q hY
  let l := q I₀
  refine ⟨l,hRq I₀,hqN I₀,⟨I₀.val,I₀.property,hqrep I₀⟩,?_⟩
  by_cases hCne : C.Nonempty
  · have hX : (Finset.univ : Finset {S // S ∈ C}).Nonempty := by
      obtain ⟨S,hS⟩ := hCne
      exact ⟨⟨S,hS⟩,Finset.mem_univ _⟩
    obtain ⟨K,_hK,hminp⟩ := Finset.exists_min_image Finset.univ p hX
    let m := p K
    have hqm : ∀ I : Y, q I < m := by
      intro I
      have hcI : c ∉ I.val := by
        rw [hqrep I]
        intro hh
        have hcj' := (Finset.mem_Icc.mp hh).1
        omega
      have hKI : K.val ≠ I.val := by
        intro heq
        exact hcI (heq ▸ hc K.val K.property)
      have hAP := hF.2 K.val (hCF K.property) I.val (hEF I.property) hKI
      apply actual_crooked_crop_end_lt (hCrop K) (hjR.trans (hp K).1.le)
        ((hW K).2.2.1 (by simp))
      simpa only [hqrep I] using hAP
    have hlm : l < m := hqm I₀
    have hmN : m ≤ N := (hp K).2
    have hCcard : C.card ≤ (Finset.Icc m N).card :=
      actual_witness_row_card hF hCF hc p hW (fun S => Finset.mem_Icc.mpr
        ⟨hminp S (Finset.mem_univ _),(hp S).2⟩)
    have hEcard : E.card ≤ (Finset.Icc l (m-1)).card := by
      apply actual_interval_row_card
      intro I hI
      let T : Y := ⟨I,hI⟩
      exact ⟨q T,Finset.mem_Icc.mpr ⟨hminq T (Finset.mem_univ _),by have hh := hqm T; omega⟩,
        hqrep T⟩
    simp only [Int.card_Icc] at hCcard hEcard
    omega
  · have hCzero : C = ∅ := Finset.not_nonempty_iff_eq_empty.mp hCne
    have hEcard : E.card ≤ (Finset.Icc l N).card := by
      apply actual_interval_row_card
      intro I hI
      let T : Y := ⟨I,hI⟩
      exact ⟨q T,Finset.mem_Icc.mpr ⟨hminq T (Finset.mem_univ _),hqN T⟩,hqrep T⟩
    have hlN : l ≤ N := hqN I₀
    simp only [hCzero,Finset.card_empty,Nat.zero_add]
    simp only [Int.card_Icc] at hEcard
    omega


theorem actual_CQ_EP_joint {N c L R : ℕ} {F C E : Finset (Finset ℤ)}
    (hLR : L ≤ R) (hRN : R ≤ N) (hF : Legal (Ground N) F)
    (hCF : C ⊆ F) (hEF : E ⊆ F) (hc : ∀ S ∈ C, (c:ℤ)∈S)
    (x p j q : Finset ℤ → ℤ)
    (hC : ∀ S ∈ C, (c:ℤ)<x S ∧ x S<(L:ℤ) ∧ (R:ℤ)<p S ∧ p S≤(N:ℤ) ∧
      IntrinsicPair (c:ℤ) S {x S,p S} ∧
      (S ∩ Finset.Icc (x S) (p S) = {x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S))))
    (hE : ∀ S ∈ E, (c:ℤ)<j S ∧ j S≤(L:ℤ) ∧ (R:ℤ)<q S ∧ q S≤(N:ℤ) ∧ S = Finset.Icc (j S) (q S)) :
    C.card+E.card ≤ (L-c)*(N-R)+2*N := by
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
  have hHat : ∀ i ∈ Active, (Hat i).card ≤ N-R := by
    intro i _hi
    exact (Finset.card_le_card (hHatHC i)).trans (hHCcard i)
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
  have htotal := ordered_row_total_le (show Active ⊆ I from Finset.filter_subset _ _)
    (fun i => (Hat i).card) (fun i => (Bar i).card+(ER i).card) (N-R) hHat hBarE hcross hinactive
  rw [hsum] at htotal
  have hIcard : I.card=L-c := by simp only [I,Int.card_Ioc];omega
  rw [hIcard] at htotal
  omega


def RightCorners (F : Finset (Finset ℤ)) (c L R : ℕ)
    (x p : Finset ℤ→ℤ) : Finset (Finset ℤ) :=
  F.filter (fun S=>(c:ℤ)∈S ∧ (c:ℤ)<x S ∧ x S<(L:ℤ) ∧ (R:ℤ)<p S ∧
    IntrinsicPair c S {x S,p S} ∧
    (S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S))))

def RightIntervals (F : Finset (Finset ℤ)) (c L R : ℕ) : Finset (Finset ℤ) :=
  F.filter (fun S=>∃a b:ℤ,(c:ℤ)<a ∧ a≤L ∧ (R:ℤ)<b ∧ S=Finset.Icc a b)

theorem actual_right_filters_joint {N c L R : ℕ} {F : Finset (Finset ℤ)}
    (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F) (x p : Finset ℤ→ℤ) :
    (RightCorners F c L R x p).card+(RightIntervals F c L R).card≤(L-c)*(N-R)+2*N := by
  have hex : ∀S:Finset ℤ,∃a b:ℤ,S∈RightIntervals F c L R→
      (c:ℤ)<a ∧ a≤L ∧ (R:ℤ)<b ∧ S=Finset.Icc a b := by
    intro S
    by_cases hS:S∈RightIntervals F c L R
    · obtain ⟨a,b,hh⟩ := (Finset.mem_filter.mp hS).2
      exact ⟨a,b,fun _=>hh⟩
    · exact ⟨0,0,fun hh=>False.elim (hS hh)⟩
  choose a b hab using hex
  apply actual_CQ_EP_joint hLR hRN hF (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    (fun S hS=>(Finset.mem_filter.mp hS).2.1) x p a b
  · intro S hS
    obtain ⟨_,hcx,hxL,hRp,hw,hcrop⟩ := (Finset.mem_filter.mp hS).2
    have hpN := ((mem_ground N (p S)).mp
      (hF.1 S (Finset.mem_filter.mp hS).1 (hw.2.2.1 (by simp)))).2
    exact ⟨hcx,hxL,hRp,hpN,hw,hcrop⟩
  · intro S hS
    obtain ⟨hca,haL,hRb,hrep⟩ := hab S hS
    have hab' : a S≤b S := haL.trans (show (L:ℤ)≤R by exact_mod_cast hLR) |>.trans hRb.le
    have hbS : b S∈S := (Finset.ext_iff.mp hrep (b S)).mpr (Finset.mem_Icc.mpr ⟨hab',le_rfl⟩)
    have hbN := ((mem_ground N (b S)).mp (hF.1 S (Finset.mem_filter.mp hS).1 hbS)).2
    exact ⟨hca,haL,hRb,hbN,hrep⟩

theorem actual_selected_right_joint {N c L R : ℕ} {F C : Finset (Finset ℤ)}
    (hLR : L≤R) (hRN : R≤N) (hF : Legal (Ground N) F) (hCF : C⊆F)
    (hc : ∀S∈C,(c:ℤ)∈S) (x p : Finset ℤ→ℤ)
    (hW : ∀S∈C,IntrinsicPair c S {x S,p S})
    (hCrop : ∀S∈C,(c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
      S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S))) :
    (C.filter (fun S=>(c:ℤ)<x S ∧ x S<(L:ℤ) ∧ (R:ℤ)<p S)).card+
      (RightIntervals F c L R).card≤(L-c)*(N-R)+2*N := by
  have hs : C.filter (fun S=>(c:ℤ)<x S ∧ x S<(L:ℤ) ∧ (R:ℤ)<p S)⊆
      RightCorners F c L R x p := by
    intro S hS
    obtain ⟨hSC,hcx,hxL,hRp⟩ := Finset.mem_filter.mp hS
    exact Finset.mem_filter.mpr ⟨hCF hSC,hc S hSC,hcx,hxL,hRp,hW S hSC,
      hCrop S hSC hcx hxL hRp⟩
  exact (Nat.add_le_add_right (Finset.card_le_card hs) _).trans
    (actual_right_filters_joint hLR hRN hF x p)

#print axioms ordered_row_sum_le_max_tail
#print axioms ordered_row_sum_le
#print axioms ordered_row_total_le
#print axioms actual_pair_crop_meets_later_interval
#print axioms actual_crooked_crop_end_lt
#print axioms actual_witness_row_card
#print axioms actual_interval_row_card
#print axioms actual_bar_interval_row_cut
#print axioms actual_CQ_EP_joint
#print axioms actual_right_filters_joint
#print axioms actual_selected_right_joint
end
end JSP233.RightJoint50
