import Erdos272.Global.APPrepare49
import Erdos272.Counting.CornerJoint49
import Erdos272.Counting.APExterior50
import Erdos272.Counting.RightJoint50

/-! Actual prepared classes and the same-family corner reduction. -/
namespace JSP233.PreparedClasses50
open StarCompletion APGeometry APCount41 APPrepare49 PreparedWitness48
open LongTerminal35 WitnessInterval43 RestrictedWitness44 DenseDeletion40 FamilyReflect43
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def CM (C : Finset (Finset ℤ)) (p : Finset ℤ→ℤ) (R : ℕ) :=
  C.filter (fun S=>p S≤(R:ℤ))
def CL (C : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (c R : ℕ) :=
  C.filter (fun S=>(R:ℤ)<p S ∧ x S<(c:ℤ))
def CQ (C : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (c L R : ℕ) :=
  C.filter (fun S=>(R:ℤ)<p S ∧ (c:ℤ)<x S ∧ x S<(L:ℤ))
def CX (C : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (L R : ℕ) :=
  C.filter (fun S=>(L:ℤ)<x S ∧ x S≤(R:ℤ) ∧ (R:ℤ)<p S)

def EM (E : Finset (Finset ℤ)) (c R : ℕ) :=
  E.filter (fun S=>(c:ℤ)∈S ∧ High S≤(R:ℤ))
def EX (E : Finset (Finset ℤ)) (R : ℕ) :=
  E.filter (fun S=>2≤Step S ∧ (R:ℤ)≤High S)
def EI (E : Finset (Finset ℤ)) (c R : ℕ) :=
  E.filter (fun S=>(c:ℤ)∈S ∧ Step S=1 ∧ (R:ℤ)<High S)
def EP (E : Finset (Finset ℤ)) (c R : ℕ) :=
  E.filter (fun S=>(c:ℤ)∉S ∧ Step S=1 ∧ (R:ℤ)<High S)
def EB (E : Finset (Finset ℤ)) (c R : ℕ) :=
  E.filter (fun S=>(c:ℤ)∉S ∧ Step S=1 ∧ High S=(R:ℤ))

theorem actual_step_one_Icc {S : Finset ℤ} (hAP : IsAP S) (hstep : Step S=1) :
    S=Finset.Icc (Low S) (High S) := by
  have hne := isAP_nonempty hAP
  obtain ⟨_,p,hp⟩ := actual_step hAP
  rw [hstep,Nat.cast_one] at hp
  ext z
  constructor
  · intro hz
    exact Finset.mem_Icc.mpr ⟨(low_spec hne).2 z hz,(high_spec hne).2 z hz⟩
  · intro hz
    obtain ⟨hl,hh⟩ := Finset.mem_Icc.mp hz
    exact apAt_fill hp (low_spec hne).1 (high_spec hne).1 hl hh (one_dvd _)

theorem actual_crooked_class_cover {C : Finset (Finset ℤ)} {c L R : ℕ}
    (x p : Finset ℤ→ℤ) (hcL : c<L)
    (hW : ∀ S∈C,IntrinsicPair c S {x S,p S} ∧ x S≤(R:ℤ) ∧ x S≠(L:ℤ)) :
    C⊆CM C p R∪CL C x p c R∪CQ C x p c L R∪CX C x p L R := by
  intro S hS
  obtain ⟨hw,hxR,hxL⟩ := hW S hS
  have hxc : x S≠(c:ℤ) := by
    intro he
    apply hw.2.1
    simp [←he]
  have hcLZ : (c:ℤ)<L := by exact_mod_cast hcL
  by_cases hpR : p S≤(R:ℤ)
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hS,hpR⟩)))
  · have hRp : (R:ℤ)<p S := by omega
    by_cases hxc' : x S<(c:ℤ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hS,hRp,hxc'⟩)))
    · have hcx : (c:ℤ)<x S := by omega
      by_cases hxL' : x S<(L:ℤ)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hS,hRp,hcx,hxL'⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,by omega,hxR,hRp⟩)

theorem actual_crooked_class_count {C : Finset (Finset ℤ)} {c L R : ℕ}
    (x p : Finset ℤ→ℤ) (hcL : c<L)
    (hW : ∀ S∈C,IntrinsicPair c S {x S,p S} ∧ x S≤(R:ℤ) ∧ x S≠(L:ℤ)) :
    C.card≤(CM C p R).card+(CL C x p c R).card+(CQ C x p c L R).card+(CX C x p L R).card := by
  have h := Finset.card_le_card (actual_crooked_class_cover x p hcL hW)
  have h1 := Finset.card_union_le (CM C p R) (CL C x p c R)
  have h2 := Finset.card_union_le (CM C p R∪CL C x p c R) (CQ C x p c L R)
  have h3 := Finset.card_union_le (CM C p R∪CL C x p c R∪CQ C x p c L R) (CX C x p L R)
  omega

theorem actual_AP_class_cover {E : Finset (Finset ℤ)} {c R : ℕ}
    (hstep : ∀ S∈E,0<Step S)
    (hout : ∀ S∈E,(c:ℤ)∉S→(R:ℤ)≤High S) :
    E⊆EM E c R∪EX E R∪EI E c R∪EP E c R∪EB E c R := by
  intro S hS
  by_cases hcS : (c:ℤ)∈S
  · by_cases hh : High S≤(R:ℤ)
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS,hcS,hh⟩))))
    · have hRh : (R:ℤ)<High S := by omega
      by_cases hd : Step S=1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,hcS,hd,hRh⟩)))
      · have hd2 : 2≤Step S := by have := hstep S hS;omega
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,hd2,hRh.le⟩))))
  · have hRh := hout S hS hcS
    by_cases hd : Step S=1
    · by_cases hh : High S=(R:ℤ)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,hcS,hd,hh⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hS,hcS,hd,by omega⟩))
    · have hd2 : 2≤Step S := by have := hstep S hS;omega
      exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS,hd2,hRh⟩))))

theorem actual_AP_class_count {E : Finset (Finset ℤ)} {c R : ℕ}
    (hstep : ∀ S∈E,0<Step S)
    (hout : ∀ S∈E,(c:ℤ)∉S→(R:ℤ)≤High S) :
    E.card≤(EM E c R).card+(EX E R).card+(EI E c R).card+(EP E c R).card+(EB E c R).card := by
  have h := Finset.card_le_card (actual_AP_class_cover hstep hout)
  have h1 := Finset.card_union_le (EM E c R) (EX E R)
  have h2 := Finset.card_union_le (EM E c R∪EX E R) (EI E c R)
  have h3 := Finset.card_union_le (EM E c R∪EX E R∪EI E c R) (EP E c R)
  have h4 := Finset.card_union_le (EM E c R∪EX E R∪EI E c R∪EP E c R) (EB E c R)
  omega

theorem actual_prepared_AP_class_count {F : Finset (Finset ℤ)} {c L R : ℕ}
    (houtside : ∀ S∈F,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (PreparedAP F c L).card≤(EM (PreparedAP F c L) c R).card+
      (EX (PreparedAP F c L) R).card+(EI (PreparedAP F c L) c R).card+
      (EP (PreparedAP F c L) c R).card+(EB (PreparedAP F c L) c R).card := by
  apply actual_AP_class_count
  · intro S hS
    exact (actual_step (actual_prepared_AP_member hS).2.1).1
  · intro S hS hcS
    exact (actual_prepared_avoider_support houtside hS hcS).2

theorem actual_EI_interval {N : ℕ} {F : Finset (Finset ℤ)} {P S : Finset ℤ} {c L R : ℕ}
    (hF : Legal (Ground N) F) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hS : S∈EI (PreparedAP F c L) c R) :
    Low S<(c:ℤ) ∧ (R:ℤ)<High S ∧ S=Finset.Icc (Low S) (High S) := by
  obtain ⟨hSE,hcS,hstep,hhigh⟩ := Finset.mem_filter.mp hS
  have hAP := (actual_prepared_AP_member hSE).2.1
  exact ⟨(actual_prepared_root_support hF hP hLP hSE hcS).1,hhigh,actual_step_one_Icc hAP hstep⟩

theorem actual_avoiding_interval {F : Finset (Finset ℤ)} {S : Finset ℤ} {c L R : ℕ}
    (hcR : c<R)
    (houtside : ∀ S∈F,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hS : S∈PreparedAP F c L) (hcS : (c:ℤ)∉S) (hstep : Step S=1) :
    (c:ℤ)<Low S ∧ Low S≤(L:ℤ) ∧ (R:ℤ)≤High S ∧ S=Finset.Icc (Low S) (High S) := by
  have hAP := (actual_prepared_AP_member hS).2.1
  have hr := actual_step_one_Icc hAP hstep
  obtain ⟨hl,hh⟩ := actual_prepared_avoider_support houtside hS hcS
  have hcRZ : (c:ℤ)<R := by exact_mod_cast hcR
  have hcl : (c:ℤ)<Low S := by
    by_contra hn
    apply hcS
    rw [hr]
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  exact ⟨hcl,hl,hh,hr⟩

theorem actual_EP_interval {N c L R : ℕ} {F : Finset (Finset ℤ)} {S : Finset ℤ}
    (hF : Legal (Ground N) F) (hcR : c<R)
    (houtside : ∀ S∈F,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hS : S∈EP (PreparedAP F c L) c R) :
    (c:ℤ)<Low S ∧ Low S≤(L:ℤ) ∧ (R:ℤ)<High S ∧ High S≤(N:ℤ) ∧
      S=Finset.Icc (Low S) (High S) := by
  obtain ⟨hSE,hcS,hd,hRh⟩ := Finset.mem_filter.mp hS
  obtain ⟨hcl,hl,_,hr⟩ := actual_avoiding_interval hcR houtside hSE hcS hd
  have hmem := actual_prepared_AP_member hSE
  have hne := isAP_nonempty hmem.2.1
  have hhN := (mem_ground N (High S)).mp (hF.1 S hmem.1 (high_spec hne).1)
  exact ⟨hcl,hl,hRh,hhN.2,hr⟩

theorem actual_EX_endpoints {N c L R : ℕ} {F : Finset (Finset ℤ)} {P S : Finset ℤ}
    (hF : Legal (Ground N) F) (hcL : c<L) (hP : P∈F) (hLP : ∀z∈P,(L:ℤ)≤z)
    (houtside : ∀ S∈F,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hS : S∈EX (PreparedAP F c L) R) :
    S∈F ∧ IsAP S ∧ 4≤S.card ∧ 2≤Step S ∧ Low S≤(L:ℤ) ∧ (R:ℤ)≤High S := by
  obtain ⟨hSE,hd,hRh⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hAP,hsize,_⟩ := actual_prepared_AP_member hSE
  have hl : Low S≤(L:ℤ) := by
    by_cases hcS : (c:ℤ)∈S
    · have hh := (actual_prepared_root_support hF hP hLP hSE hcS).1
      have hcLZ : (c:ℤ)<L := by exact_mod_cast hcL
      omega
    · exact (actual_prepared_avoider_support houtside hSE hcS).1
  exact ⟨hSF,hAP,hsize,hd,hl,hRh⟩

theorem actual_EB_count {F : Finset (Finset ℤ)} {c L R : ℕ}
    (hcR : c<R)
    (houtside : ∀ S∈F,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    (EB (PreparedAP F c L) c R).card≤L-c := by
  let B := EB (PreparedAP F c L) c R
  have hB : ∀S∈B,(c:ℤ)<Low S ∧ Low S≤(L:ℤ) ∧
      S=Finset.Icc (Low S) (R:ℤ) := by
    intro S hS
    obtain ⟨hSE,hcS,hd,hh⟩ := Finset.mem_filter.mp hS
    obtain ⟨hcl,hl,_,hr⟩ := actual_avoiding_interval hcR houtside hSE hcS hd
    exact ⟨hcl,hl,by simpa only [hh] using hr⟩
  have hmaps : Set.MapsTo Low (B:Set (Finset ℤ)) (Finset.Ioc (c:ℤ) (L:ℤ):Set ℤ) := by
    intro S hS
    exact Finset.mem_Ioc.mpr ⟨(hB S hS).1,(hB S hS).2.1⟩
  have hinj : Set.InjOn Low (B:Set (Finset ℤ)) := by
    intro S hS T hT he
    rw [(hB S hS).2.2,(hB T hT).2.2,he]
  have hh := Finset.card_le_card_of_injOn Low hmaps hinj
  have hi : (Finset.Ioc (c:ℤ) (L:ℤ)).card=L-c := by
    simp only [Int.card_Ioc]
    omega
  exact hh.trans_eq hi

theorem actual_prepared_corner_reduction {N c L R : ℕ} {P : Finset ℤ}
    {G : Finset (Finset ℤ)} (x p : Finset ℤ→ℤ)
    (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R)
    (hP : P∈G) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hroot : ∀ S∈G,¬IsAP S→(c:ℤ)∈S)
    (houtside : ∀ S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hW : ∀ S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S} ∧
      x S≤(R:ℤ) ∧ x S≠(L:ℤ)) :
    (PreparedCrooked G c L).card+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(CQ (PreparedCrooked G c L) x p c L R).card+
      (EM (PreparedAP G c L) c R).card+(EX (PreparedAP G c L) R).card+
      (EP (PreparedAP G c L) c R).card+(EB (PreparedAP G c L) c R).card+
      c*(N-R)+(R-L)*(N-R) := by
  let C := PreparedCrooked G c L
  let E := PreparedAP G c L
  have hCG : C⊆G := (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hEG : E⊆G := fun _ hS=>(actual_prepared_AP_member hS).1
  have hbad : ∀S∈C,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
  have hc : ∀S∈C,(c:ℤ)∈S := fun S hS=>hroot S (hCG hS) (hbad S hS)
  have hleft : (CL C x p c R).card+(EI E c R).card≤c*(N-R) := by
    apply CornerJoint49.actual_left_interval_joint (by omega) hG
      ((Finset.filter_subset _ _).trans hCG) ((Finset.filter_subset _ _).trans hEG)
    · exact fun S hS=>hc S (Finset.mem_filter.mp hS).1
    · exact fun S hS=>hbad S (Finset.mem_filter.mp hS).1
    · intro S hS
      obtain ⟨hSC,hRp,hxc⟩ := Finset.mem_filter.mp hS
      exact ⟨x S,p S,hxc,hRp,(hW S hSC).1⟩
    · intro S hS
      obtain ⟨hl,hh,he⟩ := actual_EI_interval hG hP hLP hS
      exact ⟨Low S,High S,hl,hh,he⟩
  have hfar : (CX C x p L R).card≤(R-L)*(N-R) := by
    apply CornerJoint49.actual_selected_far_rectangle x p hG hCG hc hbad
    exact fun S hS=>(hW S hS).1
  have hC := actual_crooked_class_count x p hcL hW
  have hE := actual_prepared_AP_class_count houtside
  change C.card+E.card≤_
  change C.card≤_ at hC
  change E.card≤_ at hE
  dsimp only [C,E] at hleft hfar hC hE ⊢
  omega

def Residual (G : Finset (Finset ℤ)) (x p : Finset ℤ→ℤ) (c L R : ℕ) : ℕ :=
  (CM (PreparedCrooked G c L) p R).card+(CQ (PreparedCrooked G c L) x p c L R).card+
  (EM (PreparedAP G c L) c R).card+(EX (PreparedAP G c L) R).card+
  (EP (PreparedAP G c L) c R).card+(EB (PreparedAP G c L) c R).card

theorem actual_prepared_right_joint {N c L R : ℕ} {G : Finset (Finset ℤ)}
    (x p : Finset ℤ→ℤ) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hW : ∀S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S} ∧
      ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) :
    (CQ (PreparedCrooked G c L) x p c L R).card+(EP (PreparedAP G c L) c R).card≤
      (L-c)*(N-R)+2*N := by
  let C := PreparedCrooked G c L
  let E := PreparedAP G c L
  have hCG : C⊆G := (Finset.filter_subset _ _).trans ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
  have hEG : E⊆G := fun _ hS=>(actual_prepared_AP_member hS).1
  have hbad : ∀S∈C,¬IsAP S := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2
  apply RightJoint50.actual_CQ_EP_joint hLR hRN hG
    ((Finset.filter_subset _ _).trans hCG) ((Finset.filter_subset _ _).trans hEG)
    (fun S hS=>hroot S (hCG (Finset.mem_filter.mp hS).1) (hbad S (Finset.mem_filter.mp hS).1))
    x p Low High
  · intro S hS
    obtain ⟨hSC,hRp,hcx,hxL⟩ := Finset.mem_filter.mp hS
    have hw := (hW S hSC).1
    have hpN := ((mem_ground N (p S)).mp (hG.1 S (hCG hSC) (hw.2.2.1 (by simp)))).2
    exact ⟨hcx,hxL,hRp,hpN,hw,(hW S hSC).2 hcx hxL hRp⟩
  · intro S hS
    exact actual_EP_interval hG (by omega) houtside hS

theorem actual_prepared_EX_count {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hP : P∈G) (hLP : ∀z∈P,(L:ℤ)≤z)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v) :
    ((EX (PreparedAP G c L) R).card:ℝ)≤
      (2/3)*(L:ℝ)*(N-R)+2*N*HarmonicAbel29.Harmonic N+N := by
  have hmember := fun S hS=>actual_EX_endpoints hG hcL hP hLP houtside (S:=S) hS
  apply APExterior50.actual_selected_exterior_count hG (by omega) hRN
    (fun S hS=>(hmember S hS).1)
    (fun S hS=>(hmember S hS).2.1)
  · intro S hS
    have hh := (hmember S hS).2.2.1
    omega
  · exact fun S hS=>(hmember S hS).2.2.2.1
  · exact fun S hS=>(hmember S hS).2.2.2.2

theorem actual_prepared_middle_reduction {N c L R : ℕ} {G : Finset (Finset ℤ)} {P : Finset ℤ}
    (x p : Finset ℤ→ℤ) (hG : Legal (Ground N) G) (hcL : c<L) (hLR : L≤R) (hRN : R≤N)
    (hP : P∈G) (hLP : ∀z∈P,(L:ℤ)≤z)
    (hroot : ∀S∈G,¬IsAP S→(c:ℤ)∈S)
    (houtside : ∀S∈G,(c:ℤ)∉S→(∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v)
    (hW : ∀S∈PreparedCrooked G c L,IntrinsicPair c S {x S,p S} ∧ x S≤(R:ℤ) ∧ x S≠(L:ℤ) ∧
      ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
        S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) :
    ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      ((R:ℝ)+(2/3)*L)*(N-R)+2*N*HarmonicAbel29.Harmonic N+3*N+(L-c:ℕ) := by
  have hcorner := actual_prepared_corner_reduction x p hG hcL hLR hP hLP hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.1,(hW S hS).2.2.1⟩)
  have hright := actual_prepared_right_joint x p hG hcL hLR hRN hroot houtside
    (fun S hS=>⟨(hW S hS).1,(hW S hS).2.2.2⟩)
  have hEB := actual_EB_count (by omega : c<R) houtside
  have hEX := actual_prepared_EX_count hG hcL hLR hRN hP hLP houtside
  have hcombined : (PreparedCrooked G c L).card+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+R*(N-R)+2*N+(L-c) := by
    have hpoly : c*(N-R)+(R-L)*(N-R)+(L-c)*(N-R)=R*(N-R) := by
      rw [←Nat.add_mul,←Nat.add_mul]
      congr 1
      omega
    omega
  have hreal : ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
      (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
      (EX (PreparedAP G c L) R).card+(R:ℝ)*(N-R)+2*N+(L-c:ℕ) := by
    have hh : ((PreparedCrooked G c L).card:ℝ)+(PreparedAP G c L).card≤
        (CM (PreparedCrooked G c L) p R).card+(EM (PreparedAP G c L) c R).card+
        (EX (PreparedAP G c L) R).card+(R*(N-R):ℕ)+(2*N:ℕ)+(L-c:ℕ) := by exact_mod_cast hcombined
    simpa only [Nat.cast_mul,Nat.cast_sub hRN,Nat.cast_ofNat] using hh
  nlinarith only [hreal,hEX]

theorem actual_original_corner_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃c∈Finset.Icc 1 N,∃L R:ℕ,c<L ∧ L≤R ∧ R≤N ∧
        (∀S∈Retained N 28 H,¬IsAP S→(c:ℤ)∈S) ∧
        (∃P∈Avoiders (Retained N 28 H) c,∀z∈P,(L:ℤ)≤z) ∧
        (∃T∈Avoiders (Retained N 28 H) c,∀z∈T,z≤(R:ℤ)) ∧
        (∀S∈Avoiders (Retained N 28 H) c,
          (∃a∈S,a≤(L:ℤ) ∧ ∀z∈S,a≤z) ∧ ∃b∈S,(R:ℤ)≤b ∧ ∀z∈S,z≤b) ∧
        ∃x p:Finset ℤ→ℤ,
          (∀S∈PreparedCrooked (Retained N 28 H) c L,
            IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤(R:ℤ) ∧ (L:ℤ)<p S ∧ x S≠(L:ℤ) ∧
            ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
              S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) ∧
          ((F.card:ℝ)≤Residual (Retained N 28 H) x p c L R+
            (c*(N-R)+(R-L)*(N-R):ℕ)+(Deleted N 28 F).card+
            (WitnessException (Ground N) c:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3) := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,_hAP,hP,hT,henv,
    _hCC,_hEE,_hdisj,_hlegal,hcount,_hstructure,x,p,hx⟩ :=
    actual_original_joint_preparation28 hN hF hcounter
  let k := c.toNat
  have hk : (k:ℤ)=c := Int.toNat_of_nonneg (by have hh := (mem_ground N c).mp hc;omega)
  rw [←hk] at hLc hroot hP hT henv hcount hx
  have hkI : k∈Finset.Icc 1 N := by
    have hh := (mem_ground N c).mp hc
    rw [←hk] at hh
    exact Finset.mem_Icc.mpr (by omega)
  have hkL : k<L := by exact_mod_cast hLc
  obtain ⟨P,hP,hLP⟩ := hP
  obtain ⟨hPF,hcP⟩ := Finset.mem_filter.mp hP
  have houtside : ∀S∈Retained N 28 H,(k:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    obtain ⟨⟨a,ha,haL,_⟩,b,hb,hRb,_⟩ := henv S (Finset.mem_filter.mpr ⟨hS,hcS⟩)
    exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
  have hbound := actual_prepared_corner_reduction x p (actual_retained_legal (r:=28) hLH)
    hkL hLR hPF hLP hroot houtside (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.1,(hx S hS).2.2.2.2.1⟩)
  have hboundR : ((PreparedCrooked (Retained N 28 H) k L).card:ℝ)+
      (PreparedAP (Retained N 28 H) k L).card≤Residual (Retained N 28 H) x p k L R+
      (k*(N-R)+(R-L)*(N-R):ℕ) := by
    dsimp only [Residual]
    have hn : (PreparedCrooked (Retained N 28 H) k L).card+
        (PreparedAP (Retained N 28 H) k L).card≤Residual (Retained N 28 H) x p k L R+
        (k*(N-R)+(R-L)*(N-R):ℕ) := by
      simpa only [Residual,Nat.add_assoc] using hbound
    exact_mod_cast hn
  have hfinal : (F.card:ℝ)≤Residual (Retained N 28 H) x p k L R+
      (k*(N-R)+(R-L)*(N-R):ℕ)+(Deleted N 28 F).card+
      (WitnessException (Ground N) k:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3 := by
    linarith only [hcount,hboundR]
  exact ⟨H,hHF,hLH,hcard,hD,hG,k,hkI,L,R,hkL,hLR,hRN,hroot,
    ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩,hLP⟩,hT,henv,x,p,hx,hfinal⟩

theorem actual_original_middle_reduction28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃H:Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃c∈Finset.Icc 1 N,∃L R:ℕ,c<L ∧ L≤R ∧ R≤N ∧
        (∀S∈Retained N 28 H,¬IsAP S→(c:ℤ)∈S) ∧
        (∃P∈Avoiders (Retained N 28 H) c,∀z∈P,(L:ℤ)≤z) ∧
        (∃T∈Avoiders (Retained N 28 H) c,∀z∈T,z≤(R:ℤ)) ∧
        (∀S∈Avoiders (Retained N 28 H) c,
          (∃a∈S,a≤(L:ℤ) ∧ ∀z∈S,a≤z) ∧ ∃b∈S,(R:ℤ)≤b ∧ ∀z∈S,z≤b) ∧
        ∃x p:Finset ℤ→ℤ,
          (∀S∈PreparedCrooked (Retained N 28 H) c L,
            IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤(R:ℤ) ∧ (L:ℤ)<p S ∧ x S≠(L:ℤ) ∧
            ((c:ℤ)<x S→x S<(L:ℤ)→(R:ℤ)<p S→
              S∩Finset.Icc (x S) (p S)={x S,p S} ∨ ¬IsAP (S∩Finset.Icc (x S) (p S)))) ∧
          ((F.card:ℝ)≤(CM (PreparedCrooked (Retained N 28 H) c L) p R).card+
            (EM (PreparedAP (Retained N 28 H) c L) c R).card+
            ((R:ℝ)+(2/3)*L)*(N-R)+(Deleted N 28 F).card+
            (WitnessException (Ground N) c:ℝ)+4*(N:ℝ)*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3) := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hP,hT,henv,x,p,hx,hcount⟩ :=
    actual_original_corner_reduction28 hN hF hcounter
  obtain ⟨P,hP,hLP⟩ := hP
  obtain ⟨hPF,hcP⟩ := Finset.mem_filter.mp hP
  have hlegal := actual_retained_legal (r:=28) hLH
  have houtside : ∀S∈Retained N 28 H,(c:ℤ)∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    obtain ⟨⟨a,ha,haL,_⟩,b,hb,hRb,_⟩ := henv S (Finset.mem_filter.mpr ⟨hS,hcS⟩)
    exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
  have hright := actual_prepared_right_joint x p hlegal hLc hLR hRN hroot houtside
    (fun S hS=>⟨(hx S hS).1,(hx S hS).2.2.2.2.2⟩)
  have hEX := actual_prepared_EX_count hlegal hLc hLR hRN hPF hLP houtside
  have hEB := actual_EB_count (by omega : c<R) houtside
  have hrightR : ((CQ (PreparedCrooked (Retained N 28 H) c L) x p c L R).card:ℝ)+
      (EP (PreparedAP (Retained N 28 H) c L) c R).card≤
      ((L-c)*(N-R):ℕ)+(2*N:ℕ) := by exact_mod_cast hright
  have hEBR : ((EB (PreparedAP (Retained N 28 H) c L) c R).card:ℝ)≤(L-c:ℕ) := by
    exact_mod_cast hEB
  have hpoly : c*(N-R)+(R-L)*(N-R)+(L-c)*(N-R)=R*(N-R) := by
    rw [←Nat.add_mul,←Nat.add_mul]
    congr 1
    omega
  have hpolyR : ((c*(N-R)+(R-L)*(N-R):ℕ):ℝ)+((L-c)*(N-R):ℕ)=(R:ℝ)*(N-R) := by
    rw [←Nat.cast_add,hpoly,Nat.cast_mul,Nat.cast_sub hRN]
  dsimp only [Residual] at hcount
  simp only [Nat.cast_add] at hcount
  simp only [Nat.cast_add] at hpolyR
  have htwoN : ((2*N:ℕ):ℝ)=2*(N:ℝ) := by norm_num
  have hfinal : (F.card:ℝ)≤(CM (PreparedCrooked (Retained N 28 H) c L) p R).card+
      (EM (PreparedAP (Retained N 28 H) c L) c R).card+
      ((R:ℝ)+(2/3)*L)*(N-R)+(Deleted N 28 F).card+
      (WitnessException (Ground N) c:ℝ)+4*(N:ℝ)*HarmonicAbel29.Harmonic N+24*N+(L-c:ℕ)+3 := by
    nlinarith only [hcount,hrightR,hEX,hEBR,hpolyR,htwoN]
  exact ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,
    ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩,hLP⟩,hT,henv,x,p,hx,hfinal⟩

#print axioms actual_step_one_Icc
#print axioms actual_crooked_class_cover
#print axioms actual_crooked_class_count
#print axioms actual_AP_class_cover
#print axioms actual_AP_class_count
#print axioms actual_prepared_AP_class_count
#print axioms actual_EI_interval
#print axioms actual_avoiding_interval
#print axioms actual_EP_interval
#print axioms actual_EX_endpoints
#print axioms actual_EB_count
#print axioms actual_prepared_corner_reduction
#print axioms actual_prepared_right_joint
#print axioms actual_prepared_EX_count
#print axioms actual_prepared_middle_reduction
#print axioms actual_original_corner_reduction28
#print axioms actual_original_middle_reduction28
end
end JSP233.PreparedClasses50
