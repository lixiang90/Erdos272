import Erdos272.Resources.PreparedWitness48
import Erdos272.Counting.APLinearCount49

/-! Actual AP endpoint preparation, with all filters on the same original family. -/
namespace JSP233.APPrepare49
open StarCompletion APGeometry APCount41 OutsideEnvelope43 PreparedWitness48
open LongTerminal35 WitnessInterval43 RestrictedWitness44 DenseDeletion40 FamilyReflect43 PrivatePairExistence
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def Progressions (F : Finset (Finset ℤ)) : Finset (Finset ℤ) := F.filter IsAP
def LargeAP (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (Progressions F).filter (fun S=>4≤S.card)
def SmallAP (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (Progressions F).filter (fun S=>¬4≤S.card)
def LowCut (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  (LargeAP F).filter (fun S=>Low S=c)
def AfterLow (F : Finset (Finset ℤ)) (c : ℤ) : Finset (Finset ℤ) :=
  (LargeAP F).filter (fun S=>Low S≠c)
def HighCut (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (AfterLow F c).filter (fun S=>High S=L)
def PreparedAP (F : Finset (Finset ℤ)) (c L : ℤ) : Finset (Finset ℤ) :=
  (AfterLow F c).filter (fun S=>High S≠L)

theorem actual_prepared_AP_member {F : Finset (Finset ℤ)} {S : Finset ℤ} {c L : ℤ}
    (hS : S∈PreparedAP F c L) :
    S∈F ∧ IsAP S ∧ 4≤S.card ∧ Low S≠c ∧ High S≠L := by
  obtain ⟨hSA,hhi⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSB,hlo⟩ := Finset.mem_filter.mp hSA
  obtain ⟨hSP,hsize⟩ := Finset.mem_filter.mp hSB
  obtain ⟨hSF,hAP⟩ := Finset.mem_filter.mp hSP
  exact ⟨hSF,hAP,hsize,hlo,hhi⟩

theorem actual_prepared_AP_subset (F : Finset (Finset ℤ)) (c L : ℤ) :
    PreparedAP F c L⊆Progressions F := by
  intro S hS
  obtain ⟨hSF,hAP,_⟩ := actual_prepared_AP_member hS
  exact Finset.mem_filter.mpr ⟨hSF,hAP⟩

theorem actual_AP_coordinates {N : ℕ} {S : Finset ℤ}
    (hsub : S⊆Ground N) (hAP : IsAP S) (htwo : 2≤S.card) :
    0<Step S ∧ Step S≤N ∧
      S=(Finset.range S.card).image (fun i:ℕ=>Low S+(Step S:ℤ)*(i:ℤ)) ∧
      High S=Low S+((S.card-1:ℕ):ℤ)*(Step S:ℤ) := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hd,p,hp⟩ := actual_step hAP
  have hrepr := apAt_eq_range hp hne
  have hspan := apAt_span_eq hp hne
  have hcast : ((S.card-1:ℕ):ℤ)=(S.card:ℤ)-1 := by omega
  refine ⟨hd,actual_step_bound hsub hAP htwo,?_,?_⟩
  · simpa only [Low,dif_pos hne] using hrepr
  · simp only [Low,High,dif_pos hne]
    rw [hcast]
    nlinarith only [hspan]

theorem actual_prepared_root_support {N : ℕ} {F : Finset (Finset ℤ)}
    {P S : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hP : P∈F) (hLP : ∀x∈P,L≤x)
    (hS : S∈PreparedAP F c L) (hcS : c∈S) : Low S<c ∧ L<High S := by
  obtain ⟨hSF,_hAP,_hsize,hlo,hhi⟩ := actual_prepared_AP_member hS
  have hne : S.Nonempty := ⟨c,hcS⟩
  have hlow := (low_spec hne).2 c hcS
  obtain ⟨z,hz⟩ := actual_inter_nonempty hF hSF hP hne
  obtain ⟨hzS,hzP⟩ := Finset.mem_inter.mp hz
  have hhigh := (high_spec hne).2 z hzS
  have hLz := hLP z hzP
  constructor <;>omega

theorem actual_prepared_avoider_support {F : Finset (Finset ℤ)} {S : Finset ℤ} {c L R : ℤ}
    (houtside : ∀S∈F,c∉S→(∃u∈S,u≤L) ∧ ∃v∈S,R≤v)
    (hS : S∈PreparedAP F c L) (hcS : c∉S) : Low S≤L ∧ R≤High S := by
  obtain ⟨hSF,hAP,_⟩ := actual_prepared_AP_member hS
  obtain ⟨⟨u,hu,huL⟩,v,hv,hRv⟩ := houtside S hSF hcS
  have hne : S.Nonempty := isAP_nonempty hAP
  exact ⟨((low_spec hne).2 u hu).trans huL,hRv.trans ((high_spec hne).2 v hv)⟩

theorem actual_prepared_AP_structure {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L R : ℤ}
    (hF : Legal (Ground N) F) (hP : P∈F) (hLP : ∀x∈P,L≤x)
    (houtside : ∀S∈F,c∉S→(∃u∈S,u≤L) ∧ ∃v∈S,R≤v) :
    ∀S∈PreparedAP F c L,0<Step S ∧ Step S≤N ∧ 4≤S.card ∧
      S=(Finset.range S.card).image (fun i:ℕ=>Low S+(Step S:ℤ)*(i:ℤ)) ∧
      High S=Low S+((S.card-1:ℕ):ℤ)*(Step S:ℤ) ∧
      (c∈S→Low S<c ∧ L<High S) ∧ (c∉S→Low S≤L ∧ R≤High S) := by
  intro S hS
  obtain ⟨hSF,hAP,hsize,_⟩ := actual_prepared_AP_member hS
  obtain ⟨hd,hdN,hrepr,hspan⟩ := actual_AP_coordinates (hF.1 S hSF) hAP (by omega)
  exact ⟨hd,hdN,hsize,hrepr,hspan,actual_prepared_root_support hF hP hLP hS,
    actual_prepared_avoider_support houtside hS⟩

theorem actual_AP_filter_partitions (F : Finset (Finset ℤ)) (c L : ℤ) :
    (LargeAP F).card+(SmallAP F).card=(Progressions F).card ∧
      (LowCut F c).card+(AfterLow F c).card=(LargeAP F).card ∧
      (HighCut F c L).card+(PreparedAP F c L).card=(AfterLow F c).card := by
  exact ⟨Finset.card_filter_add_card_filter_not (s:=Progressions F) (fun S=>4≤S.card),
    Finset.card_filter_add_card_filter_not (s:=LargeAP F) (fun S=>Low S=c),
    Finset.card_filter_add_card_filter_not (s:=AfterLow F c) (fun S=>High S=L)⟩

theorem actual_progression_crooked_partition (F : Finset (Finset ℤ)) :
    (Progressions F).card+(CrookedMembers F).card=F.card := by
  exact Finset.card_filter_add_card_filter_not (s:=F) IsAP

theorem actual_prepared_families_disjoint (F : Finset (Finset ℤ)) (c L : ℤ) :
    Disjoint (PreparedCrooked F c L) (PreparedAP F c L) := by
  apply Finset.disjoint_left.mpr
  intro S hC hE
  have hbad : ¬IsAP S :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1).2
  exact hbad (actual_prepared_AP_member hE).2.1

theorem actual_prepared_union_legal {N : ℕ} {F : Finset (Finset ℤ)} (c L : ℤ)
    (hF : Legal (Ground N) F) :
    Legal (Ground N) (PreparedCrooked F c L∪PreparedAP F c L) := by
  have hs : PreparedCrooked F c L∪PreparedAP F c L⊆F := by
    intro S hS
    rcases Finset.mem_union.mp hS with hC|hE
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hC).1).1).1
    · exact (actual_prepared_AP_member hE).1
  exact ⟨fun S hS=>hF.1 S (hs hS),fun S hS T hT hne=>hF.2 S (hs hS) T (hs hT) hne⟩

theorem actual_large_AP_member {F : Finset (Finset ℤ)} {S : Finset ℤ}
    (hS : S∈LargeAP F) : S∈F ∧ IsAP S ∧ 4≤S.card := by
  obtain ⟨hSA,hsize⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hAP⟩ := Finset.mem_filter.mp hSA
  exact ⟨hSF,hAP,hsize⟩

theorem actual_small_AP_member {F : Finset (Finset ℤ)} {S : Finset ℤ}
    (hS : S∈SmallAP F) : S∈F ∧ IsAP S ∧ S.card≤3 := by
  obtain ⟨hSA,hsize⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hAP⟩ := Finset.mem_filter.mp hSA
  exact ⟨hSF,hAP,by omega⟩

theorem actual_prepared_AP_count {N : ℕ} {F : Finset (Finset ℤ)} (c L : ℤ)
    (hF : Legal (Ground N) F) :
    ((Progressions F).card:ℝ)≤(PreparedAP F c L).card+
      2*(N:ℝ)*HarmonicAbel29.Harmonic N+20*N+3 := by
  have hSF : SmallAP F⊆F := fun _ hS=>(actual_small_AP_member hS).1
  have hlegal : Legal (Ground N) (SmallAP F) :=
    ⟨fun S hS=>hF.1 S (hSF hS),fun S hS T hT hn=>hF.2 S (hSF hS) T (hSF hT) hn⟩
  have hs := APLinearCount49.actual_small_AP_family_count hlegal
    (fun _ hS=>(actual_small_AP_member hS).2.1)
    (fun _ hS=>(actual_small_AP_member hS).2.2)
  have hD : ((LowCut F c).card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
    apply APLinearCount49.actual_fixed_low_count
    · intro S hS
      exact hF.1 S (actual_large_AP_member (Finset.mem_filter.mp hS).1).1
    · intro S hS
      exact (actual_large_AP_member (Finset.mem_filter.mp hS).1).2.1
    · intro S hS
      have hh := (actual_large_AP_member (Finset.mem_filter.mp hS).1).2.2
      omega
    · exact fun _ hS=>(Finset.mem_filter.mp hS).2
  have hJ : ((HighCut F c L).card:ℝ)≤(N:ℝ)*HarmonicAbel29.Harmonic N+N := by
    apply APLinearCount49.actual_fixed_high_count
    · intro S hS
      exact hF.1 S (actual_large_AP_member (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).1
    · intro S hS
      exact (actual_large_AP_member (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2.1
    · intro S hS
      have hh := (actual_large_AP_member (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2.2
      omega
    · exact fun _ hS=>(Finset.mem_filter.mp hS).2
  obtain ⟨h1,h2,h3⟩ := actual_AP_filter_partitions F c L
  have h1R : ((LargeAP F).card:ℝ)+(SmallAP F).card=(Progressions F).card := by exact_mod_cast h1
  have h2R : ((LowCut F c).card:ℝ)+(AfterLow F c).card=(LargeAP F).card := by exact_mod_cast h2
  have h3R : ((HighCut F c L).card:ℝ)+(PreparedAP F c L).card=(AfterLow F c).card := by exact_mod_cast h3
  have hsR : ((SmallAP F).card:ℝ)≤18*(N:ℝ)+3 := by exact_mod_cast hs
  linarith only [hD,hJ,h1R,h2R,h3R,hsR]

theorem actual_joint_preparation_loss {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hLP : ∀x∈P,L≤x) :
    (F.card:ℝ)≤(PreparedCrooked F c L).card+(PreparedAP F c L).card+
      (WitnessException (Ground N) c:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3 := by
  have hC : ((CrookedMembers F).card:ℝ)≤(PreparedCrooked F c L).card+
      (N:ℝ)+(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_prepared_crooked_count hF hroot hP hcP hLP
  have hA := actual_prepared_AP_count c L hF
  have hp : ((Progressions F).card:ℝ)+(CrookedMembers F).card=F.card := by
    exact_mod_cast actual_progression_crooked_partition F
  linarith only [hC,hA,hp]

theorem actual_prepared_union_loss {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L : ℤ}
    (hF : Legal (Ground N) F) (hroot : ∀S∈F,¬IsAP S→c∈S)
    (hP : P∈F) (hcP : c∉P) (hLP : ∀x∈P,L≤x) :
    (F.card:ℝ)≤(PreparedCrooked F c L∪PreparedAP F c L).card+
      (WitnessException (Ground N) c:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3 := by
  have hp := Finset.card_union_of_disjoint (actual_prepared_families_disjoint F c L)
  have hh := actual_joint_preparation_loss hF hroot hP hcP hLP
  rw [hp,Nat.cast_add]
  exact hh

theorem actual_original_joint_preparation28 {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 2^49≤N) (hF : Legal (Ground N) F) (hcounter : B N<F.card) :
    ∃ H : Finset (Finset ℤ),(H=F ∨ H=Family N F) ∧ Legal (Ground N) H ∧ H.card=F.card ∧
      (Deleted N 28 H).card=(Deleted N 28 F).card ∧
      (Retained N 28 H).card=(Retained N 28 F).card ∧
      ∃ c∈Ground N,∃ L R:ℕ,c<(L:ℤ) ∧ L≤R ∧ R≤N ∧
        (∀ S∈Retained N 28 H,¬IsAP S→c∈S) ∧
        (∀ S∈Avoiders (Retained N 28 H) c,IsAP S) ∧
        (∃ P∈Avoiders (Retained N 28 H) c,∀ z∈P,(L:ℤ)≤z) ∧
        (∃ T∈Avoiders (Retained N 28 H) c,∀ z∈T,z≤(R:ℤ)) ∧
        (∀ S∈Avoiders (Retained N 28 H) c,
          (∃ a∈S,a≤(L:ℤ) ∧ ∀ z∈S,a≤z) ∧
          ∃ b∈S,(R:ℤ)≤b ∧ ∀ z∈S,z≤b) ∧
        (PreparedCrooked (Retained N 28 H) c L⊆CrookedMembers (Retained N 28 H)) ∧
        (PreparedAP (Retained N 28 H) c L⊆Progressions (Retained N 28 H)) ∧
        Disjoint (PreparedCrooked (Retained N 28 H) c L) (PreparedAP (Retained N 28 H) c L) ∧
        Legal (Ground N) (PreparedCrooked (Retained N 28 H) c L∪PreparedAP (Retained N 28 H) c L) ∧
        ((F.card:ℝ)≤(PreparedCrooked (Retained N 28 H) c L).card+
          (PreparedAP (Retained N 28 H) c L).card+(Deleted N 28 F).card+
          (WitnessException (Ground N) c:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3) ∧
        (∀ S∈PreparedAP (Retained N 28 H) c L,0<Step S ∧ Step S≤N ∧ 4≤S.card ∧
          S=(Finset.range S.card).image (fun i:ℕ=>Low S+(Step S:ℤ)*(i:ℤ)) ∧
          High S=Low S+((S.card-1:ℕ):ℤ)*(Step S:ℤ) ∧
          (c∈S→Low S<c ∧ (L:ℤ)<High S) ∧ (c∉S→Low S≤(L:ℤ) ∧ (R:ℤ)≤High S)) ∧
        ∃ x p:Finset ℤ→ℤ,∀ S∈PreparedCrooked (Retained N 28 H) c L,
          IntrinsicPair c S {x S,p S} ∧ x S<p S ∧ x S≤(R:ℤ) ∧ (L:ℤ)<p S ∧ x S≠(L:ℤ) ∧
            (c<x S→x S<(L:ℤ)→(R:ℤ)<p S→S∩Finset.Icc (x S) (p S)={x S,p S} ∨
              ¬IsAP (S∩Finset.Icc (x S) (p S))) := by
  obtain ⟨H,hHF,hLH,hcard,hD,hG,c,hc,hroot,hAP,L,R,hLc,hLR,hRN,hP,hT,henv⟩ :=
    OneSided47.actual_original_outside_envelope28 hN hF hcounter
  obtain ⟨P,hP,hLP⟩ := hP
  obtain ⟨T,hT,hTR⟩ := hT
  obtain ⟨hPF,hcP⟩ := Finset.mem_filter.mp hP
  obtain ⟨hTF,hcT⟩ := Finset.mem_filter.mp hT
  have hlegal := actual_retained_legal (r:=28) hLH
  have houtside : ∀S∈Retained N 28 H,c∉S→
      (∃u∈S,u≤(L:ℤ)) ∧ ∃v∈S,(R:ℤ)≤v := by
    intro S hS hcS
    obtain ⟨⟨a,ha,haL,_⟩,b,hb,hRb,_⟩ := henv S (Finset.mem_filter.mpr ⟨hS,hcS⟩)
    exact ⟨⟨a,ha,haL⟩,b,hb,hRb⟩
  have hstructure := actual_prepared_AP_structure hlegal hPF hLP houtside
  have hcount := actual_joint_preparation_loss hlegal hroot hPF hcP hLP
  have hpNat := actual_deletion_card_identity N 28 H
  rw [hD,hcard] at hpNat
  have hpR : ((Retained N 28 H).card:ℝ)+(Deleted N 28 F).card=F.card := by exact_mod_cast hpNat
  have hfinal : (F.card:ℝ)≤(PreparedCrooked (Retained N 28 H) c L).card+
      (PreparedAP (Retained N 28 H) c L).card+(Deleted N 28 F).card+
      (WitnessException (Ground N) c:ℝ)+2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3 := by
    linarith only [hcount,hpR]
  have hLRZ : (L:ℤ)≤R := by exact_mod_cast hLR
  obtain ⟨x,p,hx⟩ := actual_prepared_witness_choices hlegal hroot hLc.le hLRZ hTF hcT hTR
  refine ⟨H,hHF,hLH,hcard,hD,hG,c,hc,L,R,hLc,hLR,hRN,hroot,hAP,
    ⟨P,Finset.mem_filter.mpr ⟨hPF,hcP⟩,hLP⟩,
    ⟨T,Finset.mem_filter.mpr ⟨hTF,hcT⟩,hTR⟩,henv,?_,
    actual_prepared_AP_subset _ _ _,actual_prepared_families_disjoint _ _ _,
    actual_prepared_union_legal c L hlegal,hfinal,hstructure,x,p,hx⟩
  exact (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)

#print axioms actual_prepared_AP_member
#print axioms actual_prepared_AP_subset
#print axioms actual_AP_coordinates
#print axioms actual_prepared_root_support
#print axioms actual_prepared_avoider_support
#print axioms actual_prepared_AP_structure
#print axioms actual_AP_filter_partitions
#print axioms actual_progression_crooked_partition
#print axioms actual_prepared_families_disjoint
#print axioms actual_prepared_union_legal
#print axioms actual_large_AP_member
#print axioms actual_small_AP_member
#print axioms actual_prepared_AP_count
#print axioms actual_joint_preparation_loss
#print axioms actual_prepared_union_loss
#print axioms actual_original_joint_preparation28
end
end JSP233.APPrepare49
