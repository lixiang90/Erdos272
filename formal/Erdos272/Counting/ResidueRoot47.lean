import Erdos272.Counting.NonIntervalAP47
import Erdos272.Counting.Straddling47
import Erdos272.Geometry.CrossLine30

/-! Actual primitive AP resources leave every residue class that their member leaves. -/
namespace JSP233.ResidueRoot47
open StarCompletion PrivatePairExistence APGeometry AffineLine30 CrossLine30
open StarResources30 WitnessInterval43 LongTerminal35 RestrictedWitness44
open scoped Classical
noncomputable section
set_option maxHeartbeats 3000000

def Outside (Ω : Finset ℤ) (c : ℤ) (k : ℕ) : Finset ℤ := Ω.filter (fun x=>¬(k:ℤ)∣x-c)
def MeetingPool (Ω : Finset ℤ) (c : ℤ) (P : Finset ℤ) : Finset (Finset ℤ) :=
  ((Ω.erase c).powersetCard 2).filter (fun Q=>¬Disjoint Q P)

theorem actual_model_offset_dvd {S : Finset ℤ} {c d : ℤ} {l r : ℕ}
    (hrep : S=mapSet c d (StaircaseGeometry.Window l r)) {x : ℤ} (hx : x∈S) : d∣x-c := by
  rw [hrep] at hx
  obtain ⟨z,_hz,he⟩ := Finset.mem_image.mp hx
  refine ⟨z,?_⟩
  dsimp only [affine] at he
  nlinarith only [he]

theorem actual_primitive_meets_outside {Ω S Q : Finset ℤ} {c d : ℤ} {k : ℕ}
    (hd : 0<d) (hsub : S⊆Ω) (hroot : c∈S) (hAP : IsAP S)
    (hdS : trueStep c S=d)
    (hQ : Q⊆S) (hprim : IsStepPrimitive c d Q)
    (hmet : (S∩Outside Ω c k).Nonempty) : ¬Disjoint Q (Outside Ω c k) := by
  intro hdis
  obtain ⟨u,v,huv,hrepQ⟩ := Finset.card_eq_two.mp hprim.1
  have hu : u∈Q := by simp [hrepQ]
  have hv : v∈Q := by simp [hrepQ]
  have hku : (k:ℤ)∣u-c := by
    by_contra hn
    exact Finset.disjoint_left.mp hdis hu (Finset.mem_filter.mpr ⟨hsub (hQ hu),hn⟩)
  have hkv : (k:ℤ)∣v-c := by
    by_contra hn
    exact Finset.disjoint_left.mp hdis hv (Finset.mem_filter.mpr ⟨hsub (hQ hv),hn⟩)
  have hg := hprim.2.2.2 u hu v hv huv
  have hkd : (k:ℤ)∣d := by
    have hh : k∣d.natAbs := hg ▸ Int.dvd_gcd hku hkv
    have hh' := Int.natCast_dvd_natCast.mpr hh
    rw [Int.natAbs_of_nonneg hd.le] at hh'
    exact hh'
  obtain ⟨_hd,l,r,hrepS⟩ := trueStep_representation hAP hroot
  rw [hdS] at hrepS
  obtain ⟨x,hx⟩ := hmet
  obtain ⟨hxS,hxO⟩ := Finset.mem_inter.mp hx
  exact (Finset.mem_filter.mp hxO).2 (hkd.trans (actual_model_offset_dvd hrepS hxS))

theorem actual_AP_pool_meets_outside {N k : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hground : ∀ S∈F,S⊆Ground N) (hroot : Rooted F c)
    (hmet : ∀ S∈F,(S∩Outside (Ground N) c k).Nonempty) :
    APResourcePool c (APLarge F)⊆MeetingPool (Ground N) c (Outside (Ground N) c k) := by
  intro Q hQ
  obtain ⟨d,hd,hQP⟩ := Finset.mem_biUnion.mp hQ
  obtain ⟨S,hS,hQS,hprim⟩ :=
    (mem_gcdStepPool c d (StepClass (APLarge F) (trueStep c) d) Q).mp hQP
  have hSL := stepClass_subset (APLarge F) (trueStep c) d hS
  obtain ⟨hSF,hAP,_hlarge⟩ := Finset.mem_filter.mp hSL
  have hdS : trueStep c S=d := (Finset.mem_filter.mp hS).2
  have hdpos := actual_step_labels_positive c (APLarge F)
    (fun T hT=>(Finset.mem_filter.mp hT).2.1)
    (fun T hT=>hroot T (Finset.mem_filter.mp hT).1) d hd
  exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨
    fun x hx=>Finset.mem_erase.mpr ⟨fun he=>hprim.2.1 (he ▸ hx),hground S hSF (hQS hx)⟩,
    hprim.1⟩,actual_primitive_meets_outside hdpos (hground S hSF) (hroot S hSF)
      hAP hdS hQS hprim (hmet S hSF)⟩

theorem actual_active_steps_card {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hground : ∀ S∈F,S⊆Ground N) (hroot : Rooted F c) :
    (APActiveSteps c (APLarge F)).card≤N := by
  have hs : APActiveSteps c (APLarge F)⊆Finset.Icc 1 (N:ℤ) := by
    intro d hd
    obtain ⟨hd0,hl,hr⟩ := actual_APLarge_active_geometry c (Ground N) F hground hroot hd
    have hll := (mem_ground N (c-2*d)).mp hl
    have hrr := (mem_ground N (c+2*d)).mp hr
    exact Finset.mem_Icc.mpr (by omega)
  have hh := Finset.card_le_card hs
  simpa only [Int.card_Icc,add_sub_cancel_right,Int.toNat_natCast] using hh

theorem intrinsic_insert_not_AP {S Q : Finset ℤ} {c : ℤ}
    (hc : c∈S) (hQ : IntrinsicPair c S Q) : ¬IsAP (insert c Q) := by
  intro hAP
  exact hQ.2.2.2 ⟨insert c Q,hAP,Finset.Subset.refl _,Finset.insert_subset_iff.mpr ⟨hc,hQ.2.2.1⟩⟩

theorem actual_good_rooted_residue_count {N k : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F) (hroot : Rooted F c)
    (hmet : ∀ S∈F,(S∩Outside (Ground N) c k).Nonempty)
    (hgood : ∀ S∈F,¬IsAP S→∃ Q,IntrinsicPair c S Q ∧ ¬Disjoint Q (Outside (Ground N) c k)) :
    F.card≤(MeetingPool (Ground N) c (Outside (Ground N) c k)).card+2*N := by
  let C := CrookedMembers F
  let X := {S // S∈C}
  have hparam : ∀ S:X,∃ Q,IntrinsicPair c S.val Q ∧ ¬Disjoint Q (Outside (Ground N) c k) := by
    intro S
    obtain ⟨hSF,hbad⟩ := Finset.mem_filter.mp S.property
    exact hgood S.val hSF hbad
  choose Q hQ hQP using hparam
  let W := (Finset.univ:Finset X).image Q
  let T := TriplePairs c F
  let A := APResourcePool c (APLarge F)
  let P := Outside (Ground N) c k
  let Pool := MeetingPool (Ground N) c P
  have hSF : ∀ S:X,S.val∈F := fun S=>(Finset.mem_filter.mp S.property).1
  have hQi : Function.Injective Q := by
    intro S U he
    apply Subtype.ext
    exact actual_intrinsic_member_eq hF (hSF S) (hSF U) (hroot S.val (hSF S))
      (hroot U.val (hSF U)) (hQ S) (by rw [he];exact (hQ U).2.2.1)
  have hWC : W.card=C.card := by
    simp only [W,Finset.card_image_of_injective _ hQi,Finset.card_univ,X,Fintype.card_coe]
  have hWpool : W⊆Pool := by
    intro q hq
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨
      fun x hx=>Finset.mem_erase.mpr ⟨fun he=>(hQ S).2.1 (he ▸ hx),
        hF.1 S.val (hSF S) ((hQ S).2.2.1 hx)⟩,(hQ S).1⟩,hQP S⟩
  have hTpool : T⊆Pool := by
    intro q hq
    have hqU := (triplePair_properties c (Ground N) F hF hroot hq).1
    refine Finset.mem_filter.mpr ⟨hqU,?_⟩
    obtain ⟨S,hST,rfl⟩ := Finset.mem_image.mp hq
    have hS := (Finset.mem_filter.mp hST).1
    obtain ⟨x,hx⟩ := hmet S hS
    obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
    have hxc : x≠c := by
      intro he
      have hh := (Finset.mem_filter.mp hxP).2
      apply hh
      simp [he]
    intro hd
    exact Finset.disjoint_left.mp hd (Finset.mem_erase.mpr ⟨hxc,hxS⟩) hxP
  have hApool : A⊆Pool := actual_AP_pool_meets_outside hF.1 hroot hmet
  have hWT : Disjoint W T := by
    apply Finset.disjoint_left.mpr
    intro q hqW hqT
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hqW
    exact intrinsic_insert_not_AP (hroot S.val (hSF S)) (hQ S)
      (triplePair_properties c (Ground N) F hF hroot hqT).2
  have hWA : Disjoint W A := by
    apply Finset.disjoint_left.mpr
    intro q hqW hqA
    obtain ⟨S,_,rfl⟩ := Finset.mem_image.mp hqW
    obtain ⟨_,_,_,U,hU,hQU⟩ := all_pool_members c (APLarge F) (trueStep c) hqA
    obtain ⟨hUF,hAP,_hsize⟩ := Finset.mem_filter.mp hU
    exact witness_pair_not_subset_AP_member hF (hSF S) hUF (hroot S.val (hSF S))
      (hroot U hUF) (Finset.mem_filter.mp S.property).2 hAP (hQ S) hQU
  have hTA : Disjoint T A := by
    apply Finset.disjoint_left.mpr
    intro q hqT hqA
    exact (all_pool_members c (APLarge F) (trueStep c) hqA).2.2.1
      (triplePair_properties c (Ground N) F hF hroot hqT).2
  have hUsub : W∪T∪A⊆Pool := Finset.union_subset (Finset.union_subset hWpool hTpool) hApool
  have hUdis : Disjoint (W∪T) A := Finset.disjoint_union_left.mpr ⟨hWA,hTA⟩
  have hpool := Finset.card_le_card hUsub
  rw [Finset.card_union_of_disjoint hUdis,Finset.card_union_of_disjoint hWT,hWC,
    triplePairs_card c F hroot] at hpool
  have hAP := actual_AP_family_count c (APLarge F)
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>hroot S (Finset.mem_filter.mp hS).1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2)
  have hactive := actual_active_steps_card hF.1 hroot
  have hsmall := apSmall_card_le c (Ground N) F hF hroot
  have hsplit := family_partition F
  dsimp only [A,C,Pool,P] at *
  rw [ground_card] at hsmall
  omega

theorem actual_rooted_residue_count {N k : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hF : Legal (Ground N) F) (hroot : Rooted F c)
    (hmet : ∀ S∈F,(S∩Outside (Ground N) c k).Nonempty) :
    F.card≤(MeetingPool (Ground N) c (Outside (Ground N) c k)).card+2*N+
      WitnessException (Ground N) c := by
  let Good := fun S:Finset ℤ=>IsAP S ∨
    ∃ Q,IntrinsicPair c S Q ∧ ¬Disjoint Q (Outside (Ground N) c k)
  let G := F.filter Good
  let B := F.filter (fun S=>¬Good S)
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G := ⟨fun S hS=>hF.1 S (hGF hS),
    fun S hS T hT hn=>hF.2 S (hGF hS) T (hGF hT) hn⟩
  have hGgood : ∀ S∈G,¬IsAP S→
      ∃ Q,IntrinsicPair c S Q ∧ ¬Disjoint Q (Outside (Ground N) c k) := by
    intro S hS hn
    rcases (Finset.mem_filter.mp hS).2 with hAP|hw
    · exact False.elim (hn hAP)
    · exact hw
  have hGcard := actual_good_rooted_residue_count hLG
    (fun S hS=>hroot S (hGF hS)) (fun S hS=>hmet S (hGF hS)) hGgood
  have hBsub : B⊆BadMembers F c (Outside (Ground N) c k) := by
    intro S hS
    obtain ⟨hSF,hn⟩ := Finset.mem_filter.mp hS
    have hbad : ¬IsAP S := fun ha=>hn (Or.inl ha)
    obtain ⟨x,hx⟩ := hmet S hSF
    obtain ⟨hxS,hxP⟩ := Finset.mem_inter.mp hx
    have hxc : x≠c := by
      intro he
      apply (Finset.mem_filter.mp hxP).2
      simp [he]
    refine Finset.mem_filter.mpr ⟨hSF,hroot S hSF,hbad,
      ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨hxc,hxS⟩,hxP⟩⟩,?_⟩
    intro Q hQ
    by_contra hdis
    exact hn (Or.inr ⟨Q,hQ,hdis⟩)
  have hBcard := (Finset.card_le_card hBsub).trans
    (actual_restricted_bad_family_bound c (Outside (Ground N) c k) hF)
  have hpart := Finset.card_filter_add_card_filter_not (s:=F) Good
  change G.card+B.card=F.card at hpart
  omega

theorem actual_rooted_residue_harmonic {N k : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hcN : c∈Ground N) (hF : Legal (Ground N) F) (hroot : Rooted F c)
    (hmet : ∀ S∈F,(S∩Outside (Ground N) c k).Nonempty) :
    (F.card:ℝ)≤(MeetingPool (Ground N) c (Outside (Ground N) c k)).card+2*(N:ℝ)+
      6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hh : (F.card:ℝ)≤(MeetingPool (Ground N) c (Outside (Ground N) c k)).card+
      2*(N:ℝ)+(WitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_rooted_residue_count hF hroot hmet
  have hW := DivisorMoment45.actual_exception_harmonic hcN
  linarith only [hh,hW]

theorem actual_rooted_parity_harmonic {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (hcN : c∈Ground N) (hF : Legal (Ground N) F) (hroot : Rooted F c)
    (hmet : ∀ S∈F,(S∩Straddling47.OppositeParity N c).Nonempty) :
    (F.card:ℝ)≤3*(N:ℝ)^2/8+5*(N:ℝ)/2+6*(N:ℝ)*HarmonicAbel29.Harmonic N^3 := by
  have hm : ∀ S∈F,(S∩Outside (Ground N) c 2).Nonempty := by
    simpa only [Outside,Straddling47.OppositeParity,Nat.cast_ofNat] using hmet
  have hh := actual_rooted_residue_harmonic hcN hF hroot hm
  have hp : ((MeetingPool (Ground N) c (Outside (Ground N) c 2)).card:ℝ)≤
      3*(N:ℝ)^2/8+(N:ℝ)/2 := by
    have hparity : Outside (Ground N) c 2 = Straddling47.OppositeParity N c := by
      ext x
      simp only [Outside,Straddling47.OppositeParity,Finset.mem_filter,Nat.cast_ofNat]
    rw [hparity]
    exact Straddling47.actual_opposite_parity_pool N c
  linarith only [hh,hp]

#print axioms actual_model_offset_dvd
#print axioms actual_primitive_meets_outside
#print axioms actual_AP_pool_meets_outside
#print axioms actual_active_steps_card
#print axioms intrinsic_insert_not_AP
#print axioms actual_good_rooted_residue_count
#print axioms actual_rooted_residue_count
#print axioms actual_rooted_residue_harmonic
#print axioms actual_rooted_parity_harmonic
end
end JSP233.ResidueRoot47
