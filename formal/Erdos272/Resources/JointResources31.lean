import Erdos272.Resources.StarBoundConcrete30
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Actual original-family joint resources. All root triples are counted once.
The remaining defect is the number of crooked large members whose actual
private resource pool is a singleton; no two-private-pair claim is assumed. -/
namespace JSP233.JointResources31
open StarCompletion PrivatePairExistence StarResources30 CrossLine30
open scoped Classical BigOperators
noncomputable section

def TwoTransversals (Ω : Finset ℤ) (D : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (Ω.powersetCard 2).filter (fun Q => ∀ T∈D, (Q∩T).Nonempty)

def Triples (G : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  G.filter (fun S => S.card=3)

def TripleLinks (c : ℤ) (G : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  (Triples G).image (fun S => S.erase c)

def LargeCrooked (G : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  G.filter (fun S => ¬IsAP S ∧ 4≤S.card)

def PrivatePool (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ))
    (S : Finset ℤ) : Finset (Finset ℤ) :=
  (AvailableBadPairsAt c Ω G).filter (fun Q =>
    Q⊆S ∧ ∀ T∈G, T≠S → ¬Q⊆T)

def PrivateLargeUnion (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ)) :
    Finset (Finset ℤ) :=
  (LargeCrooked G).biUnion (PrivatePool c Ω G)

def SingletonPrivateLarge (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ)) :
    Finset (Finset ℤ) :=
  (LargeCrooked G).filter (fun S => (PrivatePool c Ω G S).card=1)

theorem rootPart_legal (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))
    (hlegal : Legal Ω F) : Legal Ω (RootPart F c) := by
  constructor
  · intro S hS
    exact hlegal.1 S (Finset.mem_filter.mp hS).1
  · intro S hS T hT hne
    exact hlegal.2 S (Finset.mem_filter.mp hS).1 T (Finset.mem_filter.mp hT).1 hne

theorem rootPart_rooted (c : ℤ) (F : Finset (Finset ℤ)) : Rooted (RootPart F c) c := by
  intro S hS
  exact (Finset.mem_filter.mp hS).2

theorem rooted_partition (c : ℤ) (G : Finset (Finset ℤ)) (hroot : Rooted G c) :
    G.card=(APSmall G).card+(Triples G).card+(APLarge G).card+(LargeCrooked G).card := by
  let small := G.filter (fun S => S.card≤2)
  let large := G.filter (fun S => 4≤S.card)
  have hs : small=APSmall G := by
    ext S
    simp only [small,APSmall,Finset.mem_filter]
    constructor
    · rintro ⟨hS,hcard⟩
      exact ⟨hS,nonempty_card_le_two_isAP ⟨c,hroot S hS⟩ hcard,hcard⟩
    · aesop
  have hd1 : Disjoint small (Triples G) := by
    apply Finset.disjoint_left.mpr
    intro S hS hT
    have := (Finset.mem_filter.mp hS).2
    have := (Finset.mem_filter.mp hT).2
    omega
  have hd2 : Disjoint (small∪Triples G) large := by
    apply Finset.disjoint_left.mpr
    intro S hS hL
    have hl := (Finset.mem_filter.mp hL).2
    rcases Finset.mem_union.mp hS with hS | hS
    · have := (Finset.mem_filter.mp hS).2; omega
    · have := (Finset.mem_filter.mp hS).2; omega
  have he : small∪Triples G∪large=G := by
    ext S
    simp only [small,Triples,large,Finset.mem_union,Finset.mem_filter]
    constructor
    · aesop
    · intro hS
      by_cases h2 : S.card≤2
      · exact Or.inl (Or.inl ⟨hS,h2⟩)
      by_cases h3 : S.card=3
      · exact Or.inl (Or.inr ⟨hS,h3⟩)
      · exact Or.inr ⟨hS,by omega⟩
  have hp : G.card=small.card+(Triples G).card+large.card := by
    calc
      G.card=(small∪Triples G∪large).card := congrArg Finset.card he.symm
      _=small.card+(Triples G).card+large.card := by
        rw [Finset.card_union_of_disjoint hd2,Finset.card_union_of_disjoint hd1]
  have hl : large.card=(APLarge G).card+(LargeCrooked G).card := by
    have hh := Finset.card_filter_add_card_filter_not (s:=large) IsAP
    have ha : large.filter IsAP=APLarge G := by
      ext S
      simp only [large,APLarge,Finset.mem_filter]
      aesop
    have hb : large.filter (fun S => ¬IsAP S)=LargeCrooked G := by
      ext S
      simp only [large,LargeCrooked,Finset.mem_filter]
      aesop
    rw [ha,hb] at hh
    exact hh.symm
  rw [hs,hl] at hp
  omega

theorem root_small_card_le_kernel (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))
    (hlegal : Legal Ω F) :
    (APSmall (RootPart F c)).card≤(CommonKernel Ω F c).card := by
  have hs : APSmall (RootPart F c)⊆RootPart F c∩PairStar Ω c := by
    intro S hS
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hS).1,
      apSmall_subset_pairStar c Ω (RootPart F c) (rootPart_legal c Ω F hlegal)
        (rootPart_rooted c F) hS⟩
  exact (Finset.card_le_card hs).trans (actual_small_members_card_le_kernel Ω F c hlegal)

theorem tripleLinks_card (c : ℤ) (G : Finset (Finset ℤ)) (hroot : Rooted G c) :
    (TripleLinks c G).card=(Triples G).card := by
  apply Finset.card_image_of_injOn
  intro S hS T hT he
  have hcS := hroot S (Finset.mem_filter.mp hS).1
  have hcT := hroot T (Finset.mem_filter.mp hT).1
  calc
    S=insert c (S.erase c) := (Finset.insert_erase hcS).symm
    _=insert c (T.erase c) := by rw [show S.erase c=T.erase c from he]
    _=T := Finset.insert_erase hcT

theorem tripleLinks_subset_pairUniverse (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) (hground : ∀ S∈G, S⊆Ω) (hroot : Rooted G c) :
    TripleLinks c G⊆PairUniverse c Ω := by
  intro Q hQ
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hSG,hcard⟩ := Finset.mem_filter.mp hS
  apply Finset.mem_powersetCard.mpr
  refine ⟨?_,?_⟩
  · intro x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
      hground S hSG (Finset.mem_erase.mp hx).2⟩
  · rw [Finset.card_erase_of_mem (hroot S hSG),hcard]

theorem root_tripleLinks_subset_twoTransversals (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hlegal : Legal Ω F) :
    TripleLinks c (RootPart F c)⊆TwoTransversals (Ω.erase c) (Avoiders F c) := by
  intro Q hQ
  have hp := tripleLinks_subset_pairUniverse c Ω (RootPart F c)
    (rootPart_legal c Ω F hlegal).1 (rootPart_rooted c F) hQ
  apply Finset.mem_filter.mpr
  refine ⟨hp,?_⟩
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hSG,hcard⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,hcS⟩ := Finset.mem_filter.mp hSG
  intro T hT
  obtain ⟨hTF,hcT⟩ := Finset.mem_filter.mp hT
  have hne : S≠T := by intro he; exact hcT (he ▸ hcS)
  obtain ⟨x,hx⟩ := isAP_nonempty (hlegal.2 S hSF T hTF hne)
  obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
  refine ⟨x,Finset.mem_inter.mpr ⟨Finset.mem_erase.mpr ⟨?_,hxS⟩,hxT⟩⟩
  intro he
  exact hcT (he ▸ hxT)

theorem root_triples_card_le_twoTransversals (c : ℤ) (Ω : Finset ℤ)
    (F : Finset (Finset ℤ)) (hlegal : Legal Ω F) :
    (Triples (RootPart F c)).card≤(TwoTransversals (Ω.erase c) (Avoiders F c)).card := by
  rw [←tripleLinks_card c (RootPart F c) (rootPart_rooted c F)]
  exact Finset.card_le_card (root_tripleLinks_subset_twoTransversals c Ω F hlegal)

theorem tripleLinks_disjoint_covered (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) (hlegal : Legal Ω G) (hroot : Rooted G c) :
    Disjoint (TripleLinks c G) (CoveredAPBadPairs c Ω G) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hC
  obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hSG,hcard⟩ := Finset.mem_filter.mp hS
  obtain ⟨hpow,hQcard,hcQ,hbad,T,hTG,hAP,hsub⟩ := Finset.mem_filter.mp hC
  have hSc := hroot S hSG
  have hSbad : ¬IsAP S := by simpa only [Finset.insert_erase hSc] using hbad
  have hne : S≠T := by intro he; exact hSbad (he ▸ hAP)
  have hST : S⊆T := by
    intro x hx
    by_cases hxc : x=c
    · simpa [hxc] using hroot T hTG
    · exact hsub (Finset.mem_erase.mpr ⟨hxc,hx⟩)
  have he : S∩T=S := Finset.inter_eq_left.mpr hST
  exact hSbad (he ▸ hlegal.2 S hSG T hTG hne)

theorem privatePool_nonempty (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ))
    (hlegal : Legal Ω G) (hroot : Rooted G c) {S : Finset ℤ}
    (hSG : S∈G) (hbad : ¬IsAP S) : (PrivatePool c Ω G S).Nonempty := by
  obtain ⟨Q,hQ,hsub,hprivate⟩ := private_resource_at_root_exists hlegal hroot hSG hbad
  exact ⟨Q,Finset.mem_filter.mpr ⟨hQ,hsub,hprivate⟩⟩

theorem privatePools_disjoint (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ))
    {S T : Finset ℤ} (hTG : T∈G) (hne : S≠T) :
    Disjoint (PrivatePool c Ω G S) (PrivatePool c Ω G T) := by
  apply Finset.disjoint_left.mpr
  intro Q hS hT
  exact (Finset.mem_filter.mp hS).2.2 T hTG hne.symm (Finset.mem_filter.mp hT).2.1

theorem privateLargeUnion_card (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ)) :
    (PrivateLargeUnion c Ω G).card=∑ S∈LargeCrooked G, (PrivatePool c Ω G S).card := by
  apply Finset.card_biUnion
  intro S hS T hT hne
  exact privatePools_disjoint c Ω G (Finset.mem_filter.mp hT).1 hne

theorem privateLargeUnion_subset_available (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) :
    PrivateLargeUnion c Ω G⊆AvailableBadPairsAt c Ω G := by
  intro Q hQ
  obtain ⟨S,hS,hQ⟩ := Finset.mem_biUnion.mp hQ
  exact (Finset.mem_filter.mp hQ).1

theorem double_largeCrooked_le_privateUnion_add_singletons
    (c : ℤ) (Ω : Finset ℤ) (G : Finset (Finset ℤ))
    (hlegal : Legal Ω G) (hroot : Rooted G c) :
    2*(LargeCrooked G).card≤(PrivateLargeUnion c Ω G).card+
      (SingletonPrivateLarge c Ω G).card := by
  have hs : ∀ S∈LargeCrooked G, 2≤(PrivatePool c Ω G S).card+
      if (PrivatePool c Ω G S).card=1 then 1 else 0 := by
    intro S hS
    obtain ⟨hSG,hbad,hlarge⟩ := Finset.mem_filter.mp hS
    have hp := Finset.card_pos.mpr (privatePool_nonempty c Ω G hlegal hroot hSG hbad)
    split_ifs <;> omega
  have hh := Finset.sum_le_sum hs
  rw [Finset.sum_add_distrib,←privateLargeUnion_card c Ω G] at hh
  have he : (∑ S∈LargeCrooked G, if (PrivatePool c Ω G S).card=1 then 1 else 0)=
      (SingletonPrivateLarge c Ω G).card := by
    rw [Finset.sum_boole]
    rfl
  rw [he] at hh
  simpa [Finset.sum_const_nat,Nat.mul_comm] using hh

theorem tripleLinks_disjoint_privateLargeUnion (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) :
    Disjoint (TripleLinks c G) (PrivateLargeUnion c Ω G) := by
  apply Finset.disjoint_left.mpr
  intro Q hQ hP
  obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hQ
  obtain ⟨hTG,hTcard⟩ := Finset.mem_filter.mp hT
  obtain ⟨S,hS,hP⟩ := Finset.mem_biUnion.mp hP
  obtain ⟨hSG,hbad,hScard⟩ := Finset.mem_filter.mp hS
  have hne : T≠S := by intro he; have := congrArg Finset.card he; omega
  exact (Finset.mem_filter.mp hP).2.2 T hTG hne (Finset.erase_subset c T)

theorem covered_disjoint_privateLargeUnion (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) :
    Disjoint (CoveredAPBadPairs c Ω G) (PrivateLargeUnion c Ω G) :=
  (covered_disjoint_available c Ω G).mono_right
    (privateLargeUnion_subset_available c Ω G)

theorem joint_resource_pools_card_le (c : ℤ) (Ω : Finset ℤ)
    (G : Finset (Finset ℤ)) (hlegal : Legal Ω G) (hroot : Rooted G c) :
    (Triples G).card+(CoveredAPBadPairs c Ω G).card+
      (PrivateLargeUnion c Ω G).card≤(PairUniverse c Ω).card := by
  rw [←tripleLinks_card c G hroot]
  have hd1 := tripleLinks_disjoint_covered c Ω G hlegal hroot
  have hd2 : Disjoint (TripleLinks c G∪CoveredAPBadPairs c Ω G)
      (PrivateLargeUnion c Ω G) := Finset.disjoint_union_left.mpr
    ⟨tripleLinks_disjoint_privateLargeUnion c Ω G,
      covered_disjoint_privateLargeUnion c Ω G⟩
  rw [←Finset.card_union_of_disjoint hd1,←Finset.card_union_of_disjoint hd2]
  apply Finset.card_le_card
  exact Finset.union_subset (Finset.union_subset
    (tripleLinks_subset_pairUniverse c Ω G hlegal.1 hroot)
    (covered_subset_pairUniverse c Ω G))
    ((privateLargeUnion_subset_available c Ω G).trans (available_subset_pairUniverse c Ω G))

theorem actual_joint_budget (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ))
    (hc : c∈Ω) (hlegal : Legal Ω F) :
    2*F.card≤2*(Avoiders F c).card+2*(CommonKernel Ω F c).card+
      (Ω.card-1).choose 2+(TwoTransversals (Ω.erase c) (Avoiders F c)).card+
      (APLarge (RootPart F c)).card+
      (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c Ω (RootPart F c)).card := by
  let G := RootPart F c
  have hG := rootPart_legal c Ω F hlegal
  have hr := rootPart_rooted c F
  have hp := rooted_partition c G hr
  have hs := root_small_card_le_kernel c Ω F hlegal
  have ht := root_triples_card_le_twoTransversals c Ω F hlegal
  have hu := joint_resource_pools_card_le c Ω G hG hr
  have hz := double_largeCrooked_le_privateUnion_add_singletons c Ω G hG hr
  have ha := actual_APLarge_count_le_covered c Ω G hG.1 hr
  have hf := root_avoider_card_partition F c
  have he : (PairUniverse c Ω).card=(Ω.card-1).choose 2 := by
    unfold PairUniverse
    rw [Finset.card_powersetCard,Finset.card_erase_of_mem hc]
  rw [he] at hu
  dsimp only [G] at hp hu hz ha
  omega

theorem actual_joint_budget_of_defect_supply
    (c : ℤ) (Ω : Finset ℤ) (F : Finset (Finset ℤ)) (hc : c∈Ω)
    (hlegal : Legal Ω F) (b : ℕ)
    (hsupply : (APActiveSteps c (APLarge (RootPart F c))).card+
      (SingletonPrivateLarge c Ω (RootPart F c)).card≤b) :
    2*F.card≤2*(Avoiders F c).card+2*(CommonKernel Ω F c).card+
      (Ω.card-1).choose 2+(TwoTransversals (Ω.erase c) (Avoiders F c)).card+
      (APLarge (RootPart F c)).card+b := by
  have hh := actual_joint_budget c Ω F hc hlegal
  omega

theorem actual_completion_payment (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F) :
    F.card+N≤B N+(Avoiders F c).card+(CommonKernel (Ground N) F c).card := by
  simpa only [ground_card] using completion_payment (Ground N) F c (B N) hc hlegal
    (StarBoundConcrete30.actual_starBound N)

theorem actual_kernel_capacity_bound (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F)
    (hcapacity : (Avoiders F c).card+(CommonKernel (Ground N) F c).card≤N) :
    F.card≤B N := by
  have hh := actual_completion_payment N F c hc hlegal
  omega

theorem actual_counterexample_joint_deficit (N : ℕ) (F : Finset (Finset ℤ)) (c : ℤ)
    (hc : c∈Ground N) (hlegal : Legal (Ground N) F) (hover : B N<F.card) :
    N+1≤(Avoiders F c).card+(CommonKernel (Ground N) F c).card := by
  have hh := actual_completion_payment N F c hc hlegal
  omega

#print axioms rootPart_legal
#print axioms rootPart_rooted
#print axioms rooted_partition
#print axioms root_small_card_le_kernel
#print axioms tripleLinks_card
#print axioms tripleLinks_subset_pairUniverse
#print axioms root_tripleLinks_subset_twoTransversals
#print axioms root_triples_card_le_twoTransversals
#print axioms tripleLinks_disjoint_covered
#print axioms privatePool_nonempty
#print axioms privatePools_disjoint
#print axioms privateLargeUnion_card
#print axioms privateLargeUnion_subset_available
#print axioms double_largeCrooked_le_privateUnion_add_singletons
#print axioms tripleLinks_disjoint_privateLargeUnion
#print axioms covered_disjoint_privateLargeUnion
#print axioms joint_resource_pools_card_le
#print axioms actual_joint_budget
#print axioms actual_joint_budget_of_defect_supply
#print axioms actual_completion_payment
#print axioms actual_kernel_capacity_bound
#print axioms actual_counterexample_joint_deficit
end
end JSP233.JointResources31
