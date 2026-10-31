import Erdos272.Core.NearAP36
import Erdos272.Resources.TraceWitnessCodes36
import Erdos272.Counting.BandAggregation34

/-! Actual transversal anchor selection, private structural-pair accounting,
and near/far band aggregation.  The remaining single-member witness/core
geometry is an explicit local premise, never an assumed band bound. -/
namespace JSP233.FarWitness36
open StarCompletion StarResources30 TraceWitnessCodes36 NearAP36 BandAggregation34
open scoped Classical BigOperators
noncomputable section

def FarMembers (K : ℕ) (F : Finset (Finset ℤ)) : Finset (Finset ℤ) :=
  F.filter (fun S=>¬HasNearAPCore K S)

theorem pair_universe_ground_card_le (N : ℕ) (c : ℤ) :
    (PairUniverse c (Ground N)).card≤N.choose 2 := by
  have hsub : PairUniverse c (Ground N)⊆(Ground N).powersetCard 2 := by
    intro Q hQ
    obtain ⟨hQG,hcard⟩ := Finset.mem_powersetCard.mp hQ
    exact Finset.mem_powersetCard.mpr ⟨hQG.trans (Finset.erase_subset _ _),hcard⟩
  simpa only [Finset.card_powersetCard,ground_card] using Finset.card_le_card hsub

theorem actual_transversal_structural_bound (N J t K : ℕ)
    (F : Finset (Finset ℤ)) (H : Finset ℤ) (hlegal : Legal (Ground N) F)
    (hcert : ∀ S∈F, ∃ c:ℤ, c∈S ∧ c∈H ∧ t*K≤4*J*(StructuralPairs c S).card) :
    F.card*t*K≤4*J*H.card*N.choose 2 := by
  have hex : ∀ S : Finset ℤ, ∃ c:ℤ, S∈F → c∈S ∧ c∈H ∧
      t*K≤4*J*(StructuralPairs c S).card := by
    intro S
    by_cases hS:S∈F
    · obtain ⟨c,hcS,hcH,hbound⟩ := hcert S hS
      exact ⟨c,fun _=>⟨hcS,hcH,hbound⟩⟩
    · exact ⟨0,fun hh=>False.elim (hS hh)⟩
  choose anchor ha using hex
  let C : ℤ→Finset (Finset ℤ) := fun c=>F.filter (fun S=>anchor S=c)
  have hCF : ∀ c, C c⊆F := fun c=>Finset.filter_subset _ _
  have hrow : ∀ c∈H, (C c).card*(t*K)≤4*J*N.choose 2 := by
    intro c hc
    have hroot : Rooted (C c) c := by
      intro S hS
      have hSF := hCF c hS
      have hh := (ha S hSF).1
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    have hLC : Legal (Ground N) (C c) :=
      ⟨fun S hS=>hlegal.1 S (hCF c hS),
       fun S hS T hT he=>hlegal.2 S (hCF c hS) T (hCF c hT) he⟩
    have hlo : ∀ S∈C c, t*K≤4*J*(StructuralPairs c S).card := by
      intro S hS
      have hh := (ha S (hCF c hS)).2.2
      simpa only [(Finset.mem_filter.mp hS).2] using hh
    have hs := Finset.sum_le_sum hlo
    simp only [Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum] at hs
    have hb := actual_family_structural_budget hLC hroot
    have hp := pair_universe_ground_card_le N c
    have hm := Nat.mul_le_mul_left (4*J) (hb.trans hp)
    exact hs.trans hm
  have hmaps : ∀ S∈F, anchor S∈H := fun S hS=>(ha S hS).2.1
  have hpart : F.card=∑ c∈H,(C c).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hs := Finset.sum_le_sum hrow
  rw [←Finset.sum_mul] at hs
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  rw [←hpart] at hs
  nlinarith only [hs]

theorem actual_hitting_set_structural_bound (N J t K : ℕ)
    (F : Finset (Finset ℤ)) (H : Finset ℤ) (hlegal : Legal (Ground N) F)
    (hhit : ∀ S∈F, (S∩H).Nonempty)
    (hW : ∀ S∈F, ∀ c∈S, c∈H → t*K≤4*J*(StructuralPairs c S).card) :
    F.card*t*K≤4*J*H.card*N.choose 2 := by
  apply actual_transversal_structural_bound N J t K F H hlegal
  intro S hS
  obtain ⟨c,hc⟩ := hhit S hS
  obtain ⟨hcS,hcH⟩ := Finset.mem_inter.mp hc
  exact ⟨c,hcS,hcH,hW S hS c hcS hcH⟩

theorem actual_member_hits_family {N : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) {R : Finset ℤ} (hR : R∈F) (hRN : R.Nonempty) :
    ∀ S∈F, (S∩R).Nonempty := by
  intro S hS
  by_cases he:S=R
  · obtain ⟨x,hx⟩ := hRN
    exact ⟨x,Finset.mem_inter.mpr ⟨he.symm ▸ hx,hx⟩⟩
  · exact isAP_nonempty (hlegal.2 S hS R hR he)

theorem actual_far_band_budget {N J K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K)
    (hlow : ∀ S∈F, 16*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤32*K)
    (hW : ∀ S∈F, ¬HasNearAPCore K S → ∀ c∈S,
      K^2≤4*J*(StructuralPairs c S).card) :
    (FarMembers K F).card*K≤128*J*N.choose 2 := by
  rcases F.eq_empty_or_nonempty with he|hne
  · simp [he,FarMembers]
  obtain ⟨R,hR⟩ := hne
  have hRN : R.Nonempty := Finset.card_pos.mp (by have hh:=hlow R hR; omega)
  have hMF : FarMembers K F⊆F := Finset.filter_subset _ _
  have hLM : Legal (Ground N) (FarMembers K F) :=
    ⟨fun S hS=>hlegal.1 S (hMF hS),
     fun S hS T hT he=>hlegal.2 S (hMF hS) T (hMF hT) he⟩
  have hh := actual_hitting_set_structural_bound N J K K (FarMembers K F) R hLM
    (fun S hS=>actual_member_hits_family hlegal hR hRN S (hMF hS))
    (by
      intro S hS c hcS _hcR
      have hb := hW S (hMF hS) (Finset.mem_filter.mp hS).2 c hcS
      simpa only [pow_two] using hb)
  have hRh := hhigh R hR
  have hm := Nat.mul_le_mul_right (4*J*N.choose 2) hRh
  have hbound : ((FarMembers K F).card*K)*K≤(128*J*N.choose 2)*K := by
    nlinarith only [hh,hm]
  exact Nat.le_of_mul_le_mul_right hbound hK

theorem actual_one_band_from_local_witnesses {N J K : ℕ} {F : Finset (Finset ℤ)}
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 16*K+1≤S.card) (hhigh : ∀ S∈F, S.card≤32*K)
    (hW : ∀ S∈F, ¬HasNearAPCore K S → ∀ c∈S,
      K^2≤4*J*(StructuralPairs c S).card) :
    F.card*(15*K)≤261*N^2+1920*J*N.choose 2 := by
  have hn := actual_near_members_band_budget hlegal hK hbad hlow
    (fun S hS=>(hhigh S hS).trans (by omega : 32*K≤64*K))
  have hf := actual_far_band_budget hlegal hK hlow hhigh hW
  have hp := Finset.card_filter_add_card_filter_not (s:=F) (HasNearAPCore K)
  change (NearMembers K F).card+(FarMembers K F).card=F.card at hp
  nlinarith only [hn,hf,hp]

theorem actual_large_from_local_far_witnesses (N K J : ℕ) (F : Finset (Finset ℤ))
    (hlegal : Legal (Ground N) F) (hK : 0<K) (hbad : ∀ S∈F, ¬IsAP S)
    (hlow : ∀ S∈F, 16*K+1≤S.card)
    (hW : ∀ j<N+1, ∀ S∈RankBand F Finset.card K j,
      ¬HasNearAPCore (2^j*K) S → ∀ c∈S,
        (2^j*K)^2≤4*J*(StructuralPairs c S).card) :
    15*K*F.card≤522*N^2+3840*J*N.choose 2 := by
  apply actual_large_from_band_budget N K J F hK hlegal.1 hlow
  intro j hj
  let G := RankBand F Finset.card K j
  have hGF : G⊆F := Finset.filter_subset _ _
  have hLG : Legal (Ground N) G :=
    ⟨fun S hS=>hlegal.1 S (hGF hS),fun S hS T hT he=>hlegal.2 S (hGF hS) T (hGF hT) he⟩
  have hb := actual_one_band_from_local_witnesses (J:=J) (K:=2^j*K) hLG
    (by positivity) (fun S hS=>hbad S (hGF hS))
    (fun S hS=>(Finset.mem_filter.mp hS).2.1)
    (fun S hS=>(Finset.mem_filter.mp hS).2.2) (hW j hj)
  have he : 15*(2^j*K)=2^j*(15*K) := by ring
  simpa only [he] using hb

#print axioms pair_universe_ground_card_le
#print axioms actual_transversal_structural_bound
#print axioms actual_hitting_set_structural_bound
#print axioms actual_member_hits_family
#print axioms actual_far_band_budget
#print axioms actual_one_band_from_local_witnesses
#print axioms actual_large_from_local_far_witnesses
end
end JSP233.FarWitness36
