module

public import Erdos272.Traces.HalfBad133
public import Erdos272.Global.APPrepare49

@[expose] public section

namespace JSP233.HalfPrepared133
open StarCompletion RestrictedWitness44 HalfBad133
open PrivatePairExistence PreparedWitness48 APPrepare49
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem actual_no_high_witness_card_half {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L : ℤ} (hF : Legal (Ground N) F)
    (hroot : ∀S∈F,¬IsAP S→c∈S) (hP : P∈F) (hcP : c∉P)
    (hLP : ∀x∈P,L≤x) :
    (CrookedMembers F\HighMembers F c L).card≤HalfWitnessException (Ground N) c := by
  have hs : CrookedMembers F\HighMembers F c L⊆BadMembers F c P := by
    intro S hS
    obtain ⟨hSC,hn⟩ := Finset.mem_sdiff.mp hS
    obtain ⟨hSF,hbad⟩ := Finset.mem_filter.mp hSC
    have hcS := hroot S hSF hbad
    refine Finset.mem_filter.mpr ⟨hSF,hcS,hbad,
      actual_avoider_meets_erase hF hSF hP hcS hcP,?_⟩
    intro Q hw
    apply Finset.disjoint_left.mpr
    intro z hzQ hzP
    exact hn (Finset.mem_filter.mpr ⟨hSC,Q,hw,z,hzQ,hLP z hzP⟩)
  exact (Finset.card_le_card hs).trans (actual_restricted_bad_family_bound_half c P hF)

theorem actual_prepared_crooked_count_half {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L : ℤ} (hF : Legal (Ground N) F)
    (hroot : ∀S∈F,¬IsAP S→c∈S) (hP : P∈F) (hcP : c∉P)
    (hLP : ∀x∈P,L≤x) :
    (CrookedMembers F).card≤(PreparedCrooked F c L).card+N+
      HalfWitnessException (Ground N) c := by
  have hbad := actual_no_high_witness_card_half hF hroot hP hcP hLP
  let D := (HighMembers F c L).filter (fun S=>BoundaryWitness S c L)
  have hDF : D⊆F := by
    intro S hS
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).1
  have hD : D.card≤N := actual_division_point_witness_card hF hDF
    (fun S hS=>hroot S (hDF hS)
      (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).1).2)
    (fun S hS=>(Finset.mem_filter.mp hS).2)
  have hHsub : HighMembers F c L⊆CrookedMembers F := Finset.filter_subset _ _
  have hp := Finset.card_sdiff_add_card_eq_card hHsub
  have hq := Finset.card_filter_add_card_filter_not (s:=HighMembers F c L)
    (fun S=>BoundaryWitness S c L)
  change D.card+(PreparedCrooked F c L).card=(HighMembers F c L).card at hq
  omega

theorem actual_joint_preparation_loss_half {N : ℕ} {F : Finset (Finset ℤ)}
    {P : Finset ℤ} {c L : ℤ} (hF : Legal (Ground N) F)
    (hroot : ∀S∈F,¬IsAP S→c∈S) (hP : P∈F) (hcP : c∉P)
    (hLP : ∀x∈P,L≤x) :
    (F.card:ℝ)≤(PreparedCrooked F c L).card+(PreparedAP F c L).card+
      (HalfWitnessException (Ground N) c:ℝ)+
      2*(N:ℝ)*HarmonicAbel29.Harmonic N+21*N+3 := by
  have hC : ((CrookedMembers F).card:ℝ)≤(PreparedCrooked F c L).card+
      (N:ℝ)+(HalfWitnessException (Ground N) c:ℝ) := by
    exact_mod_cast actual_prepared_crooked_count_half hF hroot hP hcP hLP
  have hA := actual_prepared_AP_count c L hF
  have hp : ((Progressions F).card:ℝ)+(CrookedMembers F).card=F.card := by
    exact_mod_cast actual_progression_crooked_partition F
  linarith only [hC,hA,hp]

#print axioms actual_no_high_witness_card_half
#print axioms actual_prepared_crooked_count_half
#print axioms actual_joint_preparation_loss_half
end
end JSP233.HalfPrepared133
