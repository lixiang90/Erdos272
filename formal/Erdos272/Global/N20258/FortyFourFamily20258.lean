module

public import Erdos272.Global.N20258.CutoffFamily20258
public import Erdos272.Counting.APDensity112
public import Erdos272.Arithmetic.N20258.FortyFourBlocks20258
public import Erdos272.Capacity.N20258.FiveSixths20258
public import Erdos272.Capacity.N20258.FortyFivePool20258

@[expose] public section
namespace JSP233.FortyFourFamily20258
open StarCompletion PrivatePairExistence IntrinsicTriples208 APClasses88404
open ProgressionPartition20258 ResidueCapacity20258 FortyFourBlocks20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

private theorem block {a b : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258≤b) (hi : b≤21600) (cert : good a b) (legal : Legal (Ground b) F)
    (sizes : ∀ S ∈ F, 44 ≤ S.card)
    (omits : ∀ z ∈ Ground b, ∃ S ∈ CrookedMembers F, z ∉ S ∧ S.card ≤ 44)
    (layer : ((CrookedMembers F).filter (fun S => S.card=44)).card ≤ 44*b)
    (capH : (CrookedMembers F).card ≤ cap b) : F.card ≤ B a := by
  let H := CrookedMembers F
  let n : ℝ := ((b-1 : ℕ) : ℝ)
  let x : ℝ := 5*n/6
  let M := ∑ S ∈ F, ((Pool S).card : ℝ)
  have hn : 20257≤n := by dsimp only [n]; exact_mod_cast (show 20257≤b-1 by omega)
  have hx : 0<x := by dsimp only [x]; linarith only [hn]
  have hw : 0≤1-529/x := sub_nonneg.mpr ((div_le_one hx).mpr (by dsimp only [x]; linarith only [hn]))
  have priced := FiveSixths20258.actual (by omega : 62≤b) legal
  change (∑ d ∈ steps, ((StepAP F d).card : ℝ))+M/x ≤ 362323/1000000*n^2+2834/1000*n+1 at priced
  have spent := FortyFivePool20258.family (by omega : b≤2^18) legal sizes layer
  have pay : 529/x*(H.card : ℝ) ≤ M/x+83*44*b/x := by
    rw [←add_div,div_mul_eq_mul_div]
    exact (div_le_div_iff_of_pos_right hx).mpr spent
  have kept := ResidueJoint20258.steps_in_ground (by omega : 62≤b)
  have split : ((F.filter IsAP).card : ℝ)+(H.card : ℝ)=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
  have finish (t c : ℕ) (count : H.card≤c)
      (part : (F.filter IsAP).card ≤ 1+(∑ d ∈ steps, (StepAP F d).card)+t)
      (bound : price b t c ≤ target a) : F.card ≤ B a := by
    have pr : ((F.filter IsAP).card : ℝ) ≤ 1+(∑ d ∈ steps, ((StepAP F d).card : ℝ))+t := by exact_mod_cast part
    have hc : (H.card : ℝ)≤c := by exact_mod_cast count
    have wc := mul_le_mul_of_nonneg_left hc hw
    have br := (Rat.cast_le (K := ℝ)).mpr bound
    unfold price at br
    push_cast at br
    change 1+(t : ℝ)+(362323/1000000*n^2+2834/1000*n+1)+83*44*b/x+(1-529/x)*c ≤ (target a : ℝ) at br
    have result : (F.card : ℝ)≤target a := by linarith only [pr,wc,br,priced,pay,split]
    have rb : B a=target a := by simp only [B,target,Nat.choose_two_right]
    rw [rb]
    exact_mod_cast result
  by_cases low : H.card≤1877*(b-2)
  · have part := actual_AP_partition (by omega : 1≤b) legal steps kept (k := 43)
      (fun d _ S hS => by have := sizes S (subset F d hS); omega)
    have eqn : lowTail b = offTail (b-1) 43 steps :=
      StrideQuotients20258.compact_tail_eq (by omega) kept
    rw [←eqn] at part
    exact finish _ _ low part cert.1
  · have part := IntervalGapTails20258.partition (by omega : 3≤b) (by decide : 0<44)
      (by omega : 44+1≤b) (by decide : 44≤1877) (by decide : (44-1)*43+1≤1877)
      steps kept legal (Finset.Subset.refl H) (Nat.lt_of_not_ge low) omits
    have eqn : highTail b=∑ d ∈ Finset.Icc 1 (b-1) \ steps,
        IntervalGapTails20258.cost ((b-1)/d) 44 1877 43 :=
      IntervalGapTails20258.grouped_eq (by omega) kept
    rw [←eqn] at part
    exact finish _ _ capH part cert.2

/-- Every actual family admitting a crooked omitter of size at most 44
at each site satisfies the conjectured bound throughout the low window. -/
theorem low_window {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258≤N) (hi : N≤21600)
    (legal : Legal (Ground N) F)
    (omits : ∀ z ∈ Ground N, ∃ S ∈ CrookedMembers F, z ∉ S ∧ S.card≤44) : F.card ≤ B N := by
  by_contra! counter
  obtain ⟨sizes,layer⟩ := SmallAnchor20258.at_44 lo (by omega) legal counter omits
  obtain ⟨a,b,aN,Nb,bhi,goodab⟩ := cover lo hi
  have one : (1 : ℤ) ∈ Ground N := (mem_ground _ _).mpr ⟨le_rfl,by omega⟩
  obtain ⟨P,hP,_,pSize⟩ := omits 1 one
  have padded : Legal (Ground b) F := by
    refine ⟨fun S hs y hy => ?_,legal.2⟩
    obtain ⟨l,r⟩ := (mem_ground _ _).mp (legal.1 S hs hy)
    exact (mem_ground _ _).mpr ⟨l,by omega⟩
  have covers (z : ℤ) (_ : z ∈ Ground b) : ∃ S ∈ CrookedMembers F, z ∉ S ∧ S.card≤44 := by
    by_cases inside : z ∈ Ground N
    · exact omits z inside
    · exact ⟨P,hP,fun hz => inside (legal.1 P (Finset.mem_filter.mp hP).1 hz),pSize⟩
  have fixed := CutoffFamily20258.fixed_cap (m := 44) (a := 44) padded (by decide) (by decide)
    (by omega) (by omega) ⟨P,hP,pSize⟩ covers
  have fc : (CrookedMembers F).card ≤ cap b := by
    norm_num [CutoffFamily20258.fixedCap,FixedSmallScalars82427.Coefficient,
      FixedSmallScalars82427.Credit,Nat.choose_two_right] at fixed
    unfold cap
    have h : ((CrookedMembers F).card : ℝ)+84239 ≤ 1893*(b : ℝ) := by linarith only [fixed]
    have h' : (CrookedMembers F).card+84239 ≤ 1893*b := by exact_mod_cast h
    omega
  have bound := block (lo.trans Nb) bhi goodab padded sizes covers
    (layer.trans (Nat.mul_le_mul_left 44 Nb)) fc
  have ab : B a≤B N := by unfold B; have := Nat.choose_le_choose 2 aN; omega
  exact (not_lt_of_ge (bound.trans ab)) counter

/-- The price of one member and its pointwise omitters suffices whenever their
sizes satisfy this inequality. The harmonic tangent removes any upper limit on N. -/
theorem of_member {N m : ℕ} {P : Finset ℤ} {F : Finset (Finset ℤ)}
    (two : 2≤N) (room : m+1≤N) (legal : Legal (Ground N) F) (hP : P ∈ F)
    (omits : ∀ z ∈ Ground N, ∃ S ∈ CrookedMembers F, z ∉ S ∧ S.card≤m)
    (enough : 5000*((m-1)*P.card+17)≤443*N) : F.card≤B N := by
  by_cases existsP : P.Nonempty
  · let n : ℝ := (N : ℝ)
    have hn : 0≤n := Nat.cast_nonneg _
    have tangent := RootHeight20258.harmonic_tangent N 16384 (by decide)
    have atBase := APDensity112.actual_harmonic_le_J (N := 16383) (J := 14) (by decide) (by decide)
    have harmonic : HarmonicAbel29.Harmonic N≤14+n/16384 := by
      norm_num only [Nat.reduceSub,Nat.cast_ofNat] at tangent atBase
      linarith only [tangent,atBase]
    have ap := APDensity112.actual_AP_count_harmonic (Density41.actual_AP_part_legal legal)
      (fun S hS => (Finset.mem_filter.mp hS).2)
    have cap := TwoTransversals20258.actual_member two room legal hP existsP omits
    let s := (m-1)*P.card
    have cap' : ((CrookedMembers F).card : ℝ)≤((s : ℝ)+1)*n := by
      have h := cap.trans (Nat.mul_le_mul_left _ (Nat.sub_le N 2))
      dsimp only [n]
      exact_mod_cast h
    have paid : 5000*((s : ℝ)+17)≤443*n := by
      dsimp only [n,s]; exact_mod_cast enough
    have split : ((Density41.APPart F).card : ℝ)+((CrookedMembers F).card : ℝ)=F.card :=
      by exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
    have bound : (F.card : ℝ)≤(N.choose 2 : ℝ)+1 := by
      rw [Nat.cast_choose_two]
      change (F.card : ℝ)≤n*(n-1)/2+1
      change _≤(329/800 : ℝ)*n^2+n*HarmonicAbel29.Harmonic N+n+1 at ap
      nlinarith only [ap,cap',split,mul_le_mul_of_nonneg_left harmonic hn,
        mul_le_mul_of_nonneg_right paid hn,sq_nonneg n,hn]
    have upper : F.card≤N.choose 2+1 := by exact_mod_cast bound
    unfold B; omega
  · have sub : F ⊆ {P} := by
      intro T hT
      apply Finset.mem_singleton.mpr
      by_contra ne
      exact existsP ((isAP_nonempty (legal.2 T hT P hP ne)).mono Finset.inter_subset_right)
    have card : F.card≤1 := by simpa using Finset.card_le_card sub
    unfold B; omega

/-- On every ground from 20258 on, a counterexample must have a site
whose every crooked omitter has at least 45 elements. -/
theorem actual {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258≤N) (legal : Legal (Ground N) F)
    (omits : ∀ z ∈ Ground N, ∃ S ∈ CrookedMembers F, z ∉ S ∧ S.card≤44) : F.card≤B N := by
  by_cases low : N≤21600
  · exact low_window lo low legal omits
  obtain ⟨P,hP,_,size⟩ := omits 1 ((mem_ground _ _).mpr ⟨le_rfl,by omega⟩)
  exact of_member (by omega) (by omega) legal (Finset.mem_filter.mp hP).1 omits (by omega)

theorem counterexample_site {N : ℕ} {F : Finset (Finset ℤ)} (lo : 20258≤N)
    (legal : Legal (Ground N) F) (counter : B N<F.card) :
    ∃ z ∈ Ground N, ∀ S ∈ CrookedMembers F, z ∉ S → 45≤S.card := by
  by_contra! h
  apply (not_lt_of_ge (actual lo legal ?_)) counter
  intro z hz
  obtain ⟨S,hs,away,small⟩ := h z hz
  exact ⟨S,hs,away,by omega⟩

#print axioms of_member
#print axioms actual
#print axioms counterexample_site
end
end JSP233.FortyFourFamily20258
