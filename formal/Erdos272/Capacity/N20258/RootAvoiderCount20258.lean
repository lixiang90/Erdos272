module

public import Erdos272.Capacity.N20258.RootPreparation20258
public import Erdos272.Counting.TerminalDeficit51

@[expose] public section

namespace JSP233.RootAvoiderCount20258
open StarCompletion APGeometry PrivatePairExistence DenseDeletion40 IntrinsicTriples208
open PureSource208 SourceBridge208 CoreUnionSource200000 MixedCore200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- A quadratic price from the maximal AP core and its defect. This uses
only the elementary physical defect bound and the old prime sum estimate. -/
theorem pool_quarter {N : ℕ} {S : Finset ℤ} (hi : N ≤ 2^18) (hS : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 400 ≤ S.card) : (S.card : ℝ)^2/4 ≤ (Pool S).card := by
  have two : 2 ≤ S.card := by omega
  have sN : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hS
  have maxle := maxAPSize_le_card S
  have split : MaxAPSize S + Defect S = S.card := by unfold Defect; omega
  have pos := crooked_defect_positive two bad
  let k := (S.card+1)/2
  have ks : S.card ≤ 2*k := by dsimp [k]; omega
  by_cases big : k ≤ Defect S
  · have h := (DensePool158375.physical_quadratic (s := S.card) (e := k)
        (by dsimp [k]; omega)).trans (actual_source_of_defect two big)
    have hR : (k : ℝ)*(k+1) ≤ (Pool S).card := by exact_mod_cast h
    have ksR : (S.card : ℝ) ≤ 2*k := by exact_mod_cast ks
    have square := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) S.card) ksR 2
    nlinarith only [hR,square,Nat.cast_nonneg (α := ℝ) k]
  · let a := MaxAPSize S
    have aN : a ≤ 2^18 := maxle.trans (sN.trans hi)
    have ha : 200 ≤ a := by dsimp [a,k] at *; omega
    have half : S.card ≤ 2*a := by dsimp [a,k] at *; omega
    have haR : (200 : ℝ) ≤ a := by exact_mod_cast ha
    have factor := mul_le_mul_of_nonneg_right haR (Nat.cast_nonneg (α := ℝ) a)
    have u := AnalyticCore180000.unit_large aN
    have sourced := actual_union_core_source (S := S) two
    by_cases few : Defect S ≤ 4
    · have close : S.card ≤ a+4 := by dsimp [a]; omega
      have cr : (S.card : ℝ) ≤ a+4 := by exact_mod_cast close
      have ha' : (396 : ℝ) ≤ a := by exact_mod_cast (show 396 ≤ a by omega)
      have factor' := mul_le_mul_of_nonneg_right ha' (Nat.cast_nonneg (α := ℝ) a)
      have price : ((a : ℝ)+4)^2/4 ≤ UnitBound a := by nlinarith only [u,factor',ha']
      have sq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) S.card) cr 2
      have paid : UnitBound a ≤ (Pool S).card :=
        (show UnitBound a ≤ Defect S*UnitBound a by
          simpa only [one_mul] using Nat.mul_le_mul_right (UnitBound a) pos).trans sourced
      have pr : (UnitBound a : ℝ) ≤ (Pool S).card := by exact_mod_cast paid
      linarith only [sq,price,pr]
    · have cr : (S.card : ℝ) ≤ 2*a := by exact_mod_cast half
      have sq := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) S.card) cr 2
      have paid : 5*UnitBound a ≤ (Pool S).card :=
        (Nat.mul_le_mul_right (UnitBound a) (by omega : 5 ≤ Defect S)).trans sourced
      have pr : 5*(UnitBound a : ℝ) ≤ (Pool S).card := by exact_mod_cast paid
      have price : (a : ℝ)^2/5 ≤ UnitBound a := by nlinarith only [u,factor,haR]
      nlinarith only [sq,price,pr,haR]

/-- In a near-extremal family the minimum size of a crooked avoider controls
both the rooted count and the price paid by every avoider. -/
theorem actual_eight_of_min {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (lo : 9000 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N)
    (hF : Legal (Ground N) F) (near : B N ≤ F.card)
    (large : ∀ S ∈ CrookedMembers F, c ∉ S → 470 ≤ S.card) :
    ((CrookedMembers F).filter (fun S => c ∉ S)).card ≤ 8*N := by
  let H := CrookedMembers F
  let E := H.filter (fun S => c ∉ S)
  change E.card ≤ 8*N
  by_contra many
  have ne : E.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T,hT,minimal⟩ := Finset.exists_min_image E Finset.card ne
  have sub : H ⊆ F := Finset.filter_subset _ _
  have esub : E ⊆ F := (Finset.filter_subset _ _).trans sub
  have miss := (Finset.mem_filter.mp hT).2
  have proper : T ⊂ Ground N := Finset.ssubset_iff_subset_ne.mpr
    ⟨hF.1 T (esub hT),fun he => miss (he ▸ hc)⟩
  have sz : T.card < N := by simpa only [ground_card] using Finset.card_lt_card proper
  let s : ℝ := T.card
  let n : ℝ := N
  have nlo : (9000 : ℝ) ≤ n := by dsimp only [n]; exact_mod_cast lo
  have nhi : n ≤ 65535 := by dsimp only [n]; exact_mod_cast (show N ≤ 65535 by omega)
  have sl : (470 : ℝ) ≤ s := by
    dsimp only [s]
    exact_mod_cast large T (Finset.mem_filter.mp hT).1 miss
  have er : 8*n ≤ (E.card : ℝ) := by dsimp only [n]; exact_mod_cast (show 8*N ≤ E.card by omega)
  have mass : (E.card : ℝ)*(s^2/4) ≤ ∑ S ∈ F, ((Pool S).card : ℝ) := calc
    _ = ∑ _S ∈ E, (s^2/4) := by simp
    _ ≤ ∑ S ∈ E, ((Pool S).card : ℝ) := by
      apply Finset.sum_le_sum
      intro S hS
      have hs : s ≤ (S.card : ℝ) := by dsimp only [s]; exact_mod_cast minimal S hS
      have comp := pow_le_pow_left₀ (by linarith only [sl] : 0 ≤ s) hs 2
      have big := large S (Finset.mem_filter.mp hS).1 (Finset.mem_filter.mp hS).2
      exact (div_le_div_of_nonneg_right comp (by norm_num)).trans
        (pool_quarter (by omega : N ≤ 2^18) (hF.1 S (esub hS))
          (Finset.mem_filter.mp (Finset.mem_filter.mp hS).1).2 (by omega))
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg esub (fun _ _ _ => by positivity)
  have quad := MixedOmitter20258.actual_quadratic (by omega : 2 ≤ N) hF (esub hT) miss sz
  change ((RootPart H c).card : ℝ) ≤ s*n-(s^2+3*s)/2 at quad
  have high := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 470) sl 2
  have coeff : 0 ≤ 3*s^2/10-n := by linarith only [high,nhi]
  have product := mul_nonneg (sub_nonneg.mpr er) coeff
  have np : 0 < n := by linarith only [nlo]
  have pay : (E.card : ℝ)-8*n+(12/5)*s^2 ≤
      6*(∑ S ∈ F, ((Pool S).card : ℝ))/(5*n) := by
    apply (le_div_iff₀ (by positivity : 0 < 5*n)).mpr
    nlinarith only [mass,product]
  have joint := LargeOmitter20258.actual_joint (by omega : 1000 ≤ N) hi hF
  change ((F.filter IsAP).card : ℝ)+6*(1/(5*n))*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
    (129/800+250001/1000000)*n^2+13*n at joint
  rw [show 6*(1/(5*n))*(∑ S ∈ F, ((Pool S).card : ℝ)) =
    6*(∑ S ∈ F, ((Pool S).card : ℝ))/(5*n) by ring] at joint
  have part : (RootPart H c).card+E.card=H.card := Finset.card_filter_add_card_filter_not _
  have total : (F.filter IsAP).card+H.card=F.card := Finset.card_filter_add_card_filter_not _
  have partR : ((RootPart H c).card : ℝ)+E.card=H.card := by exact_mod_cast part
  have totalR : ((F.filter IsAP).card : ℝ)+H.card=F.card := by exact_mod_cast total
  have lower : (N.choose 2 : ℝ) ≤ F.card := by
    exact_mod_cast (show N.choose 2 ≤ F.card by unfold B at near; omega)
  rw [Nat.cast_choose_two] at lower
  change n*(n-1)/2 ≤ (F.card : ℝ) at lower
  have nn := mul_le_mul_of_nonneg_right nlo np.le
  nlinarith only [pay,joint,quad,partR,totalR,lower,sq_nonneg (29*s-5*n),nn,np,sl]

theorem actual_eight {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (lo : 9000 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N)
    (hF : Legal (Ground N) F) (near : B N ≤ F.card)
    (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) :
    ((CrookedMembers F).filter (fun S => c ∉ S)).card ≤ 8*N := by
  apply actual_eight_of_min lo hi hc hF near
  intro S hS miss
  obtain ⟨hSF,bad⟩ := Finset.mem_filter.mp hS
  have del : S ∈ Deleted N 12 F := by
    by_contra outside
    exact miss (root S (Finset.mem_sdiff.mpr ⟨hSF,outside⟩) bad)
  have := (Finset.mem_filter.mp del).2.2
  omega

theorem actual_omitted {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ}
    (lo : 9000 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N)
    (hF : Legal (Ground N) F) (near : B N ≤ F.card)
    (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) :
    (TerminalDeficit51.OmittedAvoiders N 12 F c).card ≤ 8*N := by
  apply (Finset.card_le_card ?_).trans (actual_eight lo hi hc hF near root)
  intro S hS
  obtain ⟨del,miss⟩ := Finset.mem_filter.mp hS
  obtain ⟨hSF,bad,_⟩ := Finset.mem_filter.mp del
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hSF,bad⟩,miss⟩

#print axioms pool_quarter
#print axioms actual_eight_of_min
#print axioms actual_eight
#print axioms actual_omitted
end
end JSP233.RootAvoiderCount20258
