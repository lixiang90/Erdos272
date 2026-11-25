module

public import Erdos272.Capacity.N20258.ScaledShadow20258
public import Erdos272.Resources.N158375.DensePool158375
public import Erdos272.Counting.N20258.ShortTransversal20258

@[expose] public section
/-! A single physical price closes the large-omitter exit on the low
window. The root members and the paid members are disjoint. -/
namespace JSP233.LargeOmitter20258
open StarCompletion APGeometry PrivatePairExistence Density41 HarmonicAbel29
open IntrinsicTriples208 SourceBridge208 SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

theorem pool_at_266 {N : ℕ} {S : Finset ℤ} (hN : N ≤ 2^18) (hS : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 266 ≤ S.card) : 17500 ≤ (Pool S).card := by
  have two : 2 ≤ S.card := by omega
  have card : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hS
  have core : MaxAPSize S ≤ 2^18 := (maxAPSize_le_card S).trans (card.trans hN)
  have sum : MaxAPSize S+Defect S=S.card := by
    have := maxAPSize_le_card S
    unfold Defect
    omega
  have one := MixedCore200000.crooked_defect_positive two bad
  have priced (k t u : ℕ) (hk : k ≤ Defect S) (ht : t ≤ MaxAPSize S) (ten : 10 ≤ t)
      (floor : 100*u+525*t ≤ 27*t*t) (target : 17500 ≤ k*u) : 17500 ≤ (Pool S).card :=
    target.trans ((Nat.mul_le_mul hk (AnalyticCore180000.floor_large ht core ten floor)).trans
      (CoreUnionSource200000.actual_union_core_source two))
  by_cases big : 132 ≤ Defect S
  · exact (by decide : 17500 ≤ 132*(132+1)).trans
      ((DensePool158375.physical_quadratic (s := S.card) (e := 132) (by omega)).trans
        (actual_source_of_defect two big))
  by_cases few : Defect S ≤ 1
  · exact priced 1 265 17500 one (by omega) (by decide) (by decide) (by decide)
  by_cases some : Defect S ≤ 4
  · exact priced 2 262 8750 (by omega) (by omega) (by decide) (by decide) (by decide)
  exact priced 5 135 3500 (by omega) (by omega) (by decide) (by decide) (by decide)

theorem pool_at_420 {N : ℕ} {S : Finset ℤ} (hN : N ≤ 2^18) (hS : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 420 ≤ S.card) : 17500 ≤ (Pool S).card :=
  pool_at_266 hN hS bad (by omega)

/-- A single choice of the seven-shadow multiplier controls both the AP
count and the resource spent on crooked members throughout this window. -/
theorem actual_joint {N : ℕ} {F : Finset (Finset ℤ)} (lo : 1000 ≤ N) (hi : N < 2^16)
    (hF : Legal (Ground N) F) :
    ((F.filter IsAP).card : ℝ) + 6*(1/(5*(N : ℝ)))*(∑ S ∈ F, ((Pool S).card : ℝ)) ≤
      (129/800+250001/1000000 : ℝ)*(N : ℝ)^2+13*N := by
  have bound := ScaledShadow20258.actual lo hi (by norm_num : (3 : ℝ) ≤ 5) hF
  have coeff : Alpha 1/5+(5 : ℝ)^2/(432*(Alpha 1)^2) ≤ 250001/1000000 := by
    rw [alpha_one]
    norm_num
  have scaled := mul_le_mul_of_nonneg_right coeff (sq_nonneg (N : ℝ))
  nlinarith only [bound,scaled,Nat.cast_nonneg (α := ℝ) N]

/-- If a sparse crooked omitter exists and every sparse crooked omitter
at the same site has at least 266 points, the entire family falls below
the conjectured bound throughout the transfer interval. -/
theorem actual_upper_at_266 {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 5040 ≤ N) (hi : N ≤ 21000) (hF : Legal (Ground N) F)
    (hT : T ∈ SparseCrooked N 12 F) (miss : c ∉ T)
    (omitters : ∀ S ∈ SparseCrooked N 12 F, c ∉ S → 266 ≤ S.card) :
    F.card ≤ N.choose 2+1 := by
  let H := CrookedMembers F
  let A := H.filter (fun S => c ∉ S)
  have sub : H ⊆ F := Finset.filter_subset _ _
  have legal : Legal (Ground N) H :=
    ⟨fun S hS => hF.1 S (sub hS),fun S hS U hU => hF.2 S (sub hS) U (sub hU)⟩
  have bad : ∀ S ∈ H, ¬IsAP S := fun _ hS => (Finset.mem_filter.mp hS).2
  obtain ⟨hTF,hTb,hTs⟩ := actual_sparse_membership.mp hT
  have hTH : T ∈ H := Finset.mem_filter.mpr ⟨hTF,hTb⟩
  have root := RootQuadratic208.actual_omitter_quadratic (by omega : 2 ≤ N) legal bad hTH miss (by omega)
  have small : 12*(T.card : ℝ) ≤ N := by exact_mod_cast hTs
  have square := mul_le_mul_of_nonneg_right small (Nat.cast_nonneg (α := ℝ) N)
  have rootCap : ((RootPart H c).card : ℝ) ≤ (N : ℝ)^2/12 := by
    nlinarith only [root,square,sq_nonneg (T.card : ℝ),Nat.cast_nonneg (α := ℝ) T.card]
  have unit (S : Finset ℤ) (hS : S ∈ A) : 17500 ≤ ((Pool S).card : ℝ) := by
    obtain ⟨hSH,hSc⟩ := Finset.mem_filter.mp hS
    have big : 266 ≤ S.card := by
      by_cases sparse : 12*S.card ≤ N
      · exact omitters S (actual_sparse_membership.mpr ⟨sub hSH,bad S hSH,sparse⟩) hSc
      · omega
    exact_mod_cast pool_at_266 (by omega : N ≤ 2^18) (hF.1 S (sub hSH)) (bad S hSH) big
  have Asub : A ⊆ F := (Finset.filter_subset _ _).trans sub
  have spent : (A.card : ℝ)*17500 ≤ ∑ S ∈ F, ((Pool S).card : ℝ) := calc
    _ = ∑ _S ∈ A, (17500 : ℝ) := by simp
    _ ≤ ∑ S ∈ A, ((Pool S).card : ℝ) := Finset.sum_le_sum unit
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Asub (fun _ _ _ => by positivity)
  let g : ℝ := 1/(5*(N : ℝ))
  have hn : (5040 : ℝ) ≤ N := by exact_mod_cast lo
  have hn0 : (0 : ℝ) < N := by linarith
  have hg : 0 ≤ g := by dsimp only [g]; positivity
  have rate : 1 ≤ 6*g*17500 := calc
    (1 : ℝ) ≤ 105000/(5*(N : ℝ)) := by
      apply (le_div_iff₀ (by positivity)).mpr
      have up : (N : ℝ) ≤ 21000 := by exact_mod_cast hi
      linarith
    _ = _ := by dsimp only [g]; ring
  have covered := mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg (α := ℝ) A.card)
  have pool := mul_le_mul_of_nonneg_left spent (by positivity : 0 ≤ 6*g)
  have jointBound := actual_joint (by omega : 1000 ≤ N) (by omega : N < 2^16) hF
  change _+6*g*_ ≤ _ at jointBound
  have split : (RootPart H c).card+A.card=H.card := Finset.card_filter_add_card_filter_not _
  have total : (F.filter IsAP).card+H.card = F.card := Finset.card_filter_add_card_filter_not _
  have splitR : ((RootPart H c).card : ℝ)+A.card = H.card := by exact_mod_cast split
  have totalR : ((F.filter IsAP).card : ℝ)+H.card = F.card := by exact_mod_cast total
  have lower := mul_le_mul_of_nonneg_right hn hn0.le
  have conclusion : (F.card : ℝ) ≤ (N.choose 2 : ℝ)+1 := by
    rw [Nat.cast_choose_two]
    nlinarith only [rootCap,covered,pool,jointBound,splitR,totalR,lower,hn]
  exact_mod_cast conclusion

theorem actual_upper {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 5040 ≤ N) (hi : N ≤ 21000) (hF : Legal (Ground N) F)
    (hT : T ∈ SparseCrooked N 12 F) (miss : c ∉ T)
    (omitters : ∀ S ∈ SparseCrooked N 12 F, c ∉ S → 420 ≤ S.card) :
    F.card ≤ N.choose 2+1 := actual_upper_at_266 lo hi hF hT miss
      (fun S hS hc => (by decide : 266 ≤ 420).trans (omitters S hS hc))

#print axioms pool_at_266
#print axioms actual_upper_at_266
#print axioms actual_upper
end
end JSP233.LargeOmitter20258
