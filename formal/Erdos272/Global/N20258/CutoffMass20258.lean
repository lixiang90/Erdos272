module

public import Erdos272.Capacity.N20258.ScaledShadow20258
public import Erdos272.Resources.N158375.DensePool158375
public import Erdos272.Counting.N20258.MixedOmitter20258

@[expose] public section
namespace JSP233.CutoffMass20258
open StarCompletion APGeometry PrivatePairExistence IntrinsicTriples208 SourceBridge208
open SparseSmall39 AnchorCompletion38 SieveConstants88404
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- A 197-site crooked set pays at least 10050 distinct intrinsic triples. -/
theorem mass_at_197 {N : ℕ} {S : Finset ℤ} (hi : N ≤ 2^18) (inGround : S ⊆ Ground N)
    (bad : ¬IsAP S) (large : 197 ≤ S.card) : 10050 ≤ (Pool S).card := by
  have two : 2 ≤ S.card := by omega
  have size : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card inGround
  have core : MaxAPSize S ≤ 2^18 := (maxAPSize_le_card S).trans (size.trans hi)
  have split : MaxAPSize S+Defect S=S.card := by
    have := maxAPSize_le_card S
    unfold Defect
    omega
  have one := MixedCore200000.crooked_defect_positive two bad
  have pay (k t u : ℕ) (hk : k ≤ Defect S) (ht : t ≤ MaxAPSize S) (three : 3 ≤ t)
      (price : 100*u+150*t ≤ 27*t*t) (tail : 100*u+525*257 ≤ 27*257*257) (fee : 10050 ≤ k*u) : 10050 ≤ (Pool S).card :=
    fee.trans ((Nat.mul_le_mul hk (AnalyticCore180000.floor_split ht core three price tail)).trans
      (CoreUnionSource200000.actual_union_core_source two))
  by_cases big : 100 ≤ Defect S
  · exact (by decide : 10050 ≤ 100*(100+1)).trans
      ((DensePool158375.physical_quadratic (s := S.card) (e := 100) (by omega)).trans
        (actual_source_of_defect two big))
  by_cases single : Defect S ≤ 1
  · exact pay 1 196 10050 one (by omega) (by decide) (by decide) (by decide) (by decide)
  by_cases few : Defect S ≤ 4
  · exact pay 2 193 5025 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)
  exact pay 5 98 2010 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide)

/-- At the first empty kernel, the true root omitter has only m sites.
Use its degree for the root, then spend the triple pool on its complement. -/
theorem below_197 {N m : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 20000 ≤ N) (hi : N ≤ 21000) (legal : Legal (Ground N) F) (counter : B N < F.card)
    (top : m ≤ 265) (hT : T ∈ CrookedMembers F) (miss : c ∉ T) (size : T.card=m)
    (minimal : ∀ S ∈ CrookedMembers F, c ∉ S → m ≤ S.card) : m ≤ 196 := by
  by_contra! large
  let H := CrookedMembers F
  let A := H.filter (fun S => c ∉ S)
  let M : ℝ := ∑ S ∈ F, ((Pool S).card : ℝ)
  have nlo : (20000 : ℝ) ≤ N := by exact_mod_cast lo
  have nhi : (N : ℝ) ≤ 21000 := by exact_mod_cast hi
  have np : (0 : ℝ) < N := by linarith
  have sub : A ⊆ F := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have unit (S : Finset ℤ) (hS : S ∈ A) : (10050 : ℝ) ≤ (Pool S).card := by
    obtain ⟨sh,sc⟩ := Finset.mem_filter.mp hS
    exact_mod_cast mass_at_197 (by omega : N ≤ 2^18) (legal.1 S (sub hS))
      (Finset.mem_filter.mp sh).2 (le_trans (by omega : 197 ≤ m) (minimal S sh sc))
  have spent : 10050*(A.card : ℝ) ≤ M := calc
    _ = ∑ _S ∈ A, (10050 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ S ∈ A, ((Pool S).card : ℝ) := Finset.sum_le_sum unit
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have raw := IntrinsicTriples208.actual_capacity legal
  rw [ground_card] at raw
  have pool : M ≤ (N.choose 3 : ℝ) := by
    dsimp only [M]
    exact_mod_cast raw
  rw [APResidual208.cast_choose_three] at pool
  have square := mul_le_mul_of_nonneg_right nhi np.le
  have cube := mul_le_mul_of_nonneg_right square np.le
  have few : (A.card : ℝ) ≤ 7350*N := by
    nlinarith only [spent,pool,square,cube,nlo,
      mul_nonneg (show (0 : ℝ) ≤ N by positivity) (by linarith : 0 ≤ 3*(N : ℝ)-2)]
  have rate : (67/70 : ℝ) ≤ 6*(1/(3*(N : ℝ)))*10050 := by
    field_simp [np.ne']
    linarith only [nhi]
  have covered := mul_le_mul_of_nonneg_right rate (Nat.cast_nonneg (α := ℝ) A.card)
  have weighted := mul_le_mul_of_nonneg_left spent (show 0 ≤ 6*(1/(3*(N : ℝ))) by positivity)
  have root := MixedOmitter20258.actual_degree legal (Finset.mem_filter.mp hT).1 miss
  rw [size] at root
  have cb := degreeBudget_closed N m (by omega) (by omega)
  have rnat : (RootPart H c).card ≤ 265*N :=
    root.trans ((by omega : DegreeBudget N m ≤ m*(N-2)).trans (Nat.mul_le_mul top (Nat.sub_le _ _)))
  have rreal : ((RootPart H c).card : ℝ) ≤ 265*N := by exact_mod_cast rnat
  have joint := ScaledShadow20258.actual (k := 3) (by omega : 1000 ≤ N) (by omega : N < 2^16)
    (by norm_num) legal
  have coeff : (129/800+(Alpha 1/3+3^2/(432*(Alpha 1)^2)) : ℝ) ≤ 47/100 := by
    rw [alpha_one]
    norm_num
  have scaled := mul_le_mul_of_nonneg_right coeff (sq_nonneg (N : ℝ))
  have splitR : ((RootPart H c).card : ℝ)+A.card = H.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := H) (fun S => c ∈ S)
  have totalR : ((F.filter IsAP).card : ℝ)+H.card = F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
  have target : (N.choose 2 : ℝ) < F.card := by
    exact_mod_cast (show N.choose 2 < F.card by unfold B at counter; omega)
  rw [Nat.cast_choose_two] at target
  change ((F.filter IsAP).card : ℝ)+6*(1/(3*(N : ℝ)))*M ≤ _ at joint
  have residual : (A.card : ℝ) ≤ 6*(1/(3*(N : ℝ)))*M+315*N := by
    linarith only [covered,weighted,few]
  nlinarith only [joint,scaled,rreal,residual,splitR,totalR,target,mul_le_mul_of_nonneg_right nlo np.le,nlo]

#print axioms mass_at_197
#print axioms below_197
end
end JSP233.CutoffMass20258
