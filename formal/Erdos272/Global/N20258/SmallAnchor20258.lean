module

public import Erdos272.Capacity.N20258.LongShadow20258
public import Erdos272.Capacity.N20258.FortyTwoPool20258
public import Erdos272.Global.N20258.SmallFortyOne20258
public import Erdos272.Counting.N20258.CoatomLayer20258

@[expose] public section
namespace JSP233.SmallAnchor20258
open StarCompletion APClasses88404 PrivatePairExistence IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- A cap on the entire crooked family suffices. All APs and all
intrinsic triples are counted on the same physical ground. -/
theorem of_cap {N : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258 ≤ N) (hi : N ≤ 2^15) (legal : Legal (Ground N) F)
    (large : ∀ S ∈ F, 42 ≤ S.card) (cap : (CrookedMembers F).card ≤ 1852*(N-2)) :
    F.card ≤ B N := by
  let H := CrookedMembers F
  let n : ℝ := (N : ℝ)-1
  let g : ℝ := 1/(5*n)
  let M : ℝ := ∑ S ∈ F, ((Pool S).card : ℝ)
  have lower : (20257 : ℝ) ≤ n := by
    have h : (20258 : ℝ) ≤ N := by exact_mod_cast lo
    dsimp only [n]; linarith only [h]
  have hp : 0 < n := by linarith
  have gp : 0 < g := by dsimp only [g]; positivity
  have scale : g*(5*n)=1 := by dsimp only [g]; field_simp
  have sub : H ⊆ F := Finset.filter_subset _ _
  have spent : 446*(H.card : ℝ) ≤ M := calc
    _ = ∑ _S ∈ H, (446 : ℝ) := by simp [mul_comm]
    _ ≤ ∑ S ∈ H, ((Pool S).card : ℝ) := Finset.sum_le_sum (fun S hS => by
      exact_mod_cast FortyTwoPool20258.member (by omega : N ≤ 2^18) (legal.1 S (sub hS))
        (Finset.mem_filter.mp hS).2 (large S (sub hS)))
    _ ≤ M := Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => by positivity)
  have joint := LongShadow20258.actual (by omega) hi legal (fun S hs _ => large S hs)
  change ((F.filter IsAP).card : ℝ)+6*g*M ≤ (411251/1000000 : ℝ)*n^2-6*n+7000 at joint
  have cost := mul_le_mul_of_nonneg_left spent (by positivity : 0 ≤ 6*g)
  have hcap : (H.card : ℝ) ≤ 1852*n := by
    have h : (H.card : ℝ) ≤ ((1852*(N-2) : ℕ) : ℝ) := by exact_mod_cast cap
    rw [Nat.cast_mul,Nat.cast_sub (by omega : 2 ≤ N)] at h
    norm_num only [Nat.cast_ofNat] at h
    dsimp only [n]; linarith only [h]
  have wpos : 0 ≤ 1-2676*g := by
    have h : (2676 : ℝ)/(5*n) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith only [lower])
    dsimp only [g]
    linarith only [h,show (2676 : ℝ)*(1/(5*n))=2676/(5*n) by ring]
  have rem := mul_le_mul_of_nonneg_left hcap wpos
  have split : ((F.filter IsAP).card : ℝ)+(H.card : ℝ)=F.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := F) IsAP
  have two : (F.card : ℝ) ≤ (N.choose 2 : ℝ) := by
    rw [Nat.cast_choose_two]
    change _ ≤ (N : ℝ)*((N : ℝ)-1)/2
    have hn : (N : ℝ)=n+1 := by dsimp only [n]; ring
    rw [hn]
    nlinarith only [joint,cost,rem,split,scale,lower,sq_nonneg (n-20257)]
  have bound : F.card ≤ N.choose 2 := by exact_mod_cast two
  unfold B
  omega

private theorem minimum {N m : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258 ≤ N) (hi : N ≤ 2^15) (legal : Legal (Ground N) F) (counter : B N < F.card)
    (m45 : m ≤ 45) (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    ∀ S ∈ F, 42 ≤ S.card := by
  intro S hS
  by_contra! small
  exact (not_lt_of_ge (SmallFortyOne20258.actual_upper lo (by omega) legal hS (by omega) (by
    intro x hx
    obtain ⟨T,hT,miss,sz⟩ := omits x hx
    exact ⟨T,hT,miss,sz.trans m45⟩))) counter

/-- An actual member, including an AP, provides the requisite cap. In
particular this discharges the size-42 exit at cutoff 45 in one step. -/
theorem of_member {N m : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (lo : 20258 ≤ N) (hi : N ≤ 2^15) (legal : Legal (Ground N) F)
    (m45 : m ≤ 45) (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ m)
    (member : P ∈ F) (price : (m-1)*P.card+1 ≤ 1852) : F.card ≤ B N := by
  by_contra! counter
  have sizes := minimum lo hi legal counter m45 omits
  have pos := sizes P member
  have bound := TwoTransversals20258.actual_member (by omega : 2 ≤ N) (by omega : m+1 ≤ N)
    legal member (Finset.card_pos.mp (by omega)) omits
  exact (not_lt_of_ge (of_cap lo hi legal sizes (bound.trans (Nat.mul_le_mul_right _ price)))) counter

/-- If the first cutoff is at most 44, a counterexample needs only
44-site small witnesses, and there are at most 44N of them. -/
theorem at_44 {N : ℕ} {F : Finset (Finset ℤ)}
    (lo : 20258 ≤ N) (hi : N ≤ 2^15) (legal : Legal (Ground N) F) (counter : B N < F.card)
    (omits : ∀ x ∈ Ground N, ∃ T ∈ CrookedMembers F, x ∉ T ∧ T.card ≤ 44) :
    (∀ S ∈ F, 44 ≤ S.card) ∧ ((CrookedMembers F).filter (fun S => S.card=44)).card ≤ 44*N := by
  have sizes := minimum lo hi legal counter (by decide : 44 ≤ 45) omits
  constructor
  · intro S hS
    by_contra! small
    exact (not_lt_of_ge (of_member lo hi legal (by decide) omits hS (by omega))) counter
  · rcases CoatomLayer20258.actual (by decide : 5 ≤ 44) (by omega : 44+1 ≤ N) legal omits with cap | layer
    · exact False.elim ((not_lt_of_ge (of_cap lo hi legal sizes cap)) counter)
    · exact layer

#print axioms of_cap
#print axioms of_member
#print axioms at_44
end
end JSP233.SmallAnchor20258
