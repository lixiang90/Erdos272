module

public import Erdos272.Capacity.N20258.RootAvoiderCount20258
public import Erdos272.Counting.N65172.StarLower65172
public import Erdos272.Counting.N67702.LowStepPayment67702
public import Erdos272.Counting.N20258.RootedArms20258

@[expose] public section
namespace JSP233.RetainedStar20258
open StarCompletion StarResources30 CrossLine30 JointResources31 HarmonicAbel29 DenseDeletion40
open LowSteps32 APGeometry StarMidpoint67702 PrivatePairExistence
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- The ten smallest possible positive steps contain more than 8,100,000 members.
Some step therefore pays its full surplus, leaving at most nine small classes. -/
theorem small_kernel {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (lo : 19227 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N) (legal : Legal (Ground N) F)
    (two : 2 ≤ (Avoiders F c).card) (ker : (CommonKernel (Ground N) F c).card ≤ 1)
    (count : (Avoiders F c).card ≤ 8*N) : F.card ≤ B N := by
  by_contra failure
  have counter : N.choose 2+1 ≤ F.card := by unfold B at failure; omega
  let n : ℝ := ((N-1 : ℕ) : ℝ)
  let A := APLarge (RootPart F c)
  let total := ∑ d ∈ LowActive 10 c A, ((StepClass A (trueStep c) (d : ℤ)).card : ℝ)
  have hg : ∀ S ∈ A, S ⊆ Ground N := fun S hs =>
    legal.1 S (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).1
  have ha : ∀ S ∈ A, IsAP S := fun _ hs => (Finset.mem_filter.mp hs).2.1
  have hr : Rooted A c := fun _ hs => (Finset.mem_filter.mp (Finset.mem_filter.mp hs).1).2
  have hl : ∀ S ∈ A, 4 ≤ S.card := fun _ hs => (Finset.mem_filter.mp hs).2.2
  have low := StarLower65172.actual_AP_lower (by omega : 7 ≤ N) hc legal two ker counter
  change n^2/18-7/2*n-2*(Avoiders F c).card+1 ≤ (A.card : ℝ) at low
  have tail := RootedArms20258.actual_ten hi hg ha hr hl hc
  change (A.card : ℝ) ≤ total+n^2/42+(25/2)*n+1641 at tail
  have np : 0 ≤ n := Nat.cast_nonneg _
  have eqn : (N : ℝ) = n+1 := by
    dsimp only [n]
    exact_mod_cast (show N = N-1+1 by omega)
  have q : ((Avoiders F c).card : ℝ) ≤ 8*(n+1) := by
    rw [←eqn]
    exact_mod_cast count
  have kr : ((CommonKernel (Ground N) F c).card : ℝ) ≤ 1 := by exact_mod_cast ker
  have near : ((N-1).choose 2 : ℝ)+n+1 ≤ F.card := by
    have hid := StarBudget30.small_budget_identity N (by omega : 1 ≤ N)
    have hidR : (N.choose 2 : ℝ)+1 = (N : ℝ)+((N-1).choose 2 : ℝ) := by exact_mod_cast hid.symm
    have cr : (N.choose 2 : ℝ)+1 ≤ F.card := by exact_mod_cast counter
    linarith only [eqn,cr,hidR]
  have nlo : 19226 ≤ n := by dsimp only [n]; exact_mod_cast (show 19226 ≤ N-1 by omega)
  have sq := mul_nonneg (sub_nonneg.mpr nlo) np
  have bottom : 2*n^2/63-16*n-2*(Avoiders F c).card-1640 ≤ total := by
    linarith only [low,tail]
  obtain ⟨k,km,full,budget⟩ := actual_unpaid_steps_at 10 810000 (by decide) hc legal
  have big : 8100000 < total := by nlinarith only [bottom,q,sq,nlo]
  have kn : k ≤ 9 := by
    by_contra! hk
    have le := full (by omega)
    change total ≤ (10 : ℝ)*810000 at le
    linarith only [big,le]
  have knR : (k : ℝ) ≤ 9 := by exact_mod_cast kn
  change (F.card : ℝ)+(total-(k : ℝ)*810000)/21 ≤
    (Avoiders F c).card+(CommonKernel (Ground N) F c).card+((N-1).choose 2 : ℕ)+n/4 at budget
  nlinarith only [bottom,q,kr,near,budget,knR,sq,nlo]

/-- If the entire retained family has a common point, the desired bound applies
to the original legal family, including all deleted members. -/
theorem actual_upper {N : ℕ} {c : ℤ} {F : Finset (Finset ℤ)}
    (lo : 19227 ≤ N) (hi : N < 2^16) (hc : c ∈ Ground N)
    (legal : Legal (Ground N) F) (root : Rooted (Retained N 12 F) c) : F.card ≤ B N := by
  by_cases near : B N ≤ F.card
  · have sub : Avoiders F c ⊆ Deleted N 12 F := by
      intro S hs
      obtain ⟨mem,miss⟩ := Finset.mem_filter.mp hs
      by_contra nd
      exact miss (root S (Finset.mem_sdiff.mpr ⟨mem,nd⟩))
    have bad : ∀ S ∈ Avoiders F c, ¬ IsAP S := fun _ hs => (Finset.mem_filter.mp (sub hs)).2.1
    by_cases two : 2 ≤ (Avoiders F c).card
    · by_cases large : 2 ≤ (CommonKernel (Ground N) F c).card
      · have paid := AnchorCompletion38.actual_crooked_large_kernel_payment N F c hc legal two large bad
        omega
      · apply small_kernel lo hi hc legal two (by omega)
        apply (Finset.card_le_card ?_).trans
          (RootAvoiderCount20258.actual_eight (by omega : 9000 ≤ N) hi hc legal near
            (fun S hs _ => root S hs))
        intro S hs
        obtain ⟨mem,miss⟩ := Finset.mem_filter.mp hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem,bad S hs⟩,miss⟩
    · apply StarBoundConcrete30.best_omitter_threshold_unconditional N F c hc legal bad
      exact (show (Avoiders F c).card ≤ 5*N/6 by omega).trans (le_max_right _ _)
  · omega

#print axioms small_kernel
#print axioms actual_upper
end
end JSP233.RetainedStar20258
