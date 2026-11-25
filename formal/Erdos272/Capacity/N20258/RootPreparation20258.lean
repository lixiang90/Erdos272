module

public import Erdos272.Capacity.N20258.LargeOmitter20258
public import Erdos272.Counting.N20258.MixedOmitter20258

@[expose] public section

namespace JSP233.RootPreparation20258
open StarCompletion DenseDeletion40 PrivatePairExistence IntrinsicTriples208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Every member missing the retained root is large, including progressions
in the original family. The same multiplier pays all crooked avoiders. -/
theorem actual_omitter_size {N : ℕ} {F : Finset (Finset ℤ)} {c : ℤ} {T : Finset ℤ}
    (lo : 11000 ≤ N) (hi : N < 2^16) (hF : Legal (Ground N) F) (near : B N ≤ F.card)
    (root : ∀ S ∈ Retained N 12 F, ¬IsAP S → c ∈ S) (hT : T ∈ F) (miss : c ∉ T) :
    11*N < 120*T.card := by
  by_contra h
  have small : 120*T.card ≤ 11*N := by omega
  let H := CrookedMembers F
  let A := H.filter (fun S => c ∉ S)
  have sub : H ⊆ F := Finset.filter_subset _ _
  have Asub : A ⊆ F := (Finset.filter_subset _ _).trans sub
  have paid (S : Finset ℤ) (hS : S ∈ A) : (5*(N : ℝ))/6 ≤ (Pool S).card := by
    obtain ⟨hSH,hc⟩ := Finset.mem_filter.mp hS
    have bad : ¬IsAP S := (Finset.mem_filter.mp hSH).2
    have del : S ∈ Deleted N 12 F := by
      by_contra outside
      exact hc (root S (Finset.mem_sdiff.mpr ⟨sub hSH,outside⟩) bad)
    have dense := (Finset.mem_filter.mp del).2.2
    by_cases low : N ≤ 21000
    · have p := LargeOmitter20258.pool_at_420 (by omega : N ≤ 2^18) (hF.1 S (sub hSH))
        bad (by omega : 420 ≤ S.card)
      have p' : (17500 : ℝ) ≤ (Pool S).card := by exact_mod_cast p
      have n' : (N : ℝ) ≤ 21000 := by exact_mod_cast low
      linarith
    · have p := DensePool158375.actual_large_member (by omega : N ≤ 2^18) (hF.1 S (sub hSH))
        bad (by omega : 1250 ≤ S.card)
      have p' : (180200 : ℝ) ≤ (Pool S).card := by exact_mod_cast p
      have n' : (N : ℝ) ≤ 65535 := by exact_mod_cast (show N ≤ 65535 by omega)
      linarith
  have mass : (A.card : ℝ)*(5*N/6 : ℝ) ≤ ∑ S ∈ F, ((Pool S).card : ℝ) := calc
    _ = ∑ _S ∈ A, (5*(N : ℝ)/6) := by simp
    _ ≤ ∑ S ∈ A, ((Pool S).card : ℝ) := Finset.sum_le_sum paid
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Asub (fun _ _ _ => by positivity)
  have nlo : (11000 : ℝ) ≤ N := by exact_mod_cast lo
  have np : (0 : ℝ) < N := by linarith
  let g : ℝ := 1/(5*(N : ℝ))
  have rate : 6*g*(5*(N : ℝ)/6)=1 := by dsimp [g]; field_simp
  have cost := mul_le_mul_of_nonneg_left mass (show 0 ≤ 6*g by dsimp [g]; positivity)
  have scale := congrArg (fun v : ℝ => v*A.card) rate
  have joint := LargeOmitter20258.actual_joint (by omega : 1000 ≤ N) hi hF
  change _+6*g*_ ≤ _ at joint
  have quad := MixedOmitter20258.actual_quadratic (by omega : 2 ≤ N) hF hT miss (by omega)
  unfold ShortTransversal20258.rootPrice at quad
  have sr : 120*(T.card : ℝ) ≤ 11*N := by exact_mod_cast small
  have sq := mul_nonneg (show 0 ≤ 11*(N : ℝ)/120-T.card by linarith only [sr])
    (show 0 ≤ (N : ℝ)-(11*N/120+T.card)/2 by linarith only [sr,np])
  have rootCap : ((RootPart H c).card : ℝ) ≤ (11/120-(11/120)^2/2)*(N : ℝ)^2 := by
    change ((RootPart (CrookedMembers F) c).card : ℝ) ≤ _
    nlinarith only [quad,sq,Nat.cast_nonneg (α := ℝ) T.card]
  have part : (RootPart H c).card+A.card=H.card := Finset.card_filter_add_card_filter_not _
  have allPart : (F.filter IsAP).card+H.card=F.card := Finset.card_filter_add_card_filter_not _
  have partR : ((RootPart H c).card : ℝ)+A.card=H.card := by exact_mod_cast part
  have totalR : ((F.filter IsAP).card : ℝ)+H.card=F.card := by exact_mod_cast allPart
  have lower : (N.choose 2 : ℝ) ≤ F.card := by
    exact_mod_cast (show N.choose 2 ≤ F.card by unfold B at near; omega)
  rw [Nat.cast_choose_two] at lower
  have gap := mul_le_mul_of_nonneg_right nlo np.le
  nlinarith only [joint,cost,scale,rootCap,partR,totalR,lower,gap,np]

#print axioms actual_omitter_size
end
end JSP233.RootPreparation20258
