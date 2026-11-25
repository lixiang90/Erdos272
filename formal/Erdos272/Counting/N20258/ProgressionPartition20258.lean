module

public import Erdos272.Counting.N20258.ProgressionTail20258
public import Erdos272.Counting.N20258.ShortTransversal20258
public import Erdos272.Counting.N80470.APQuotient80470

@[expose] public section
namespace JSP233.ProgressionPartition20258
open StarCompletion APCount41 APClasses88404 ProgressionTail20258
open ProgressionLengths20258 ShortTransversal20258
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false

/-- Sum over all short-length-truncated strides outside the classes charged
separately to the shadows of the original family. -/
def offTail (n k : ℕ) (kept : Finset ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 n \ kept, tail (n/d) k

theorem actual_AP_partition {N k : ℕ} {F : Finset (Finset ℤ)}
    (hN : 1 ≤ N) (hF : Legal (Ground N) F) (kept : Finset ℕ)
    (hkept : kept ⊆ Finset.Icc 1 (N-1))
    (hmin : ∀ d ∈ Finset.Icc 1 (N-1) \ kept, ∀ S ∈ StepAP F d, k < S.card) :
    (F.filter IsAP).card ≤ 1 + (∑ d ∈ kept, (StepAP F d).card) + offTail (N-1) k kept := by
  let P := F.filter IsAP
  let A := P.filter fun S => 2 ≤ S.card
  let C := P.filter fun S => ¬2 ≤ S.card
  have part : A.card + C.card = P.card := Finset.card_filter_add_card_filter_not _
  have hCF : C ⊆ F := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have small : C.card ≤ 1 := actual_singleton_family_count
    ⟨fun S hS => hF.1 S (hCF hS), fun S hS T hT => hF.2 S (hCF hS) T (hCF hT)⟩
    (fun S hS => by have := (Finset.mem_filter.mp hS).2; omega)
  have maps : ∀ S ∈ A, Step S ∈ Finset.Icc 1 (N-1) := by
    intro S hS
    obtain ⟨hP,htwo⟩ := Finset.mem_filter.mp hS
    obtain ⟨hSF,hAP⟩ := Finset.mem_filter.mp hP
    exact Finset.mem_Icc.mpr ⟨(actual_step hAP).1,APQuotient80470.actual_step_span (hF.1 S hSF) hAP htwo⟩
  have all : A.card = ∑ d ∈ Finset.Icc 1 (N-1), (StepAP F d).card := by
    rw [Finset.card_eq_sum_card_fiberwise maps]
    apply Finset.sum_congr rfl
    intro d _
    congr 1
    ext S
    simp only [A,P,StepAP,Finset.mem_filter]
    tauto
  have outer : (∑ d ∈ Finset.Icc 1 (N-1) \ kept, (StepAP F d).card) ≤ offTail (N-1) k kept :=
    Finset.sum_le_sum fun d hd =>
      actual_step_tail hN (Finset.mem_Icc.mp (Finset.mem_sdiff.mp hd).1).1 hF (hmin d hd)
  have split := Finset.sum_sdiff (f := fun d => (StepAP F d).card) hkept
  change P.card ≤ _
  omega

/-- If the shortest progression has length l, its incidence bound pays the
crooked members and the exact length tails pay all progression classes. -/
theorem actual_shortest_bound {N m l : ℕ} {F : Finset (Finset ℤ)} {P : Finset ℤ}
    (hN : 2 ≤ N) (hm : m+2 ≤ N) (hF : Legal (Ground N) F)
    (hP : P ∈ F) (hAP : IsAP P) (length : P.card = l)
    (minimal : ∀ S ∈ F, IsAP S → l ≤ S.card)
    (omits : ∀ x ∈ P, ∃ T ∈ PrivatePairExistence.CrookedMembers F, x ∉ T ∧ T.card ≤ m) :
    (F.card : ℝ) ≤ l*rootPrice N m+1+offTail (N-1) (l-1) ∅ := by
  have positive : 0 < l := length ▸ Finset.card_pos.mpr (isAP_nonempty hAP)
  have A := actual_AP_partition (N := N) (k := l-1) (by omega) hF ∅ (by simp)
    (fun d _ S hS => by have := minimal S (APClasses88404.subset F d hS) (is_ap hS); omega)
  simp only [Finset.sum_empty, Nat.add_zero] at A
  have bad := actual_short_transversal hN hm hF hP hAP omits
  rw [length] at bad
  have total : (F.filter IsAP).card + (PrivatePairExistence.CrookedMembers F).card = F.card :=
    Finset.card_filter_add_card_filter_not _
  have AR : ((F.filter IsAP).card : ℝ) ≤ 1+(offTail (N-1) (l-1) ∅ : ℕ) := by exact_mod_cast A
  have FR : ((F.filter IsAP).card : ℝ)+(PrivatePairExistence.CrookedMembers F).card = F.card := by
    exact_mod_cast total
  linarith only [bad,AR,FR]

end
end JSP233.ProgressionPartition20258
