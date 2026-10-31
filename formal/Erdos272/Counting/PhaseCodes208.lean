import Erdos272.Counting.PhaseDensity208
import Erdos272.Counting.ConflictBudget208

namespace JSP233.PhaseCodes208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

variable {α : Type*} [DecidableEq α]

def Compatible (code : α→ℕ×ℕ) (i j : α) : Prop :=
  ∃z : ℕ, z%(code i).1=(code i).2 ∧ z%(code j).1=(code j).2

theorem compatible_symm (code : α→ℕ×ℕ) : Symmetric (Compatible code) := by
  rintro i j ⟨z,hi,hj⟩
  exact ⟨z,hj,hi⟩

theorem independent_density (code : α→ℕ×ℕ) (C : Finset α)
    (hcode : ∀i∈C,code i∈PhaseDensity208.Codes)
    (hind : ConflictBudget208.Independent (Compatible code) C) :
    (∑i∈C,1/((code i).1 : ℝ))≤10/11 := by
  have hinj : Set.InjOn code (↑C : Set α) := by
    intro i hi j hj heq
    by_contra hne
    have hb := PhaseDensity208.mem_codes.mp (hcode i hi)
    have hz : (code i).2%(code i).1=(code i).2 := Nat.mod_eq_of_lt hb.2.2.2
    apply hind i hi j hj hne
    refine ⟨(code i).2,hz,?_⟩
    rwa [←heq]
  let K := C.image code
  have hK : K⊆PhaseDensity208.Codes := by
    intro c hc
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hc
    exact hcode i hi
  have hdisj : ∀z : ℕ,(K.filter (fun c => z%c.1=c.2)).card≤1 := by
    intro z
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haK,hza⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbK,hzb⟩ := Finset.mem_filter.mp hb
    obtain ⟨i,hi,hia⟩ := Finset.mem_image.mp haK
    obtain ⟨j,hj,hjb⟩ := Finset.mem_image.mp hbK
    by_cases heq : i=j
    · exact hia.symm.trans (heq ▸ hjb)
    · exact False.elim (hind i hi j hj heq ⟨z,by simpa only [hia] using hza,by simpa only [hjb] using hzb⟩)
  have hh := PhaseDensity208.actual_disjoint_density K hK hdisj
  dsimp only [K] at hh
  rw [Finset.sum_image hinj] at hh
  exact hh

theorem phase_conflict_bound (code : α→ℕ×ℕ) (C : Finset α)
    (hcode : ∀i∈C,code i∈PhaseDensity208.Codes) :
    (∑i∈C,1/((code i).1 : ℝ))≤10/11+
      ConflictBudget208.PairCost (Compatible code) (fun i => 1/((code i).1 : ℝ)) C/2 := by
  apply ConflictBudget208.weighted_budget (compatible_symm code)
  · intro i hi
    positivity
  · intro D hDC hD
    exact independent_density code D (fun i hi => hcode i (hDC hi)) hD

#print axioms independent_density
#print axioms phase_conflict_bound
end
end JSP233.PhaseCodes208
