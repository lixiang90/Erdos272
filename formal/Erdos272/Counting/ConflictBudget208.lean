import Mathlib.Tactic

/-! Delete the smaller endpoint of a conflicting pair. Ordered pairs are
counted twice, so the exact charge is one half of their symmetric cost. -/
namespace JSP233.ConflictBudget208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

variable {α : Type*} [DecidableEq α]

def Cost (R : α→α→Prop) (w : α→ℝ) (i j : α) : ℝ :=
  if i=j then 0 else if R i j then min (w i) (w j) else 0

def PairCost (R : α→α→Prop) (w : α→ℝ) (C : Finset α) : ℝ :=
  ∑i∈C,∑j∈C,Cost R w i j

def Independent (R : α→α→Prop) (C : Finset α) : Prop :=
  ∀i∈C,∀j∈C,i≠j→¬R i j

theorem cost_nonneg {R : α→α→Prop} {w : α→ℝ} {i j : α}
    (hi : 0≤w i) (hj : 0≤w j) : 0≤Cost R w i j := by
  unfold Cost
  split_ifs <;> positivity

theorem cost_symm {R : α→α→Prop} (hR : Symmetric R) (w : α→ℝ) (i j : α) :
    Cost R w i j=Cost R w j i := by
  by_cases he : i=j
  · subst j
    rfl
  · have he' := Ne.symm he
    have hr : R i j ↔ R j i := ⟨fun h => hR h,fun h => hR h⟩
    simp only [Cost,if_neg he,if_neg he',hr,min_comm]

theorem paircost_nonneg {R : α→α→Prop} {w : α→ℝ} {C : Finset α}
    (hw : ∀i∈C,0≤w i) : 0≤PairCost R w C :=
  Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => cost_nonneg (hw i hi) (hw j hj)

theorem paircost_insert {R : α→α→Prop} (hR : Symmetric R) (w : α→ℝ)
    {C : Finset α} {i : α} (hi : i∉C) :
    PairCost R w (insert i C)=PairCost R w C+2*(∑j∈C,Cost R w i j) := by
  have hs : (∑j∈C,Cost R w j i)=∑j∈C,Cost R w i j :=
    Finset.sum_congr rfl (fun j _ => cost_symm hR w j i)
  simp only [PairCost,Finset.sum_insert hi,Cost,ite_true,zero_add,
    Finset.sum_add_distrib]
  change (∑j∈C,Cost R w i j)+((∑j∈C,Cost R w j i)+
    (∑j∈C,∑k∈C,Cost R w j k))=(∑j∈C,∑k∈C,Cost R w j k)+2*(∑j∈C,Cost R w i j)
  rw [hs]
  ring

theorem weighted_budget {R : α→α→Prop} (hR : Symmetric R) (w : α→ℝ)
    (C : Finset α) (mu : ℝ) (hw : ∀i∈C,0≤w i)
    (hbound : ∀D⊆C,Independent R D → (∑i∈D,w i)≤mu) :
    (∑i∈C,w i)≤mu+PairCost R w C/2 := by
  revert hw hbound
  refine Finset.strongInductionOn C ?_
  intro C ih hw hbound
  by_cases hind : Independent R C
  · exact (hbound C le_rfl hind).trans
      (le_add_of_nonneg_right (div_nonneg (paircost_nonneg hw) (by norm_num)))
  · have hex : ∃i∈C,∃j∈C,i≠j ∧ R i j ∧ w i≤w j := by
      simp only [Independent] at hind
      push Not at hind
      obtain ⟨i,hi,j,hj,hij,hRij⟩ := hind
      rcases le_total (w i) (w j) with hle | hle
      · exact ⟨i,hi,j,hj,hij,hRij,hle⟩
      · exact ⟨j,hj,i,hi,hij.symm,hR hRij,hle⟩
    obtain ⟨i,hi,j,hj,hij,hRij,hle⟩ := hex
    let D := C.erase i
    have hDC : D⊆C := Finset.erase_subset _ _
    have hstrict : D⊂C := Finset.erase_ssubset hi
    have hd := ih D hstrict (fun x hx => hw x (hDC hx))
      (fun E hED hE => hbound E (hED.trans hDC) hE)
    have hjD : j∈D := Finset.mem_erase.mpr ⟨hij.symm,hj⟩
    have hcost : Cost R w i j=w i := by simp [Cost,hij,hRij,min_eq_left hle]
    have hsingle := Finset.single_le_sum (f := fun x => Cost R w i x)
      (fun x hx => cost_nonneg (R := R) (hw i hi) (hw x (hDC hx))) hjD
    rw [hcost] at hsingle
    have hpc := paircost_insert hR w (show i∉D from Finset.notMem_erase i C)
    rw [Finset.insert_erase hi] at hpc
    have hsum : (∑x∈D,w x)+w i=∑x∈C,w x := Finset.sum_erase_add _ _ hi
    linarith only [hd,hsingle,hpc,hsum]

#print axioms weighted_budget
end
end JSP233.ConflictBudget208
