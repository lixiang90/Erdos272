module

public import Erdos272.Arithmetic.WindowCounts208

@[expose] public section

namespace JSP233.WindowSums208
open LightClosed208 WindowCounts208
open scoped BigOperators
set_option maxHeartbeats 0

def RightSum (q A J B : ℕ) : ℕ :=
  ∑ r∈Finset.Ico (RightLeft q J B) (Count q A B),(q+1-r*B)
def rightWeight (q A J B : ℕ) : ℕ :=
  rightIndexCount q A J B*(q+1)-B*(Tri (Count q A B)-Tri (RightLeft q J B))
def Full (A J B : ℕ) : ℕ :=
  Count J A B*(J+1)-B*Tri (Count J A B)
def maximum_sum (A J B lo hi : ℕ) : ℕ :=
  max (rightWeight hi A J B)
    (if J≤hi ∧ lo≤Last J B hi then Full A J B else 0)

theorem rightSum_eq_closed {q A J B : ℕ} (hB : 0<B) (hAJ : A≤J) :
    RightSum q A J B=rightWeight q A J B := by
  have hb : ∀ r∈Finset.Ico (RightLeft q J B) (Count q A B),B*r≤q+1 := by
    intro r hr
    have hh := (lt_count hB).mp (Finset.mem_Ico.mp hr).2
    nlinarith
  unfold RightSum rightWeight rightIndexCount
  simp_rw [Nat.mul_comm _ B]
  rw [Finset.sum_tsub_distrib _ hb]
  simp only [Finset.sum_const,Nat.card_Ico,smul_eq_mul]
  rw [←Finset.mul_sum,sum_Ico_id (rightLeft_le_count hB hAJ)]

theorem full_sum {A J B : ℕ} (hB : 0<B) :
    (∑ r∈Finset.range (Count J A B),(J+1-r*B))=Full A J B := by
  have hb : ∀ r∈Finset.range (Count J A B),B*r≤J+1 := by
    intro r hr
    have hh := (lt_count hB).mp (Finset.mem_range.mp hr)
    nlinarith
  unfold Full
  simp_rw [Nat.mul_comm _ B]
  rw [Finset.sum_tsub_distrib _ hb]
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul]
  rw [←Finset.mul_sum,Finset.sum_range_id]
  rfl

theorem rightSum_le_full {q A J B : ℕ} (hB : 0<B) : RightSum q A J B≤Full A J B := by
  let u:=RightLeft q J B
  let n:=rightIndexCount q A J B
  have hc : q≤J+u*B := (rightLeft_le hB).mp le_rfl
  have hn : n≤Count J A B := rightCount_le_period hB
  have hs : RightSum q A J B=(∑ i∈Finset.range n,(q+1-(u+i)*B)) := by
    unfold RightSum
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    rfl
  rw [hs]
  calc
    _ ≤ ∑ i∈Finset.range n,(J+1-i*B) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Nat.add_mul]
      omega
    _ ≤ ∑ i∈Finset.range (Count J A B),(J+1-i*B) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) (by intros;exact Nat.zero_le _)
    _ = Full A J B := full_sum hB

theorem rightSum_mono {q hi A J B : ℕ} (hB : 0<B) (hqh : q≤hi)
    (hleft : RightLeft q J B=RightLeft hi J B) : RightSum q A J B≤RightSum hi A J B := by
  have hcount := count_mono (A:=A) hB hqh
  have hsub : Finset.Ico (RightLeft q J B) (Count q A B) ⊆
      Finset.Ico (RightLeft hi J B) (Count hi A B) := by
    intro r hr
    obtain ⟨hl,hh⟩ := Finset.mem_Ico.mp hr
    exact Finset.mem_Ico.mpr ⟨by omega,by omega⟩
  unfold RightSum
  calc
    _ ≤ ∑ r∈Finset.Ico (RightLeft q J B) (Count q A B),(hi+1-r*B) := by
      apply Finset.sum_le_sum
      intro r hr
      omega
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by intros;exact Nat.zero_le _)

theorem maximum_sum_bound {A J B lo hi q : ℕ} (hB : 0<B) (hAJ : A≤J)
    (hlo : lo≤q) (hhi : q≤hi) : RightSum q A J B≤maximum_sum A J B lo hi := by
  unfold maximum_sum
  by_cases hj : J≤hi ∧ lo≤Last J B hi
  · rw [if_pos hj]
    exact (rightSum_le_full hB).trans (le_max_right _ _)
  · rw [if_neg hj]
    have heq := rightLeft_eq_of_no_last hB (hlo.trans hhi) hj
    have hlow := rightLeft_mono (J:=J) (B:=B) hlo
    have hhigh := rightLeft_mono (J:=J) (B:=B) hhi
    have heq' : RightLeft q J B=RightLeft hi J B := by omega
    have hh := rightSum_mono (A:=A) hB hhi heq'
    rw [rightSum_eq_closed (q:=hi) hB hAJ] at hh
    exact hh.trans (le_max_left _ _)

theorem actual_Icc_sum_bound {q A J B V lo hi : ℕ} (hB : 0<B) (hAJ : A≤J)
    (hAq : A≤q) (hlo : lo≤q) (hhi : q≤hi) :
    (∑ r∈Finset.Icc (RightLeft q J B) ((q-A)/B),min V (q-r*B+1))≤maximum_sum A J B lo hi := by
  have he : Finset.Icc (RightLeft q J B) ((q-A)/B)=Finset.Ico (RightLeft q J B) (Count q A B) := by
    ext r
    simp only [Finset.mem_Icc,Finset.mem_Ico,Count,if_pos hAq]
    omega
  rw [he]
  apply le_trans _ (maximum_sum_bound hB hAJ hlo hhi)
  unfold RightSum
  apply Finset.sum_le_sum
  intro r hr
  have hh := (lt_count hB).mp (Finset.mem_Ico.mp hr).2
  have hm := min_le_right V (q-r*B+1)
  omega

#print axioms rightSum_eq_closed
#print axioms maximum_sum_bound
#print axioms actual_Icc_sum_bound
end JSP233.WindowSums208
