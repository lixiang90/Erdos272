import Erdos272.Counting.LightPhases208

namespace JSP233.LightClosed208
open LightPhases208
open scoped BigOperators
set_option maxHeartbeats 0

def Count (q C B : ℕ) : ℕ := if C≤q then (q-C)/B+1 else 0
def Tri (n : ℕ) : ℕ := n*(n-1)/2
def WeightSum (q T E B V : ℕ) : ℕ :=
  let L:=Count q (T-E) B
  let O:=Count q (V-E) B
  V*O+((L-O)*(q+E)-B*(Tri L-Tri O))

theorem lt_count {q C B r : ℕ} (hB : 0<B) : r<Count q C B ↔ C+r*B≤q := by
  unfold Count
  by_cases hC : C≤q
  · rw [if_pos hC]
    have hh : r≤(q-C)/B ↔ r*B≤q-C := Nat.le_div_iff_mul_le hB
    omega
  · rw [if_neg hC]
    omega

theorem count_antitone {q C D B : ℕ} (hB : 0<B) (hCD : C≤D) : Count q D B≤Count q C B := by
  by_contra! h
  have hh := (lt_count hB).mp h
  have hbad : Count q C B<Count q C B := (lt_count hB).mpr (by omega)
  exact Nat.lt_irrefl _ hbad

theorem sum_Ico_id {O L : ℕ} (hOL : O≤L) : (∑ r∈Finset.Ico O L,r)=Tri L-Tri O := by
  have hh := Finset.sum_range_add_sum_Ico (fun r : ℕ=>r) hOL
  rw [Finset.sum_range_id,Finset.sum_range_id] at hh
  unfold Tri
  omega

theorem weight_sum {q T E B V : ℕ} (hB : 0<B) (hET : E≤T) (hTV : T≤V) :
    (∑ r∈Finset.range (Count q (T-E) B),min V (q-r*B+E))=WeightSum q T E B V := by
  let L:=Count q (T-E) B
  let O:=Count q (V-E) B
  have hOL : O≤L := count_antitone hB (Nat.sub_le_sub_right hTV E)
  have hfull : ∀ r∈Finset.range O,min V (q-r*B+E)=V := by
    intro r hr
    have hh := (lt_count hB).mp (Finset.mem_range.mp hr)
    have hEV : E≤V := hET.trans hTV
    rw [min_eq_left]
    omega
  have htail : ∀ r∈Finset.Ico O L,min V (q-r*B+E)=q+E-r*B := by
    intro r hr
    obtain ⟨hrO,hrL⟩ := Finset.mem_Ico.mp hr
    have hh := (lt_count hB).mp hrL
    have hnot : ¬(V-E+r*B≤q) := by
      intro hh
      have hx := (lt_count hB).mpr hh
      omega
    have hEV : E≤V := hET.trans hTV
    rw [min_eq_right (by omega)]
    omega
  have hbound : ∀ r∈Finset.Ico O L,B*r≤q+E := by
    intro r hr
    have hh := (lt_count hB).mp (Finset.mem_Ico.mp hr).2
    nlinarith
  have hs : (∑ r∈Finset.Ico O L,(q+E-r*B))=(L-O)*(q+E)-B*(Tri L-Tri O) := by
    simp_rw [Nat.mul_comm _ B]
    rw [Finset.sum_tsub_distrib _ hbound]
    simp only [Finset.sum_const,Nat.card_Ico,smul_eq_mul]
    rw [←Finset.mul_sum,sum_Ico_id hOL]
  calc
    (∑ r∈Finset.range L,min V (q-r*B+E))=
        (∑ r∈Finset.range O,min V (q-r*B+E))+(∑ r∈Finset.Ico O L,min V (q-r*B+E)) :=
      (Finset.sum_range_add_sum_Ico _ hOL).symm
    _ = V*O+((L-O)*(q+E)-B*(Tri L-Tri O)) := by
      rw [Finset.sum_congr rfl hfull,Finset.sum_congr rfl htail,hs]
      simp [Nat.mul_comm]
    _ = WeightSum q T E B V := rfl

#print axioms lt_count
#print axioms weight_sum
end JSP233.LightClosed208
