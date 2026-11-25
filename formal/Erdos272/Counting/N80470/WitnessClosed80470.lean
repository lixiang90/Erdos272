module

public import Erdos272.Geometry.N82427.PhaseClosed82427

@[expose] public section

namespace JSP233.WitnessClosed80470
open LightPhases208 LightClosed208 PhaseClosed82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def CappedSum (q T E B C : ℕ) : ℕ :=
  let L := Count q (T-E) B
  let O := min L (Count q (C-E) B)
  C*O+((L-O)*(q+E)-B*(Tri L-Tri O))

theorem capped_weight_sum_of_le {q T E B C : ℕ} (hB : 0<B) (hEC : E≤C) :
    (∑ r∈Finset.range (Count q (T-E) B), min C (q-r*B+E))=CappedSum q T E B C := by
  let L := Count q (T-E) B
  let O := min L (Count q (C-E) B)
  have hOL : O≤L := min_le_left _ _
  have hfull : ∀ r∈Finset.range O, min C (q-r*B+E)=C := by
    intro r hr
    have hrO : r<O := Finset.mem_range.mp hr
    have hrC : r<Count q (C-E) B := hrO.trans_le (min_le_right _ _)
    have hh := (lt_count hB).mp hrC
    rw [min_eq_left]
    omega
  have htail : ∀ r∈Finset.Ico O L, min C (q-r*B+E)=q+E-r*B := by
    intro r hr
    obtain ⟨hrO,hrL⟩ := Finset.mem_Ico.mp hr
    have hh := (lt_count hB).mp hrL
    have hnot : ¬(C-E+r*B≤q) := by
      intro h
      have hrC := (lt_count hB).mpr h
      have hmin : r<O := lt_min hrL hrC
      omega
    rw [min_eq_right (by omega)]
    omega
  have hbound : ∀ r∈Finset.Ico O L, B*r≤q+E := by
    intro r hr
    have hh := (lt_count hB).mp (Finset.mem_Ico.mp hr).2
    nlinarith
  have hs : (∑ r∈Finset.Ico O L, (q+E-r*B))=
      (L-O)*(q+E)-B*(Tri L-Tri O) := by
    simp_rw [Nat.mul_comm _ B]
    rw [Finset.sum_tsub_distrib _ hbound]
    simp only [Finset.sum_const,Nat.card_Ico,smul_eq_mul]
    rw [←Finset.mul_sum,sum_Ico_id hOL]
  calc
    (∑ r∈Finset.range L, min C (q-r*B+E))=
        (∑ r∈Finset.range O, min C (q-r*B+E))+
          (∑ r∈Finset.Ico O L, min C (q-r*B+E)) :=
      (Finset.sum_range_add_sum_Ico _ hOL).symm
    _=C*O+((L-O)*(q+E)-B*(Tri L-Tri O)) := by
      rw [Finset.sum_congr rfl hfull,Finset.sum_congr rfl htail,hs]
      simp [Nat.mul_comm]
    _=CappedSum q T E B C := rfl

theorem capped_weight_sum {q T E B C : ℕ} (hB : 0<B) :
    (∑ r∈Finset.range (Count q (T-E) B), min C (q-r*B+E))=CappedSum q T E B C := by
  by_cases hEC : E≤C
  · exact capped_weight_sum_of_le hB hEC
  · have hCE : C≤E := by omega
    have hz : C-E=0 := Nat.sub_eq_zero_of_le hCE
    have hc : Count q (T-E) B≤Count q (C-E) B := by
      rw [hz]
      exact count_antitone hB (Nat.zero_le _)
    have hmin : min (Count q (T-E) B) (Count q (C-E) B)=Count q (T-E) B :=
      min_eq_left hc
    have hs : (∑ r∈Finset.range (Count q (T-E) B), min C (q-r*B+E))=
        C*Count q (T-E) B := by
      have heq : ∀ r∈Finset.range (Count q (T-E) B), min C (q-r*B+E)=C := by
        intro r _hr
        exact min_eq_left (by omega)
      rw [Finset.sum_congr rfl heq]
      simp [Nat.mul_comm]
    rw [hs]
    simp only [CappedSum,hmin,Nat.sub_self,Nat.zero_mul,Nat.mul_zero,Nat.add_zero]

def CappedPrice (N d T E B C : ℕ) : ℕ :=
  ∑ i∈LightPhases208.Indices N d (T-E) B, min C ((N-i.2)/d-i.1*B+E)

def CappedClosed (N d T E B C : ℕ) : ℕ :=
  N%d*CappedSum (N/d) T E B C+(d-N%d)*CappedSum (N/d-1) T E B C

-- The phase partition below reuses the established symbolic division identities.
theorem capped_price_phase_sum {N d T E B C : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E < T) :
    CappedPrice N d T E B C =
      ∑ x ∈ Finset.Icc 1 d, CappedSum ((N-x)/d) T E B C := by
  unfold CappedPrice LightPhases208.Indices
  rw [Finset.sum_filter,Finset.product_eq_sprod,Finset.sum_product,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  have hf : (Finset.range (N+1)).filter (fun r => x+(T-E+r*B)*d ≤ N) =
      Finset.range (Count ((N-x)/d) (T-E) B) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range]
    have he := phase_active (N:=N) (x:=x) hd (by omega : 0 < T-E+r*B)
    have hc := lt_count (q:=(N-x)/d) (C:=T-E) (r:=r) hB
    have hb : Count ((N-x)/d) (T-E) B ≤ N+1 :=
      (LightPrice208.count_le_ground (N:=N-x) (d:=d) (A:=T-E) hB).trans (by omega)
    omega
  change (∑ r ∈ Finset.range (N+1),
    if x+(T-E+r*B)*d ≤ N then min C ((N-x)/d-r*B+E) else 0) = _
  rw [←Finset.sum_filter,hf]
  exact capped_weight_sum hB

theorem capped_price_closed {N d T E B C : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E < T) :
    CappedPrice N d T E B C = CappedClosed N d T E B C := by
  rw [capped_price_phase_sum hd hB hET]
  have hm := Nat.mod_lt N hd
  have hf1 : (Finset.Icc 1 d).filter (fun x => x ≤ N%d) = Finset.Icc 1 (N%d) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have hf2 : (Finset.Icc 1 d).filter (fun x => ¬x ≤ N%d) = Finset.Icc (N%d+1) d := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have he : (∑ x ∈ Finset.Icc 1 d, CappedSum ((N-x)/d) T E B C) =
      ∑ x ∈ Finset.Icc 1 d,
        if x ≤ N%d then CappedSum (N/d) T E B C else CappedSum (N/d-1) T E B C := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [phase_div hd hx]
    split_ifs <;> rfl
  rw [he,Finset.sum_ite,hf1,hf2]
  simp only [Finset.sum_const,Nat.card_Icc,smul_eq_mul]
  unfold CappedClosed
  congr 1 <;> congr 1 <;> omega


#print axioms capped_weight_sum_of_le
#print axioms capped_weight_sum
#print axioms capped_price_phase_sum
#print axioms capped_price_closed
end
end JSP233.WitnessClosed80470
