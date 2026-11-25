module

public import Erdos272.Geometry.N82427.PhaseDefs82427
public import Erdos272.Arithmetic.LightClosed208
public import Erdos272.Arithmetic.LightPrice208

@[expose] public section

namespace JSP233.PhaseClosed82427
open LightPhases208 LightClosed208 PhaseDefs82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Closed (N d T E B V : ℕ) : ℕ :=
  N%d*WeightSum (N/d) T E B V+(d-N%d)*WeightSum (N/d-1) T E B V

theorem phase_div {N d x : ℕ} (hd : 0 < d) (hx : x ∈ Finset.Icc 1 d) :
    (N-x)/d = if x ≤ N%d then N/d else N/d-1 := by
  obtain ⟨hx1,hxd⟩ := Finset.mem_Icc.mp hx
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  split_ifs with hxr
  · have hxN : x ≤ N := by omega
    have hsub : N-x+x=N := Nat.sub_add_cancel hxN
    apply Nat.div_eq_of_lt_le <;> nlinarith
  · by_cases hq : N/d=0
    · have hn : N=N%d := by simpa only [hq,zero_mul,zero_add] using hdecomp
      simp only [hq,Nat.zero_sub]
      rw [Nat.sub_eq_zero_of_le (by omega : N ≤ x),Nat.zero_div]
    · have hqpos : 1 ≤ N/d := Nat.one_le_iff_ne_zero.mpr hq
      have hq1 : N/d-1+1=N/d := Nat.sub_add_cancel hqpos
      have hmul : (N/d-1)*d+d=N/d*d := by
        calc
          _ = (N/d-1+1)*d := by ring
          _ = _ := by rw [hq1]
      have hprod : d ≤ N/d*d := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right d hqpos
      have hdN : d ≤ N := hprod.trans (Nat.div_mul_le_self N d)
      have hxN : x ≤ N := hxd.trans hdN
      have hsub : N-x+x=N := Nat.sub_add_cancel hxN
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [hq1]
        omega

theorem phase_active {N d x k : ℕ} (hd : 0 < d) (hk : 0 < k) :
    x+k*d ≤ N ↔ k ≤ (N-x)/d := by
  constructor
  · intro h
    apply (Nat.le_div_iff_mul_le hd).mpr
    omega
  · intro h
    have hb := (Nat.le_div_iff_mul_le hd).mp h
    have hk1 : 1 ≤ k := by omega
    have hpos : 0 < N-x := by nlinarith
    omega

theorem price_phase_sum {N d T E B V : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E < T) (hTV : T ≤ V) :
    PhaseDefs82427.Price N d T E B V =
      ∑ x ∈ Finset.Icc 1 d, WeightSum ((N-x)/d) T E B V := by
  unfold PhaseDefs82427.Price LightPhases208.Indices
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
    if x+(T-E+r*B)*d ≤ N then min V ((N-x)/d-r*B+E) else 0) = _
  rw [←Finset.sum_filter,hf]
  exact weight_sum hB hET.le hTV

theorem price_closed {N d T E B V : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E < T) (hTV : T ≤ V) :
    PhaseDefs82427.Price N d T E B V = Closed N d T E B V := by
  rw [price_phase_sum hd hB hET hTV]
  have hm := Nat.mod_lt N hd
  have hf1 : (Finset.Icc 1 d).filter (fun x => x ≤ N%d) = Finset.Icc 1 (N%d) := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have hf2 : (Finset.Icc 1 d).filter (fun x => ¬x ≤ N%d) = Finset.Icc (N%d+1) d := by
    ext x
    simp only [Finset.mem_filter,Finset.mem_Icc]
    omega
  have he : (∑ x ∈ Finset.Icc 1 d, WeightSum ((N-x)/d) T E B V) =
      ∑ x ∈ Finset.Icc 1 d,
        if x ≤ N%d then WeightSum (N/d) T E B V else WeightSum (N/d-1) T E B V := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [phase_div hd hx]
    split_ifs <;> rfl
  rw [he,Finset.sum_ite,hf1,hf2]
  simp only [Finset.sum_const,Nat.card_Icc,smul_eq_mul]
  unfold Closed
  congr 1 <;> congr 1 <;> omega

#print axioms phase_div
#print axioms phase_active
#print axioms price_phase_sum
#print axioms price_closed
end
end JSP233.PhaseClosed82427
