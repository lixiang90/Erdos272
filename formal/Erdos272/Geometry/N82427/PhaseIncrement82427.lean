module

public import Erdos272.Geometry.N82427.PhaseClosed82427

@[expose] public section

namespace JSP233.PhaseIncrement82427
open LightPhases208 PhaseDefs82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem indices_mono {N H d A B : ℕ} (hNH : N ≤ H) :
    Indices N d A B ⊆ Indices H d A B := by
  intro i hi
  obtain ⟨hprod,hactive⟩ := Finset.mem_filter.mp hi
  obtain ⟨hr,hx⟩ := Finset.mem_product.mp hprod
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_product.mpr ⟨?_,hx⟩,by omega⟩
  exact Finset.mem_range.mpr ((Finset.mem_range.mp hr).trans_le (by omega))

theorem cap_mono {N H d E B V : ℕ} (hNH : N ≤ H) (i : ℕ × ℕ) :
    PhaseDefs82427.Cap N d E B V i ≤ PhaseDefs82427.Cap H d E B V i := by
  unfold PhaseDefs82427.Cap
  apply min_le_min_left V
  apply Nat.add_le_add_right
  apply Nat.sub_le_sub_right
  exact Nat.div_le_div_right (Nat.sub_le_sub_right hNH _)

theorem price_mono {N H d T E B V : ℕ} (hNH : N ≤ H) :
    PhaseDefs82427.Price N d T E B V ≤ PhaseDefs82427.Price H d T E B V := by
  unfold PhaseDefs82427.Price
  exact (Finset.sum_le_sum (fun i _ => cap_mono hNH i)).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (indices_mono hNH) (by intros; exact Nat.zero_le _))

theorem price_increment {N d T E B V r : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E ≤ T) (hTV : T ≤ V)
    (hq : T-E+r*B=N/d) :
    PhaseDefs82427.Price N d T E B V+T ≤ PhaseDefs82427.Price (N+1) d T E B V := by
  let i : ℕ × ℕ := (r,N%d+1)
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  have hrB : r ≤ r*B := by nlinarith [show 1 ≤ B by omega]
  have hrN : r < N+2 := by have hh := Nat.div_le_self N d; omega
  have hnew : i ∈ Indices (N+1) d (T-E) B := by
    change (r,N%d+1) ∈ Indices (N+1) d (T-E) B
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr hrN,Finset.mem_Icc.mpr ⟨by omega,by omega⟩⟩,?_⟩
    change N%d+1+(T-E+r*B)*d ≤ N+1
    rw [hq]
    omega
  have hnot : i ∉ Indices N d (T-E) B := by
    intro hi
    have ha := (Finset.mem_filter.mp hi).2
    change N%d+1+(T-E+r*B)*d ≤ N at ha
    rw [hq] at ha
    omega
  have hcap : PhaseDefs82427.Cap (N+1) d E B V i=T := by
    have hs : N+1-(N%d+1)=N/d*d := by omega
    have hdiv : (N/d*d)/d=N/d := Nat.mul_div_cancel _ hd
    change min V ((N+1-(N%d+1))/d-r*B+E)=T
    rw [hs,hdiv]
    have he : N/d-r*B+E=T := by omega
    rw [he,min_eq_right hTV]
  have hsub : insert i (Indices N d (T-E) B) ⊆ Indices (N+1) d (T-E) B := by
    apply Finset.insert_subset_iff.mpr
    exact ⟨hnew,indices_mono (Nat.le_succ N)⟩
  have hpay := Finset.sum_le_sum (s:=Indices N d (T-E) B)
    (fun j _ => cap_mono (d:=d) (E:=E) (B:=B) (V:=V) (Nat.le_succ N) j)
  simp only [Nat.succ_eq_add_one] at hpay
  have hmore := Finset.sum_le_sum_of_subset_of_nonneg
    (f:=fun j => PhaseDefs82427.Cap (N+1) d E B V j) hsub (by intros; exact Nat.zero_le _)
  rw [Finset.sum_insert hnot,hcap] at hmore
  unfold PhaseDefs82427.Price at *
  omega

#print axioms indices_mono
#print axioms cap_mono
#print axioms price_mono
#print axioms price_increment
end
end JSP233.PhaseIncrement82427
