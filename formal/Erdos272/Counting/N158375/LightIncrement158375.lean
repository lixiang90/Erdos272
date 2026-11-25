module

public import Erdos272.Resources.ActualCleanupEval208

@[expose] public section

namespace JSP233.LightIncrement158375
open LightPhases208 LightPrice208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def PhaseCost (N d T E B V r : ℕ) : ℕ :=
  min d (N-(T-E+r*B)*d)*min V (N/d-r*B+E)

theorem phase_mono {N H d T E B V r : ℕ} (hNH : N ≤ H) :
    PhaseCost N d T E B V r ≤ PhaseCost H d T E B V r := by
  apply Nat.mul_le_mul
  · exact min_le_min_left d (Nat.sub_le_sub_right hNH _)
  · exact min_le_min_left V (Nat.add_le_add_right
      (Nat.sub_le_sub_right (Nat.div_le_div_right (c := d) hNH) _) E)

theorem phase_increment {N d T E B V r : ℕ}
    (hd : 0 < d) (hET : E ≤ T) (hTV : T ≤ V)
    (hq : T-E+r*B=N/d) :
    PhaseCost N d T E B V r+T ≤ PhaseCost (N+1) d T E B V r := by
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  have hfirst : N-(T-E+r*B)*d=N%d := by rw [hq]; omega
  have hnext : N+1-(T-E+r*B)*d=N%d+1 := by rw [hq]; omega
  have hcap := partial_cap hET hTV hq
  have hdiv := Nat.div_le_div_right (c := d) (Nat.le_succ N)
  have hcapnext : T ≤ min V ((N+1)/d-r*B+E) := by
    rw [←hcap]
    exact min_le_min_left V (Nat.add_le_add_right (Nat.sub_le_sub_right hdiv _) E)
  have hmul := Nat.mul_le_mul_left (N%d+1) hcapnext
  dsimp only [PhaseCost]
  rw [hfirst, hnext, hcap, min_eq_right (by omega : N%d ≤ d),
    min_eq_right (by omega : N%d+1 ≤ d)]
  nlinarith only [hmul]

theorem price_increment {N d T E B V r : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E ≤ T) (hTV : T ≤ V)
    (hq : T-E+r*B=N/d) :
    Price N d T E B V+T ≤ Price (N+1) d T E B V := by
  have hrB : r ≤ r*B := by nlinarith [show 1 ≤ B by omega]
  have hdiv := Nat.div_le_self N d
  have hr : r ∈ Finset.range (N+1) := Finset.mem_range.mpr (by omega)
  have hrest := Finset.sum_le_sum (s := (Finset.range (N+1)).erase r)
    (fun j _ => phase_mono (T := T) (E := E) (B := B) (V := V) (r := j) (d := d) (Nat.le_succ N))
  have hbefore := Finset.sum_erase_add (Finset.range (N+1)) (fun j => PhaseCost N d T E B V j) hr
  have hafter := Finset.sum_erase_add (Finset.range (N+1)) (fun j => PhaseCost (N+1) d T E B V j) hr
  have hterm := phase_increment hd hET hTV hq
  have hsum : (∑ j ∈ Finset.range (N+1), PhaseCost N d T E B V j)+T ≤
      ∑ j ∈ Finset.range (N+1), PhaseCost (N+1) d T E B V j := by
    calc
      _ = ((∑ j ∈ (Finset.range (N+1)).erase r, PhaseCost N d T E B V j)+
          PhaseCost N d T E B V r)+T := by rw [hbefore]
      _ ≤ (∑ j ∈ (Finset.range (N+1)).erase r, PhaseCost (N+1) d T E B V j)+
          PhaseCost (N+1) d T E B V r := by
        simpa only [Nat.add_assoc] using Nat.add_le_add hrest hterm
      _ = _ := hafter
  have hmore : (∑ j ∈ Finset.range (N+1), PhaseCost (N+1) d T E B V j) ≤
      ∑ j ∈ Finset.range (N+1+1), PhaseCost (N+1) d T E B V j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
      (by intros; exact Nat.zero_le _)
  exact hsum.trans hmore

theorem closed_increment {N d T E B V r : ℕ}
    (hd : 0 < d) (hB : 0 < B) (hET : E ≤ T) (hTV : T ≤ V)
    (hq : T-E+r*B=N/d) :
    Closed N d T E B V+T ≤ Closed (N+1) d T E B V := by
  rw [←price_closed hd hB hET hTV, ←price_closed hd hB hET hTV]
  exact price_increment hd hB hET hTV hq

#print axioms phase_mono
#print axioms phase_increment
#print axioms price_increment
#print axioms closed_increment
end
end JSP233.LightIncrement158375
