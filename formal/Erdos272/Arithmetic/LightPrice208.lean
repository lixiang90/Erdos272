module

public import Erdos272.Arithmetic.LightClosed208

@[expose] public section

namespace JSP233.LightPrice208
open LightPhases208 LightClosed208
open scoped BigOperators
set_option maxHeartbeats 0

def Correction (N d T E B : ℕ) : ℕ :=
  if T-E≤N/d ∧ (N/d-(T-E))%B=0 then (d-N%d)*T else 0

def Closed (N d T E B V : ℕ) : ℕ :=
  d*WeightSum (N/d) T E B V-Correction N d T E B

theorem phase_formula {N d k : ℕ} (hd : 0<d) :
    min d (N-k*d)=if k<N/d then d else if k=N/d then N%d else 0 := by
  have hm := Nat.mod_lt N hd
  have hdecomp : N=N/d*d+N%d := by nlinarith [Nat.mod_add_div N d]
  split_ifs with hlt heq
  · have hmul := Nat.mul_le_mul_right d (by omega : k+1≤N/d)
    have hh : k*d+d≤N := by
      simpa only [Nat.add_mul,Nat.one_mul] using hmul.trans (Nat.div_mul_le_self N d)
    omega
  · subst k
    omega
  · have hmul := Nat.mul_le_mul_right d (by omega : N/d+1≤k)
    have hmul' : N/d*d+d≤k*d := by simpa only [Nat.add_mul,Nat.one_mul] using hmul
    have hh : N<k*d := by omega
    omega

theorem count_le_ground {N d A B : ℕ} (hB : 0<B) : Count (N/d) A B≤N+1 := by
  by_contra! h
  have hh := (lt_count hB).mp h
  have hprod := Nat.mul_le_mul_left (N+1) (by omega : 1≤B)
  have hdiv := Nat.div_le_self N d
  nlinarith

theorem partial_cap {q T E B V r : ℕ} (hET : E≤T) (hTV : T≤V)
    (heq : T-E+r*B=q) : min V (q-r*B+E)=T := by
  have hh : q-r*B+E=T := by omega
  rw [hh,min_eq_right hTV]

theorem correction_sum {N d T E B : ℕ} (hB : 0<B) :
    (∑ r∈Finset.range (N+1),if T-E+r*B=N/d then (d-N%d)*T else 0)=Correction N d T E B := by
  let A:=T-E
  let q:=N/d
  by_cases hg : A≤q ∧ (q-A)%B=0
  · let r:=(q-A)/B
    have hdiv : r*B=q-A := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hg.2)
    have heq : A+r*B=q := by omega
    have hrL : r<Count q A B := (lt_count hB).mpr heq.le
    have hr : r∈Finset.range (N+1) := Finset.mem_range.mpr (hrL.trans_le (count_le_ground hB))
    rw [Finset.sum_eq_single r]
    · change (if A+r*B=q then (d-N%d)*T else 0)=Correction N d T E B
      rw [if_pos heq]
      change (d-N%d)*T=(if A≤q ∧ (q-A)%B=0 then (d-N%d)*T else 0)
      rw [if_pos hg]
    · intro x hx hne
      have hneq : ¬(A+x*B=q) := by
        intro hxq
        have hxr : x=r := by nlinarith
        exact hne hxr
      exact if_neg hneq
    · intro hn
      exact False.elim (hn hr)
  · have hz : (∑ r∈Finset.range (N+1),if A+r*B=q then (d-N%d)*T else 0)=0 := by
      apply Finset.sum_eq_zero
      intro r hr
      apply if_neg
      intro heq
      have hA : A≤q := by omega
      have hrem : (q-A)%B=0 := by
        have hh : q-A=r*B := by omega
        rw [hh]
        simp
      exact hg ⟨hA,hrem⟩
    exact hz.trans (if_neg hg).symm

theorem phase_balance {N d T E B V : ℕ} (hd : 0<d) (hB : 0<B) (hET : E≤T) (hTV : T≤V) (r : ℕ) :
    min d (N-(T-E+r*B)*d)*min V (N/d-r*B+E)+
      (if T-E+r*B=N/d then (d-N%d)*T else 0)=
      if r<Count (N/d) (T-E) B then d*min V (N/d-r*B+E) else 0 := by
  rw [phase_formula hd]
  by_cases hlt : T-E+r*B<N/d
  · have hr : r<Count (N/d) (T-E) B := (lt_count hB).mpr hlt.le
    simp only [if_pos hlt,if_neg (Nat.ne_of_lt hlt),if_pos hr,add_zero]
  · by_cases heq : T-E+r*B=N/d
    · have hr : r<Count (N/d) (T-E) B := (lt_count hB).mpr heq.le
      simp only [if_neg hlt,if_pos heq,if_pos hr,partial_cap hET hTV heq]
      have hm := Nat.mod_lt N hd
      have hh : N%d+(d-N%d)=d := by omega
      rw [←Nat.add_mul,hh]
    · have hr : ¬r<Count (N/d) (T-E) B := by
        intro hh
        have hh' := (lt_count hB).mp hh
        omega
      simp only [if_neg hlt,if_neg heq,if_neg hr,zero_mul,zero_add]

theorem price_closed {N d T E B V : ℕ} (hd : 0<d) (hB : 0<B) (hET : E≤T) (hTV : T≤V) :
    Price N d T E B V=Closed N d T E B V := by
  have hL : Count (N/d) (T-E) B≤N+1 := count_le_ground hB
  have hf : (Finset.range (N+1)).filter (fun r=>r<Count (N/d) (T-E) B)=
      Finset.range (Count (N/d) (T-E) B) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have hs := Finset.sum_congr (s₁:=Finset.range (N+1)) (s₂:=Finset.range (N+1)) rfl
    (fun r hr=>phase_balance (N:=N) (d:=d) (T:=T) (E:=E) (B:=B) (V:=V) hd hB hET hTV r)
  rw [Finset.sum_add_distrib,correction_sum hB,←Finset.sum_filter,hf,←Finset.mul_sum,weight_sum hB hET hTV] at hs
  change Price N d T E B V+Correction N d T E B=d*WeightSum (N/d) T E B V at hs
  unfold Closed
  omega

#print axioms phase_formula
#print axioms correction_sum
#print axioms price_closed
end JSP233.LightPrice208
