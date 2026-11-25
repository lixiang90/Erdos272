module

public import Erdos272.Counting.N80470.WitnessClosed80470

@[expose] public section

namespace JSP233.WitnessLegacy80470
open LightPhases208 LightClosed208 LightPrice208 WitnessClosed80470
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def CappedCorrection (N d T E B C : ℕ) : ℕ :=
  if T-E≤N/d ∧ (N/d-(T-E))%B=0 then (d-N%d)*min C T else 0

def LegacyClosed (N d T E B C : ℕ) : ℕ :=
  d*CappedSum (N/d) T E B C-CappedCorrection N d T E B C

theorem partial_cap {q T E B C r : ℕ} (hET : E≤T)
    (heq : T-E+r*B=q) : min C (q-r*B+E)=min C T := by
  have hh : q-r*B+E=T := by omega
  rw [hh]

theorem correction_sum {N d T E B C : ℕ} (hB : 0<B) :
    (∑ r∈Finset.range (N+1),if T-E+r*B=N/d then (d-N%d)*min C T else 0)=CappedCorrection N d T E B C := by
  let A:=T-E
  let q:=N/d
  by_cases hg : A≤q ∧ (q-A)%B=0
  · let r:=(q-A)/B
    have hdiv : r*B=q-A := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hg.2)
    have heq : A+r*B=q := by omega
    have hrL : r<Count q A B := (lt_count hB).mpr heq.le
    have hr : r∈Finset.range (N+1) := Finset.mem_range.mpr (hrL.trans_le (count_le_ground hB))
    rw [Finset.sum_eq_single r]
    · change (if A+r*B=q then (d-N%d)*min C T else 0)=CappedCorrection N d T E B C
      rw [if_pos heq]
      change (d-N%d)*min C T=(if A≤q ∧ (q-A)%B=0 then (d-N%d)*min C T else 0)
      rw [if_pos hg]
    · intro x hx hne
      have hneq : ¬(A+x*B=q) := by
        intro hxq
        have hxr : x=r := by nlinarith
        exact hne hxr
      exact if_neg hneq
    · intro hn
      exact False.elim (hn hr)
  · have hz : (∑ r∈Finset.range (N+1),if A+r*B=q then (d-N%d)*min C T else 0)=0 := by
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

theorem phase_balance {N d T E B C : ℕ} (hd : 0<d) (hB : 0<B) (hET : E≤T)  (r : ℕ) :
    min d (N-(T-E+r*B)*d)*min C (N/d-r*B+E)+
      (if T-E+r*B=N/d then (d-N%d)*min C T else 0)=
      if r<Count (N/d) (T-E) B then d*min C (N/d-r*B+E) else 0 := by
  rw [phase_formula hd]
  by_cases hlt : T-E+r*B<N/d
  · have hr : r<Count (N/d) (T-E) B := (lt_count hB).mpr hlt.le
    simp only [if_pos hlt,if_neg (Nat.ne_of_lt hlt),if_pos hr,add_zero]
  · by_cases heq : T-E+r*B=N/d
    · have hr : r<Count (N/d) (T-E) B := (lt_count hB).mpr heq.le
      simp only [if_neg hlt,if_pos heq,if_pos hr,partial_cap hET heq]
      have hm := Nat.mod_lt N hd
      have hh : N%d+(d-N%d)=d := by omega
      rw [←Nat.add_mul,hh]
    · have hr : ¬r<Count (N/d) (T-E) B := by
        intro hh
        have hh' := (lt_count hB).mp hh
        omega
      simp only [if_neg hlt,if_neg heq,if_neg hr,zero_mul,zero_add]

theorem legacy_price_closed {N d T E B C : ℕ} (hd : 0<d) (hB : 0<B) (hET : E≤T)  :
    Price N d T E B C=LegacyClosed N d T E B C := by
  have hL : Count (N/d) (T-E) B≤N+1 := count_le_ground hB
  have hf : (Finset.range (N+1)).filter (fun r=>r<Count (N/d) (T-E) B)=
      Finset.range (Count (N/d) (T-E) B) := by
    ext r
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have hs := Finset.sum_congr (s₁:=Finset.range (N+1)) (s₂:=Finset.range (N+1)) rfl
    (fun r hr=>phase_balance (N:=N) (d:=d) (T:=T) (E:=E) (B:=B) (C:=C) hd hB hET r)
  rw [Finset.sum_add_distrib,correction_sum hB,←Finset.sum_filter,hf,←Finset.mul_sum,capped_weight_sum hB] at hs
  change Price N d T E B C+CappedCorrection N d T E B C=d*CappedSum (N/d) T E B C at hs
  unfold LegacyClosed
  omega

#print axioms partial_cap
#print axioms correction_sum
#print axioms phase_balance
#print axioms legacy_price_closed
end
end JSP233.WitnessLegacy80470
