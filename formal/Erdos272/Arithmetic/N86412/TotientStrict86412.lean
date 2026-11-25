module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Algebra.BigOperators.Intervals
public import Erdos272.Foundation.ProofTactics

@[expose] public section

namespace JSP233.TotientStrict86412
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def U (s : ℕ) : ℕ :=
  ∑ q ∈ Finset.Ico 3 s, if ¬q ∣ s then Nat.totient q else 0

def PhiInclusive (s : ℕ) : ℕ := ∑ q ∈ Finset.range (s+1), Nat.totient q

def EvenBonus (s : ℕ) : ℕ := if 2 ∣ s then 1 else 0

theorem nondivisor_sum {s : ℕ} (hs : 3 ≤ s) :
    (∑ q ∈ Finset.range (s+1), if ¬q ∣ s then Nat.totient q else 0) =
      (if 2 ∣ s then 0 else 1)+U s := by
  let J := insert 2 (Finset.Ico 3 s)
  have hsub : J ⊆ Finset.range (s+1) := by
    intro q hq
    simp only [J, Finset.mem_insert, Finset.mem_Ico] at hq
    apply Finset.mem_range.mpr
    omega
  have hzero : ∀ q ∈ Finset.range (s+1), q ∉ J →
      (if ¬q ∣ s then Nat.totient q else 0) = 0 := by
    intro q hq hnot
    have hq' := Finset.mem_range.mp hq
    simp only [J, Finset.mem_insert, Finset.mem_Ico] at hnot
    have hc : q = 0 ∨ q = 1 ∨ q = s := by omega
    rcases hc with rfl | rfl | rfl <;> simp
  have he := Finset.sum_subset hsub hzero
  have hnot : 2 ∉ Finset.Ico 3 s := by simp
  rw [← he]
  dsimp only [J]
  rw [Finset.sum_insert hnot]
  change (if ¬2 ∣ s then Nat.totient 2 else 0)+U s = _
  by_cases hd : 2 ∣ s <;> simp [hd]

theorem u_add_identity {s : ℕ} (hs : 3 ≤ s) :
    U s+s+1 = PhiInclusive s+EvenBonus s := by
  have hd : (∑ q ∈ Finset.range (s+1), if q ∣ s then Nat.totient q else 0) = s := by
    simpa only [Finset.sum_filter, Nat.succ_eq_add_one] using Nat.sum_totient' s
  have hp : PhiInclusive s = s+(if 2 ∣ s then 0 else 1)+U s := by
    unfold PhiInclusive
    calc
      _ = (∑ q ∈ Finset.range (s+1), if q ∣ s then Nat.totient q else 0)+
          (∑ q ∈ Finset.range (s+1), if ¬q ∣ s then Nat.totient q else 0) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro q hq
        by_cases h : q ∣ s <;> simp [h]
      _ = _ := by rw [hd, nondivisor_sum hs]; omega
  by_cases h : 2 ∣ s
  · rw [if_pos h] at hp
    rw [EvenBonus, if_pos h]
    omega
  · rw [if_neg h] at hp
    rw [EvenBonus, if_neg h]
    omega

theorem even_bonus_le_one (s : ℕ) : EvenBonus s ≤ 1 := by
  unfold EvenBonus
  split_ifs <;> omega

theorem u_succ_mono {s : ℕ} (hs : 3 ≤ s) : U s ≤ U (s+1) := by
  have h₀ := u_add_identity hs
  have h₁ := u_add_identity (by omega : 3 ≤ s+1)
  have hphi : PhiInclusive (s+1) = PhiInclusive s+Nat.totient (s+1) := by
    exact Finset.sum_range_succ _ _
  have hpos : 0 < Nat.totient (s+1) := Nat.totient_pos.mpr (by omega)
  have hne : Nat.totient (s+1) ≠ 1 := by
    intro h
    have hh := Nat.totient_eq_one_iff.mp h
    omega
  have hb := even_bonus_le_one s
  omega

theorem u_mono {s t : ℕ} (hs : 3 ≤ s) (hst : s ≤ t) : U s ≤ U t := by
  induction t, hst using Nat.le_induction with
  | base => exact le_rfl
  | succ t hst ih => exact ih.trans (u_succ_mono (by omega))

#print axioms nondivisor_sum
#print axioms u_add_identity
#print axioms even_bonus_le_one
#print axioms u_succ_mono
#print axioms u_mono
end
end JSP233.TotientStrict86412
