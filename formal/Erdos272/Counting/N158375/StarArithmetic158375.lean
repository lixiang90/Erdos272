module

public import Erdos272.Core.N200000.CoreUnionSource200000

@[expose] public section

namespace JSP233.StarArithmetic158375
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem choose_succ_two (n : ℕ) : (n+1).choose 2 = n.choose 2+n := by
  have h₁ := APInterval208.choose_two_twice n
  have h₂ := APInterval208.choose_two_twice (n+1)
  nlinarith only [h₁, h₂]

theorem divided_choose_step (n k : ℕ) (hk : 0 < k) :
    ((n+1)/k).choose 2 ≤ (n/k).choose 2+n := by
  have h₁ : n/k ≤ (n+1)/k := Nat.div_le_div_right (by omega)
  have h₂ : (n+1)/k ≤ n/k+1 := by
    apply (Nat.div_le_iff_le_mul hk).mpr
    have hm := Nat.mod_lt n hk
    have he := Nat.mod_add_div n k
    have hb : n+1 ≤ (n/k+1)*k := by nlinarith only [hm, he]
    omega
  have h₃ : n/k ≤ n := Nat.div_le_self _ _
  by_cases he : (n+1)/k = n/k
  · rw [he]; omega
  · have he' : (n+1)/k = n/k+1 := by omega
    rw [he', choose_succ_two]
    omega

theorem divided_choose_contract {b c k : ℕ} (hk : 0 < k) (hbc : b ≤ c) :
    c.choose 2 + (b/k).choose 2 ≥ b.choose 2+(c/k).choose 2 := by
  induction c, hbc using Nat.le_induction with
  | base => omega
  | succ c hbc ih =>
      have hs := divided_choose_step c k hk
      rw [choose_succ_two]
      omega

theorem half_loss (b q : ℕ) (hq : 0 < q) :
    ((b+2*q-1)/(2*q)).choose 2 ≤ (b/q).choose 2 := by
  by_cases hz : b/q = 0
  · have hb : b < q := (Nat.div_eq_zero_iff.mp hz).resolve_left (by omega)
    have hc : (b+2*q-1)/(2*q) ≤ 1 := by
      apply (Nat.div_le_iff_le_mul (by omega : 0 < 2*q)).mpr
      omega
    have hzero : ((b+2*q-1)/(2*q)).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [hzero]
  · have hbd := Nat.mod_lt b hq
    have he := Nat.mod_add_div b q
    have hc : (b+2*q-1)/(2*q) ≤ b/q := by
      apply (Nat.div_le_iff_le_mul (by omega : 0 < 2*q)).mpr
      have hu : 0 < b/q := Nat.pos_of_ne_zero hz
      have hm : q ≤ q*(b/q) := Nat.le_mul_of_pos_right q hu
      have hb : b ≤ (b/q)*(2*q) := by nlinarith only [hbd, he, hm]
      omega
    exact Nat.choose_le_choose 2 hc

#print axioms choose_succ_two
#print axioms divided_choose_step
#print axioms divided_choose_contract
#print axioms half_loss
end JSP233.StarArithmetic158375
