module

public import Erdos272.Resources.N118533.DensePool118533
public import Erdos272.Resources.APResidual208

@[expose] public section

namespace JSP233.QuarterCount109474
open StarCompletion APGeometry IntrinsicTriples208 DensePool118533
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem count_gate {n : ℝ} (hn : 34040 ≤ n) :
    n^3/6 < (19/2 : ℝ)*n*Price (n/4) := by
  have hp : 0 < (125143/84270000 : ℝ)*n-(741/53 : ℝ) := by
    linarith only [hn]
  have hn0 : 0 < n := by linarith only [hn]
  have hmul := mul_pos (sq_pos_of_pos hn0) hp
  unfold Price
  nlinarith only [hmul]

theorem actual_member_price {N : ℕ} {E : Finset (Finset ℤ)}
    (hN : 34040 ≤ N) (hcap : N ≤ 2^18) (hE : Legal (Ground N) E)
    (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, (N : ℝ)/4 < S.card)
    {S : Finset ℤ} (hS : S ∈ E) :
    Price ((N : ℝ)/4) ≤ ((Pool S).card : ℝ) := by
  have hn : (34040 : ℝ) ≤ N := by exact_mod_cast hN
  have hd := hdense S hS
  have hsR : (8510 : ℝ) < S.card := by linarith only [hn, hd]
  have hsNat : 8510 < S.card := by exact_mod_cast hsR
  have hs : 8511 ≤ S.card := by omega
  have hp := actual_pool_price hs hcap (hE.1 S hS) (hbad S hS)
  exact (price_mono (by linarith only [hn] : (8000 : ℝ) ≤ (N : ℝ)/4) hd.le).trans hp

theorem actual_count {N : ℕ} {E : Finset (Finset ℤ)}
    (hN : 34040 ≤ N) (hcap : N ≤ 2^18) (hE : Legal (Ground N) E)
    (hbad : ∀ S ∈ E, ¬IsAP S)
    (hdense : ∀ S ∈ E, (N : ℝ)/4 < S.card) :
    (E.card : ℝ) ≤ (19/2 : ℝ)*N := by
  have hn : (34040 : ℝ) ≤ N := by exact_mod_cast hN
  have htheta : 0 < Price ((N : ℝ)/4) := price_pos (by linarith only [hn])
  have hmass : Price ((N : ℝ)/4)*(E.card : ℝ) ≤
      ∑ S ∈ E, ((Pool S).card : ℝ) := by
    calc
      _ = ∑ _S ∈ E, Price ((N : ℝ)/4) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun S hS => actual_member_price hN hcap hE hbad hdense hS)
  have hcNat := actual_capacity hE
  rw [ground_card] at hcNat
  have hc : (∑ S ∈ E, ((Pool S).card : ℝ)) ≤ (N.choose 3 : ℝ) := by
    exact_mod_cast hcNat
  rw [APResidual208.cast_choose_three] at hc
  have hfactor : 0 ≤ (N : ℝ)*(3*(N : ℝ)-2) :=
    mul_nonneg (Nat.cast_nonneg N) (by linarith only [hn])
  have hpool : (∑ S ∈ E, ((Pool S).card : ℝ)) ≤ (N : ℝ)^3/6 := by
    nlinarith only [hc, hfactor]
  have hg := count_gate hn
  by_contra hnot
  have hlt : (19/2 : ℝ)*N < (E.card : ℝ) := lt_of_not_ge hnot
  have hmul := mul_lt_mul_of_pos_left hlt htheta
  nlinarith only [hmul, hmass, hpool, hg]

#print axioms count_gate
#print axioms actual_member_price
#print axioms actual_count
end
end JSP233.QuarterCount109474
