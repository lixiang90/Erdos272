module

public import Erdos272.Resources.N150465.DensePool150465
public import Erdos272.Resources.APResidual208
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.DenseCount150465
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 DensePool150465
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem count_gate {n : ℝ} (hn : 115000 ≤ n) : n^3/6 < 103*n*Price (n/12) := by
  have hp : 0 < (52869/144000000 : ℝ)*n-(201159/4800 : ℝ) := by
    linarith only [hn]
  have hn0 : 0 < n := by linarith only [hn]
  have hmul := mul_pos (sq_pos_of_pos hn0) hp
  unfold Price
  nlinarith only [hmul]

theorem actual_deleted_member_price {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 115000 ≤ N) (hhi : N ≤ 2^18) (hF : Legal (Ground N) F)
    {S : Finset ℤ} (hS : S ∈ Deleted N 12 F) :
    Price ((N : ℝ)/12) ≤ ((Pool S).card : ℝ) := by
  obtain ⟨hSF, hbad, hdense⟩ := Finset.mem_filter.mp hS
  have hs : 1000 ≤ S.card := by omega
  have hcard : S.card ≤ N := by
    simpa only [ground_card] using Finset.card_le_card (hF.1 S hSF)
  have hp := actual_pool_price hs (hcard.trans hhi) hbad
  have hnR : (115000 : ℝ) ≤ N := by exact_mod_cast hN
  have hdR : (N : ℝ) < 12*(S.card : ℝ) := by exact_mod_cast hdense
  have hm := price_mono (by linarith only [hnR] : (1000 : ℝ) ≤ (N : ℝ)/12)
    (by linarith only [hdR] : (N : ℝ)/12 ≤ (S.card : ℝ))
  exact hm.trans hp

theorem actual_deleted_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 115000 ≤ N) (hhi : N ≤ 2^18) (hF : Legal (Ground N) F) :
    (Deleted N 12 F).card ≤ 103*N := by
  have hnR : (115000 : ℝ) ≤ N := by exact_mod_cast hN
  have htheta : 0 < Price ((N : ℝ)/12) := price_pos (by linarith only [hnR])
  have hmass : Price ((N : ℝ)/12)*((Deleted N 12 F).card : ℝ) ≤
      ∑ S ∈ Deleted N 12 F, ((Pool S).card : ℝ) := by
    calc
      _ = ∑ _S ∈ Deleted N 12 F, Price ((N : ℝ)/12) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun S hS => actual_deleted_member_price hN hhi hF hS)
  have hcNat := actual_capacity (actual_deleted_legal (r := 12) hF)
  rw [ground_card] at hcNat
  have hc : (∑ S ∈ Deleted N 12 F, ((Pool S).card : ℝ)) ≤ (N.choose 3 : ℝ) := by
    exact_mod_cast hcNat
  rw [APResidual208.cast_choose_three] at hc
  have hfactor : 0 ≤ (N : ℝ)*(3*(N : ℝ)-2) :=
    mul_nonneg (Nat.cast_nonneg N) (by linarith only [hnR])
  have hcap : (∑ S ∈ Deleted N 12 F, ((Pool S).card : ℝ)) ≤ (N : ℝ)^3/6 := by
    nlinarith only [hc, hfactor]
  have hg := count_gate hnR
  have hreal : ((Deleted N 12 F).card : ℝ) ≤ 103*(N : ℝ) := by
    by_contra hnot
    have hlt : 103*(N : ℝ) < ((Deleted N 12 F).card : ℝ) := lt_of_not_ge hnot
    have hmul := mul_lt_mul_of_pos_left hlt htheta
    nlinarith only [hmul, hmass, hcap, hg]
  exact_mod_cast hreal

theorem actual_omitted_count {N c : ℕ} {F : Finset (Finset ℤ)}
    (hN : 115000 ≤ N) (hhi : N ≤ 2^18) (hF : Legal (Ground N) F) :
    (RootModel291012.Omitted N c F).card ≤ 103*N := by
  have hs : RootModel291012.Omitted N c F ⊆ Deleted N 12 F :=
    Finset.filter_subset _ _
  exact (Finset.card_le_card hs).trans (actual_deleted_count hN hhi hF)

#print axioms count_gate
#print axioms actual_deleted_member_price
#print axioms actual_deleted_count
#print axioms actual_omitted_count
end
end JSP233.DenseCount150465
