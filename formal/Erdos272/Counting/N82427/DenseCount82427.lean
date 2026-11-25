module

public import Erdos272.Resources.N82427.DensePool82427
public import Erdos272.Resources.APResidual208
public import Erdos272.Resources.N291012.RootModel291012

@[expose] public section

namespace JSP233.DenseCount82427
open StarCompletion APGeometry DenseDeletion40 IntrinsicTriples208 DensePool82427
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Gate (rho beta : ℝ) : Prop :=
  1/12≤rho ∧ 0≤beta ∧ 0<beta*(8981/30000)*rho^2-1/6 ∧
    0<(beta*(8981/30000)*rho^2-1/6)*82427-beta*(100481/15000)*rho

theorem deleted_gate : Gate (1/12) (1609/20) := by norm_num [Gate]
theorem quarter_gate : Gate (1/4) (223/25) := by norm_num [Gate]
theorem three_tenths_gate : Gate (3/10) (1239/200) := by norm_num [Gate]

theorem count_gate {n rho beta : ℝ} (hn : 82427≤n) (hg : Gate rho beta) :
    n^3/6 < beta*n*Price (rho*n) := by
  obtain ⟨_hrho, hbeta, hleading, hgate⟩ := hg
  have hn0 : 0<n := by linarith only [hn]
  have hs := mul_le_mul_of_nonneg_left hn hleading.le
  have hlin : 0<(beta*(8981/30000)*rho^2-1/6)*n-beta*(100481/15000)*rho := by
    linarith only [hs, hgate]
  have hp := mul_pos (sq_pos_of_pos hn0) hlin
  have hc : 0≤beta*(431981/30000)*n := by positivity
  have he : beta*n*Price (rho*n)-n^3/6 =
      n^2*((beta*(8981/30000)*rho^2-1/6)*n-beta*(100481/15000)*rho)+
        beta*(431981/30000)*n := by
    unfold Price
    ring
  apply sub_pos.mp
  rw [he]
  exact add_pos_of_pos_of_nonneg hp hc

theorem actual_density_count {N : ℕ} {E : Finset (Finset ℤ)} {rho beta : ℝ}
    (hN : 82427≤N) (hcap : N≤2^18) (hE : Legal (Ground N) E)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, rho*(N : ℝ)<S.card)
    (hg : Gate rho beta) : (E.card : ℝ)≤beta*N := by
  have hn : (82427 : ℝ)≤N := by exact_mod_cast hN
  have hn0 : (0 : ℝ)≤N := Nat.cast_nonneg N
  have hrho := mul_le_mul_of_nonneg_right hg.1 hn0
  have hsize : (128 : ℝ)≤rho*N := by linarith only [hn, hrho]
  have htheta : 0<Price (rho*N) := price_pos hsize
  have hpoint : ∀ S∈E, Price (rho*N)≤((Pool S).card : ℝ) := by
    intro S hS
    have hd := hdense S hS
    have hs : 128≤S.card := by
      exact_mod_cast (show (128 : ℝ)≤S.card by linarith only [hsize, hd])
    exact (price_mono hsize hd.le).trans (actual_pool_price hs hcap (hE.1 S hS) (hbad S hS))
  have hmass : Price (rho*N)*(E.card : ℝ)≤∑ S∈E, ((Pool S).card : ℝ) := by
    calc
      _ = ∑ _S∈E, Price (rho*N) := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hpoint
  have hcapacity := actual_capacity hE
  rw [ground_card] at hcapacity
  have hc : (∑ S∈E, ((Pool S).card : ℝ))≤(N.choose 3 : ℝ) := by exact_mod_cast hcapacity
  rw [APResidual208.cast_choose_three] at hc
  have hfactor : 0≤(N : ℝ)*(3*(N : ℝ)-2) :=
    mul_nonneg hn0 (by linarith only [hn])
  have hpool : (∑ S∈E, ((Pool S).card : ℝ))≤(N : ℝ)^3/6 := by
    nlinarith only [hc, hfactor]
  have hgcount := count_gate hn hg
  by_contra hnot
  have hlt : beta*(N : ℝ)<E.card := lt_of_not_ge hnot
  have hm := mul_lt_mul_of_pos_left hlt htheta
  nlinarith only [hm, hmass, hpool, hgcount]

theorem actual_deleted_count {N : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427≤N) (hcap : N≤2^18) (hF : Legal (Ground N) F) :
    ((Deleted N 12 F).card : ℝ)≤(1609/20 : ℝ)*N := by
  have hbad : ∀ S∈Deleted N 12 F, ¬IsAP S :=
    fun S hS => (Finset.mem_filter.mp hS).2.1
  have hdense : ∀ S∈Deleted N 12 F, (1/12 : ℝ)*N<S.card := by
    intro S hS
    have hd : (N : ℝ)<12*(S.card : ℝ) := by
      exact_mod_cast (Finset.mem_filter.mp hS).2.2
    nlinarith only [hd]
  have hc := actual_density_count hN hcap (actual_deleted_legal (r := 12) hF)
    hbad hdense deleted_gate
  exact_mod_cast hc

theorem actual_omitted_count {N c : ℕ} {F : Finset (Finset ℤ)}
    (hN : 82427≤N) (hcap : N≤2^18) (hF : Legal (Ground N) F) :
    ((RootModel291012.Omitted N c F).card : ℝ)≤(1609/20 : ℝ)*N := by
  have hs : RootModel291012.Omitted N c F⊆Deleted N 12 F := Finset.filter_subset _ _
  have hc : ((RootModel291012.Omitted N c F).card : ℝ)≤(Deleted N 12 F).card := by
    exact_mod_cast Finset.card_le_card hs
  exact hc.trans (actual_deleted_count hN hcap hF)

theorem actual_quarter_count {N : ℕ} {E : Finset (Finset ℤ)}
    (hN : 82427≤N) (hcap : N≤2^18) (hE : Legal (Ground N) E)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, (N : ℝ)/4<S.card) :
    (E.card : ℝ)≤(223/25 : ℝ)*N := by
  have hd : ∀ S∈E, (1/4 : ℝ)*N<S.card := by
    intro S hS
    have hh := hdense S hS
    nlinarith only [hh]
  have hc := actual_density_count hN hcap hE hbad hd quarter_gate
  exact_mod_cast hc

theorem actual_three_tenths_count {N : ℕ} {E : Finset (Finset ℤ)}
    (hN : 82427≤N) (hcap : N≤2^18) (hE : Legal (Ground N) E)
    (hbad : ∀ S∈E, ¬IsAP S) (hdense : ∀ S∈E, (3/10 : ℝ)*N<S.card) :
    (E.card : ℝ)≤(1239/200 : ℝ)*N :=
  actual_density_count hN hcap hE hbad hdense three_tenths_gate

#print axioms deleted_gate
#print axioms quarter_gate
#print axioms three_tenths_gate
#print axioms count_gate
#print axioms actual_density_count
#print axioms actual_deleted_count
#print axioms actual_omitted_count
#print axioms actual_quarter_count
#print axioms actual_three_tenths_count
end
end JSP233.DenseCount82427
