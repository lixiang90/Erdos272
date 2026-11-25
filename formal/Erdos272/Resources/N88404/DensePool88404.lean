module

public import Erdos272.Core.N88404.DenseCore88404
public import Erdos272.Resources.N150465.DensePool150465

@[expose] public section

namespace JSP233.DensePool88404
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208 DenseCore88404
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Price (s : ℝ) : ℝ :=
  (2977/10000 : ℝ)*s^2-(32977/5000 : ℝ)*s+142977/10000

theorem price_eq_core (s : ℝ) : Price s=CorePrice (s-1) := by
  unfold Price CorePrice
  ring

theorem price_mono {x y : ℝ} (hx : 7350≤x) (hxy : x≤y) : Price x≤Price y := by
  have hc : 0≤(2977/10000 : ℝ)*(x+y)-(32977/5000 : ℝ) := by
    linarith only [hx, hxy]
  have hm := mul_nonneg (sub_nonneg.mpr hxy) hc
  unfold Price
  nlinarith only [hm]

theorem price_pos {s : ℝ} (hs : 7350≤s) : 0<Price s := by
  have hp : 0<Price 7350 := by norm_num [Price]
  exact hp.trans_le (price_mono (by norm_num) hs)

theorem actual_pool_price {N : ℕ} {S : Finset ℤ} (hsize : 7350≤S.card)
    (hN : N≤2^18) (hground : S⊆Ground N) (hbad : ¬IsAP S) :
    Price (S.card : ℝ) ≤ ((Pool S).card : ℝ) := by
  have hcap : S.card≤2^18 :=
    (show S.card≤N by simpa only [ground_card] using Finset.card_le_card hground).trans hN
  let e := (S.card+47)/48
  have htwo : 2≤S.card := by omega
  have hr : S.card≤48*e ∧ 48*e≤S.card+47 := by dsimp only [e]; omega
  have hcut : e+7195≤S.card := by dsimp only [e]; omega
  have hsR : (7350 : ℝ)≤S.card := by exact_mod_cast hsize
  by_cases hlarge : e≤Defect S
  · have hp := DensePool150465.physical_triangular (k := 690) (m := 7195) hcap hcut (by decide)
    have hn := hp.trans (actual_source_of_defect htwo hlarge)
    have hpR : (690 : ℝ)*(e : ℝ)*((e : ℝ)+1) ≤ ((Pool S).card : ℝ) := by
      exact_mod_cast hn
    have hre : (S.card : ℝ)≤48*(e : ℝ) := by exact_mod_cast hr.1
    have hm := mul_nonneg (sub_nonneg.mpr hre)
      (show (0 : ℝ)≤48*(e : ℝ)+S.card by positivity)
    unfold Price
    nlinarith only [hpR, hm, hsR, Nat.cast_nonneg (α := ℝ) e,
      Nat.cast_nonneg (α := ℝ) S.card, sq_nonneg (S.card : ℝ)]
  · have hsplit : MaxAPSize S+Defect S=S.card := by
      have hh := maxAPSize_le_card S
      unfold Defect
      omega
    have hd := MixedCore200000.crooked_defect_positive htwo hbad
    have hsmall : 47*Defect S≤MaxAPSize S := by omega
    have ha : 92≤MaxAPSize S := by omega
    have hpool := actual_core_price hN hground htwo ha
    have hc := core_coupling (by exact_mod_cast ha : (92 : ℝ)≤MaxAPSize S)
      (by exact_mod_cast hd : (1 : ℝ)≤Defect S)
      (by exact_mod_cast hsmall : (47 : ℝ)*Defect S≤MaxAPSize S)
    have hsum : (MaxAPSize S : ℝ)+Defect S=S.card := by exact_mod_cast hsplit
    rw [hsum, ←price_eq_core] at hc
    exact hc.trans hpool

#print axioms price_eq_core
#print axioms price_mono
#print axioms price_pos
#print axioms actual_pool_price
end
end JSP233.DensePool88404
