module

public import Erdos272.Resources.N150465.DensePool150465
public import Erdos272.Counting.N118533.DenseBonus118533

@[expose] public section

namespace JSP233.DensePool94488
open StarCompletion APGeometry PureSource208 SourceBridge208 IntrinsicTriples208
open CoreUnionSource200000 MixedCore200000 StarArithmetic130000 CorrelatedSource118533
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Price (s : ℝ) : ℝ := (3249439/11520000 : ℝ)*s^2-(47/8 : ℝ)*s

theorem price_mono {x y : ℝ} (hx : 7500 ≤ x) (hxy : x ≤ y) : Price x ≤ Price y := by
  have hc : 0 ≤ (3249439/11520000 : ℝ)*(x+y)-(47/8 : ℝ) := by
    linarith only [hx, hxy]
  have hmul := mul_nonneg (sub_nonneg.mpr hxy) hc
  unfold Price
  nlinarith only [hmul]

theorem price_pos {s : ℝ} (hs : 7500 ≤ s) : 0 < Price s := by
  have hp : 0 < Price 7500 := by norm_num [Price]
  exact hp.trans_le (price_mono (by norm_num) hs)

theorem actual_pool_price {N : ℕ} {S : Finset ℤ} (hsize : 7500 ≤ S.card)
    (hN : N ≤ 2^18) (hground : S ⊆ Ground N) (hbad : ¬IsAP S) :
    Price (S.card : ℝ) ≤ ((Pool S).card : ℝ) := by
  have hcap : S.card ≤ 2^18 :=
    (show S.card ≤ N by simpa only [ground_card] using Finset.card_le_card hground).trans hN
  let e := (S.card+47)/48
  have htwo : 2 ≤ S.card := by omega
  have hr : S.card ≤ 48*e ∧ 48*e ≤ S.card+47 := by
    dsimp only [e]
    omega
  have hcut : e+7342 ≤ S.card := by
    dsimp only [e]
    omega
  have hsR : (7500 : ℝ) ≤ S.card := by exact_mod_cast hsize
  by_cases hlarge : e ≤ Defect S
  · have hp := DensePool150465.physical_triangular (k := 700) (m := 7342) hcap hcut (by decide)
    have hn := hp.trans (actual_source_of_defect htwo hlarge)
    have hpR : (700 : ℝ)*(e : ℝ)*((e : ℝ)+1) ≤ ((Pool S).card : ℝ) := by
      exact_mod_cast hn
    have hre : (S.card : ℝ) ≤ 48*(e : ℝ) := by exact_mod_cast hr.1
    have hmul := mul_nonneg (sub_nonneg.mpr hre)
      (show (0 : ℝ) ≤ 48*(e : ℝ)+S.card by positivity)
    unfold Price
    nlinarith only [hpR, hmul, Nat.cast_nonneg (α := ℝ) e,
      Nat.cast_nonneg (α := ℝ) S.card, sq_nonneg (S.card : ℝ)]
  · have hmax := maxAPSize_le_card S
    have hsplit : MaxAPSize S+Defect S=S.card := by unfold Defect; omega
    have haNat : 47*S.card ≤ 48*MaxAPSize S := by omega
    have haR : (47 : ℝ)*S.card ≤ 48*(MaxAPSize S : ℝ) := by exact_mod_cast haNat
    have ha : (47/48 : ℝ)*S.card ≤ (MaxAPSize S : ℝ) := by linarith only [haR]
    have he := crooked_defect_positive htwo hbad
    have hstar := actual_eight_star_source hN hground htwo (by omega : 12 ≤ MaxAPSize S)
    have hunit : UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S) ≤ (Pool S).card := by
      have hm : UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S) ≤
          Defect S*(UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S)) := by
        simpa only [one_mul] using Nat.mul_le_mul_right
          (UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S)) he
      exact hm.trans hstar
    have hu := DenseBonus118533.combined_quadratic (by omega : 92 ≤ MaxAPSize S) (hmax.trans hcap)
    have hunitR : (UnitBound (MaxAPSize S)+Bonus Primes (MaxAPSize S) : ℕ) ≤
        ((Pool S).card : ℝ) := by exact_mod_cast hunit
    have hc : 0 ≤ (1471/5000 : ℝ)*((MaxAPSize S : ℝ)+(47/48 : ℝ)*S.card)-6 := by
      linarith only [ha, hsR]
    have hmul := mul_nonneg (sub_nonneg.mpr ha) hc
    unfold Price
    nlinarith only [hu, hunitR, hmul]

#print axioms price_mono
#print axioms price_pos
#print axioms actual_pool_price
end
end JSP233.DensePool94488
