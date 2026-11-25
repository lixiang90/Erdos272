module

public import Erdos272.Resources.N158375.DensePool158375
public import Erdos272.Resources.N291012.LowResourceBridges3040

@[expose] public section

namespace JSP233.DensePool150465
open StarCompletion APGeometry PureSource208 SourceBridge208 IntrinsicTriples208
open CoreUnionSource200000 MixedCore200000
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Price (s : ℝ) : ℝ := (233523/1000000 : ℝ)*s^2-(1953/400 : ℝ)*s

theorem physical_triangular {s e k m : ℕ} (hcap : s ≤ 2^18)
    (hse : e+m ≤ s) (hphi : 1001*(2*k) ≤ 192*m) :
    k*e*(e+1) ≤ physicalK s e := by
  induction e generalizing s with
  | zero => simp
  | succ e ih =>
      have hp := ih (s := s) hcap (by omega)
      have hq : m ≤ s-(e+1) := by omega
      have hr := LowResourceBridges3040.finite_totient_ratio
        (N := s) (m := s-(e+1))
        (hcap.trans_lt (by decide : 2^18 < 510510)) (Nat.sub_le _ _)
      have ht : 2*k ≤ Nat.totient (s-(e+1)) := by omega
      have hm := DensePool158375.multiplicity_first_step
        (s := s) (e := e+1) (by omega) (by omega)
      have hmul := Nat.mul_le_mul ht hm
      rw [physicalK_succ (by omega : e < s)]
      nlinarith only [hp, hmul]

theorem price_mono {x y : ℝ} (hx : 1000 ≤ x) (hxy : x ≤ y) : Price x ≤ Price y := by
  have hc : 0 ≤ (233523/1000000 : ℝ)*(x+y)-(1953/400 : ℝ) := by
    linarith only [hx, hxy]
  have hmul := mul_nonneg (sub_nonneg.mpr hxy) hc
  unfold Price
  nlinarith only [hmul]

theorem price_pos {s : ℝ} (hs : 1000 ≤ s) : 0 < Price s := by
  have hp : 0 < Price 1000 := by norm_num [Price]
  exact hp.trans_le (price_mono (by norm_num) hs)

theorem actual_pool_price {S : Finset ℤ} (hsize : 1000 ≤ S.card)
    (hcap : S.card ≤ 2^18) (hbad : ¬IsAP S) :
    Price (S.card : ℝ) ≤ ((Pool S).card : ℝ) := by
  let e := (7*S.card+99)/100
  have htwo : 2 ≤ S.card := by omega
  have hr : 7*S.card ≤ 100*e ∧ 100*e ≤ 7*S.card+99 := by
    dsimp only [e]
    omega
  have hcut : e+600 ≤ S.card := by
    dsimp only [e]
    omega
  have hsR : (1000 : ℝ) ≤ S.card := by exact_mod_cast hsize
  by_cases hlarge : e ≤ Defect S
  · have hp := physical_triangular (k := 50) (m := 600) hcap hcut (by decide)
    have hn := hp.trans (actual_source_of_defect htwo hlarge)
    have hpR : (50 : ℝ)*(e : ℝ)*((e : ℝ)+1) ≤ ((Pool S).card : ℝ) := by
      exact_mod_cast hn
    have hre : (7 : ℝ)*S.card ≤ 100*(e : ℝ) := by exact_mod_cast hr.1
    have hmul := mul_nonneg (sub_nonneg.mpr hre)
      (show (0 : ℝ) ≤ 100*(e : ℝ)+7*S.card by positivity)
    unfold Price
    nlinarith only [hpR, hmul, Nat.cast_nonneg (α := ℝ) e,
      Nat.cast_nonneg (α := ℝ) S.card, sq_nonneg (S.card : ℝ)]
  · have hmax := maxAPSize_le_card S
    have hsplit : MaxAPSize S+Defect S=S.card := by
      unfold Defect
      omega
    have haNat : 93*S.card ≤ 100*MaxAPSize S := by omega
    have haR : (93 : ℝ)*S.card ≤ 100*(MaxAPSize S : ℝ) := by exact_mod_cast haNat
    have ha : (93/100 : ℝ)*S.card ≤ (MaxAPSize S : ℝ) := by linarith only [haR]
    have he := crooked_defect_positive htwo hbad
    have hunit : UnitBound (MaxAPSize S) ≤ (Pool S).card := by
      have hm : UnitBound (MaxAPSize S) ≤ Defect S*UnitBound (MaxAPSize S) := by
        simpa only [one_mul] using Nat.mul_le_mul_right (UnitBound (MaxAPSize S)) he
      exact hm.trans (actual_union_core_source htwo)
    have hu := AnalyticCore180000.unit_large (hmax.trans hcap)
    have hunitR : (UnitBound (MaxAPSize S) : ℝ) ≤ ((Pool S).card : ℝ) := by
      exact_mod_cast hunit
    have hc : 0 ≤ (27/100 : ℝ)*((MaxAPSize S : ℝ)+(93/100 : ℝ)*S.card)-21/4 := by
      linarith only [ha, hsR]
    have hmul := mul_nonneg (sub_nonneg.mpr ha) hc
    unfold Price
    nlinarith only [hu, hunitR, hmul]

#print axioms physical_triangular
#print axioms price_mono
#print axioms price_pos
#print axioms actual_pool_price
end
end JSP233.DensePool150465
