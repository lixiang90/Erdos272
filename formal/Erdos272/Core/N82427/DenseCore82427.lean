module

public import Erdos272.Resources.N82427.ThreeFiveSource82427

@[expose] public section

namespace JSP233.DenseCore82427
open StarCompletion APGeometry SourceBridge208 IntrinsicTriples208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def CorePrice (a : ℝ) : ℝ := (8981/30000 : ℝ)*a^2-(61/10 : ℝ)*a+8

theorem core_ge_self {a : ℝ} (ha : 92≤a) : a≤CorePrice a := by
  have hm := mul_nonneg (show 0≤a-92 by linarith only [ha])
    (show 0≤(8981/30000 : ℝ)*(a+92)-71/10 by linarith only [ha])
  unfold CorePrice
  nlinarith only [hm]

theorem core_growth {a k : ℝ} (ha : 92≤a) (hk : 0≤k) (hsmall : 3*k≤a) :
    CorePrice (a+k)≤CorePrice a+k*a := by
  have hc : (2*(8981/30000) : ℝ)*a+(8981/30000)*k-61/10≤a := by
    linarith only [ha, hsmall]
  have hm := mul_le_mul_of_nonneg_left hc hk
  unfold CorePrice
  nlinarith only [hm]

theorem core_coupling {a d : ℝ} (ha : 92≤a) (hd : 1≤d) (hsmall : 3*d≤a) :
    CorePrice (a+d-1)≤d*CorePrice a := by
  have hk : 0≤d-1 := by linarith only [hd]
  have hg := core_growth ha hk (by linarith only [hsmall] : 3*(d-1)≤a)
  rw [show a+(d-1)=a+d-1 by ring] at hg
  have hm := mul_le_mul_of_nonneg_left (core_ge_self ha) hk
  nlinarith only [hg, hm]

theorem actual_core_price {N : ℕ} {S : Finset ℤ}
    (hN : N≤2^18) (hground : S⊆Ground N) (hS : 2≤S.card)
    (ha : 92≤MaxAPSize S) :
    (Defect S : ℝ)*CorePrice (MaxAPSize S : ℝ)≤((Pool S).card : ℝ) := by
  have hc := ThreeFiveArithmetic82427.chord_bonus_quadratic (MaxAPSize S)
  have hsource := ThreeFiveSource82427.actual_core_price_plus_chord hN hground hS ha
  have hprice : CorePrice (MaxAPSize S : ℝ)≤DenseCore88404.CorePrice (MaxAPSize S : ℝ)+
      (ThreeFiveArithmetic82427.ChordBonus (MaxAPSize S) : ℝ) := by
    unfold CorePrice DenseCore88404.CorePrice
    linarith only [hc]
  exact (mul_le_mul_of_nonneg_left hprice (Nat.cast_nonneg (α := ℝ) (Defect S))).trans hsource

#print axioms core_ge_self
#print axioms core_growth
#print axioms core_coupling
#print axioms actual_core_price
end
end JSP233.DenseCore82427
