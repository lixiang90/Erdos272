module

public import Erdos272.Core.N88404.DenseCore88404

@[expose] public section

namespace JSP233.DenseCore86412
open DenseCore88404
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem core_growth {a k : ℝ} (ha : 92≤a) (hk : 0≤k) (hsmall : 3*k≤a) :
    CorePrice (a+k) ≤ CorePrice a+k*a := by
  have hc : (2*(2977/10000) : ℝ)*a+(2977/10000)*k-6≤a := by
    linarith only [ha, hsmall]
  have hm := mul_le_mul_of_nonneg_left hc hk
  unfold CorePrice
  nlinarith only [hm]

theorem core_coupling {a d : ℝ} (ha : 92≤a) (hd : 1≤d) (hsmall : 3*d≤a) :
    CorePrice (a+d-1) ≤ d*CorePrice a := by
  have hk : 0≤d-1 := by linarith only [hd]
  have hg := core_growth ha hk (by linarith only [hsmall] : 3*(d-1)≤a)
  have he : a+(d-1)=a+d-1 := by ring
  rw [he] at hg
  have hm := mul_le_mul_of_nonneg_left (DenseCore88404.core_ge_self ha) hk
  nlinarith only [hg, hm]

#print axioms core_growth
#print axioms core_coupling
end JSP233.DenseCore86412
