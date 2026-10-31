import Erdos272.Retention.CrossBad120
namespace JSP233.Shape140
open StarCompletion APGeometry
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
theorem actual_bad13_shape {N L R m : ℕ}
    (hLR : L≤R) (hRN : R≤N) (hm : N<11*m)
    (hpay : 369*(L+N-R)≤10*N) :
    16*((L+N-R)+(R-L+1)/13-m)≤7*(L+N-R) := by
  let w := L+N-R
  let M := R-L+1
  have hMw : M+w=N+1 := by dsimp only [M,w];omega
  have hdiv := Nat.mul_div_le M 13
  by_cases hs : w+M/13<m
  · have hb : w+M/13-m=0 := by omega
    change 16*(w+M/13-m)≤7*w
    rw [hb]
    omega
  · have hsub := Nat.sub_add_cancel (show m≤w+M/13 by omega)
    have hd : 143*(w+M/13-m)+2*N+2≤132*w := by nlinarith only [hsub,hdiv,hMw,hm]
    change 369*w≤10*N at hpay
    change 16*(w+M/13-m)≤7*w
    omega


#print axioms actual_bad13_shape
end
end JSP233.Shape140
