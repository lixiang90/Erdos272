module

public import Erdos272.Counting.N82427.JointEllipse82427

@[expose] public section

namespace JSP233.RootJoint67702
open Recovery208 JointEllipse82427
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem root_substitution {n c L charge : ℝ}
    (hc : c≤L) (hmono : 0≤n+1-charge-2*L) :
    c*(n+1-charge-c)≤L*(n+1-charge-L) := by
  have hleft : 0≤L-c := sub_nonneg.mpr hc
  have hright : 0≤n+1-charge-L-c := by linarith only [hc,hmono]
  have hp := mul_nonneg hleft hright
  nlinarith only [hp]

theorem loss_bound (p : Parameters) {r n c L w : ℝ}
    (hlambda : 0≤p.multiplier) (hU : 0<U p) (hD : 0<Determinant p)
    (hc : c≤L) (hmono : 0≤n+1-p.multiplier*r-2*L)
    (hp : WidthProfile L w≤p.A*n+(p.B+r)*L+p.W*w+p.C-r*c) :
    c*(n-c)+c+w^2/4+w≤Upper p n := by
  have hs := square_identity p hD.ne' n L w
  have hnon := mul_nonneg hD.le (sq_nonneg (2*U p*L+2*V p*w-X p n))
  have hsq := sq_nonneg (2*Determinant p*w-(U p*Y p-V p*X p n))
  have hscale : 0<4*U p*Determinant p := by positivity
  have hmul : 0≤(4*U p*Determinant p)*
      (Fraction p n+U p*L^2+2*V p*L*w+Z p*w^2-X p n*L-Y p*w) := by
    linarith only [hs,hnon,hsq]
  have hf := nonneg_of_mul_nonneg_right hmul hscale
  have hpaid := mul_le_mul_of_nonneg_left hp hlambda
  have hroot := root_substitution hc hmono
  dsimp only [WidthProfile] at hpaid
  dsimp only [Upper,U,V,Z,X,Y] at hf ⊢
  nlinarith only [hf,hpaid,hroot]

#print axioms root_substitution
#print axioms loss_bound
end
end JSP233.RootJoint67702
