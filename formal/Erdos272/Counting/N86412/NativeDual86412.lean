module

public import Erdos272.Resources.Recovery208

@[expose] public section

namespace JSP233.NativeDual86412
open Recovery208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Dual (u v : ℝ) : ℝ := (40000*u^2+131600*u*v+114959*v^2)/3359

theorem dual_nonnegative (u v : ℝ) : 0≤Dual u v := by
  have he : Dual u v=((200*u+329*v)^2+6718*v^2)/3359 := by
    unfold Dual
    ring
  rw [he]
  positivity

theorem dual_square_bound (u v x y : ℝ) :
    (u*x+v*y)^2 ≤ Dual u v*WidthProfile x y := by
  have he : Dual u v*WidthProfile x y-(u*x+v*y)^2 =
      ((65800*u+114959*v)*x-(40000*u+65800*v)*y)^2/268720000 := by
    unfold Dual WidthProfile
    ring
  have hn : 0≤((65800*u+114959*v)*x-(40000*u+65800*v)*y)^2/(268720000 : ℝ) :=
    div_nonneg (sq_nonneg _) (by norm_num)
  linarith only [he, hn]

theorem actual_dual_bound {n L w A tL tw C target u v : ℝ}
    (hp : WidthProfile L w ≤ A*n+tL*L+tw*w+C)
    (ht : 0<target-(u*LeftCentre tL tw+v*WidthCentre tL tw))
    (hg : Dual u v*(A*n+ShiftEnergy tL tw C) <
      (target-(u*LeftCentre tL tw+v*WidthCentre tL tw))^2) :
    u*L+v*w < target := by
  have hs := actual_profile_shift hp
  have hb := dual_square_bound u v (L-LeftCentre tL tw) (w-WidthCentre tL tw)
  have hpaid := mul_le_mul_of_nonneg_left hs (dual_nonnegative u v)
  have hsq : (u*L+v*w-(u*LeftCentre tL tw+v*WidthCentre tL tw))^2 ≤
      Dual u v*(A*n+ShiftEnergy tL tw C) := by
    calc
      _ = (u*(L-LeftCentre tL tw)+v*(w-WidthCentre tL tw))^2 := by ring
      _ ≤ _ := hb.trans hpaid
  by_contra hh
  have hge : target≤u*L+v*w := le_of_not_gt hh
  have hprod := mul_nonneg (sub_nonneg.mpr hge)
    (show 0≤u*L+v*w+target-2*(u*LeftCentre tL tw+v*WidthCentre tL tw)
      by linarith only [ht, hge])
  nlinarith only [hsq, hg, hprod]

#print axioms dual_nonnegative
#print axioms dual_square_bound
#print axioms actual_dual_bound
end
end JSP233.NativeDual86412
