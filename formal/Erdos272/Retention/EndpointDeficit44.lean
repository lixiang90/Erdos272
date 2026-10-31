import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert

/-! Preserve the endpoint square in the raw retained resource expression.
These are scalar/weighted algebraic identities. They do not assume or prove
an actual-family cardinal bound or the complete prepared-family bridge. -/
namespace JSP233.EndpointDeficit44
noncomputable section

theorem endpoint_square_identity (L w : ℝ) :
    L^2/2+w^2/4-(2/3:ℝ)*L*w=
      (L+w)^2/102+(10*L-7*w)^2/204 := by ring

theorem quadratic_endpoint_deficit {L w k : ℝ} (hL : 0≤L) (hw : 0≤w)
    (hk : k≤5/3) :
    (L+w)^2/102≤L^2/2+w^2/4-(k-1)*L*w := by
  apply sub_nonneg.mp
  have he : (L^2/2+w^2/4-(k-1)*L*w)-(L+w)^2/102=
      (10*L-7*w)^2/204+(5/3-k)*L*w := by ring
  rw [he]
  exact add_nonneg (div_nonneg (sq_nonneg _) (by norm_num))
    (mul_nonneg (mul_nonneg (sub_nonneg.mpr hk) hL) hw)

theorem retained_endpoint_deficit {n q c a x s k : ℝ}
    (hq : 0≤q) (hc : 0≤c) (hx : 0≤x) (hsa : s≤a)
    (hk0 : 0≤k) (hk : k≤5/3) (hn : n=q+c+a+x) :
    k*x*(q+c)+a*x+k*c*(a-s)+s*(q+c+a)-s^2/2≤
      n^2/2-((q+c)+x)^2/102 := by
  let L := q+c
  let w := x+a-s
  have hL : 0≤L := add_nonneg hq hc
  have hw : 0≤w := by dsimp [w]; linarith
  have hxw : x≤w := by dsimp [w]; linarith
  have hmain : k*x*(q+c)+a*x+k*c*(a-s)+s*(q+c+a)-s^2/2≤
      k*L*w+w^2/4+s*(L+w)+s^2/2 := by
    have hp := mul_nonneg (mul_nonneg hk0 hq) (sub_nonneg.mpr hsa)
    apply sub_nonneg.mp
    calc
      0≤k*q*(a-s)+(x-(a-s))^2/4 :=
        add_nonneg hp (div_nonneg (sq_nonneg _) (by norm_num))
      _=(k*L*w+w^2/4+s*(L+w)+s^2/2)-
          (k*x*(q+c)+a*x+k*c*(a-s)+s*(q+c+a)-s^2/2) := by
        dsimp [L,w]
        ring
  have hi : n^2/2-(k*L*w+w^2/4+s*(L+w)+s^2/2)=
      L^2/2+w^2/4-(k-1)*L*w := by
    rw [hn]
    dsimp [L,w]
    ring
  have hqf := quadratic_endpoint_deficit hL hw hk
  have he : (L+x)^2≤(L+w)^2 :=
    (sq_le_sq₀ (add_nonneg hL hx) (add_nonneg hL hw)).mpr (by linarith only [hxw])
  have hchain : ((q+c)+x)^2/102≤
      n^2/2-(k*x*(q+c)+a*x+k*c*(a-s)+s*(q+c+a)-s^2/2) := by
    calc
      _≤(L+w)^2/102 := div_le_div_of_nonneg_right he (by norm_num)
      _≤L^2/2+w^2/4-(k-1)*L*w := hqf
      _=n^2/2-(k*L*w+w^2/4+s*(L+w)+s^2/2) := hi.symm
      _≤_ := sub_le_sub_left hmain _
  linarith only [hchain]

theorem weighted_middle_endpoint_deficit {N c L R rho s : ℝ}
    (hc : 0≤c) (hcL : c≤L) (hRN : R≤N) (hs : s≤R-L)
    (hrho : 0≤rho) (hdensity : 1≤(5/3:ℝ)*rho) :
    rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*(N^2/2-(L+(N-R))^2/102) := by
  have hh := retained_endpoint_deficit (n:=N) (q:=L-c) (c:=c) (a:=R-L)
    (x:=N-R) (s:=s) (k:=5/3) (sub_nonneg.mpr hcL) hc
    (sub_nonneg.mpr hRN) hs (by norm_num) le_rfl (by ring)
  have hh' : (5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+(5/3:ℝ)*c*(R-L-s)+
      s*R-s^2/2≤N^2/2-(L+(N-R))^2/102 := by
    convert hh using 1 <;> ring
  have hraw : rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
      rho*(s*R-s^2/2)≤rho*((5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+
        (5/3:ℝ)*c*(R-L-s)+s*R-s^2/2) := by
    apply sub_nonneg.mp
    have he : rho*((5/3:ℝ)*(N-R)*L+(R-L)*(N-R)+
        (5/3:ℝ)*c*(R-L-s)+s*R-s^2/2)-
        (rho*((5/3:ℝ)*L*(N-R)+(R-L)*(N-R))+c*((R-L)-s)+
          rho*(s*R-s^2/2))=((5/3:ℝ)*rho-1)*(c*(R-L-s)) := by ring
    rw [he]
    exact mul_nonneg (sub_nonneg.mpr hdensity) (mul_nonneg hc (sub_nonneg.mpr hs))
  exact hraw.trans (mul_le_mul_of_nonneg_left hh' hrho)

#print axioms endpoint_square_identity
#print axioms quadratic_endpoint_deficit
#print axioms retained_endpoint_deficit
#print axioms weighted_middle_endpoint_deficit
end
end JSP233.EndpointDeficit44
