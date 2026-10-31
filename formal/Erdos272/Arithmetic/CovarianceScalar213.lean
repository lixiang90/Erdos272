import Erdos272.Resources.FrontierSum208
import Erdos272.Arithmetic.FrontierDensity208
import Erdos272.Arithmetic.HarmonicLog55

/-! Scalar closure for the weaker covariance route using only D(c)>=0.
No family cardinality or geometry oracle is assumed.  Finite row and
convolution bounds will be supplied by the separate resource module. -/
namespace JSP233.CovarianceScalar213
open FrontierDensity208 FrontierSum208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def K : ℝ := 23359/80000
def Alpha : ℝ := 1/Rho-1
def Polynomial (t : ℝ) : ℝ := t^2/4+(7/10)*t+3/5
def CentrePolynomial (t : ℝ) : ℝ := t^2/4+(27869/40000)*t+23069/40000

theorem rho_pos : (0 : ℝ)<Rho := by norm_num [Rho]
theorem alpha_bounds : (0 : ℝ)≤Alpha ∧ Alpha≤129/200 := by norm_num [Alpha,Rho]
theorem K_nonneg : (0 : ℝ)≤K := by norm_num [K]

theorem quadratic_main {c Z : ℝ} (hZ : Rho*Z≤1) :
    -c^2/2+(1-Rho)^2*c^2/(2*Rho)*Z≤-K*c^2 := by
  have hp : (0 : ℝ)≤Alpha^2*c^2/2 := by positivity
  have hm:=mul_le_mul_of_nonneg_left hZ hp
  have he : (1-Rho)^2*c^2/(2*Rho)*Z=(Alpha^2*c^2/2)*(Rho*Z) := by
    dsimp only [Alpha,Rho]
    ring
  have hs : Alpha^2≤(129/200 : ℝ)^2 := by
    have hh:=mul_self_le_mul_self alpha_bounds.1 alpha_bounds.2
    simpa only [pow_two] using hh
  have hc:=mul_le_mul_of_nonneg_right hs (show (0 : ℝ)≤c^2/2 by positivity)
  rw [he]
  dsimp only [K]
  nlinarith only [hm,hc]

theorem central_deficit {c a : ℝ} (hc : 0≤c) (ha : 0≤a) (hphase : a≤Alpha*c) :
    -K*c^2-c*a≤-K*(c+a)^2 := by
  have hbound : a≤(129/200 : ℝ)*c := hphase.trans
    (mul_le_mul_of_nonneg_right alpha_bounds.2 hc)
  have hsq:=mul_le_mul_of_nonneg_right hbound ha
  have hprod:=mul_nonneg hc ha
  dsimp only [K]
  nlinarith only [hsq,hprod]

/-- The exact centre coefficients are .696725 and .576725.  This uses
only weighted z <= (61/200)H, rather than the stronger D integral lemma. -/
theorem central_total {c a Z weighted square rowError logc H : ℝ}
    (hc : 0≤c) (ha : 0≤a) (hlog : 0≤logc) (hphase : a≤Alpha*c)
    (hZ : Rho*Z≤1) (hweighted : weighted≤(61/200)*H) (hH : H≤1+logc)
    (hsquare : square≤(19/50)*c)
    (hrow : rowError≤c*(logc^2/4+logc/2)) :
    -c^2/2-c*a+(1-Rho)^2*c^2/(2*Rho)*Z+Alpha*c*weighted+square+rowError≤
      -K*(c+a)^2+c*CentrePolynomial logc := by
  have hw : weighted≤(61/200)*(1+logc) :=
    hweighted.trans (mul_le_mul_of_nonneg_left hH (by norm_num))
  have hcw:=mul_le_mul_of_nonneg_left hw (mul_nonneg alpha_bounds.1 hc)
  have hcl:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right alpha_bounds.2 hc)
    (show (0 : ℝ)≤(61/200)*(1+logc) by positivity)
  have hlin : Alpha*c*weighted≤(129/200)*c*((61/200)*(1+logc)) := hcw.trans hcl
  have hquad:=quadratic_main (c := c) hZ
  have hdef:=central_deficit hc ha hphase
  calc
    _≤-K*(c+a)^2+(129/200)*c*((61/200)*(1+logc))+(19/50)*c+
        c*(logc^2/4+logc/2) := by linarith only [hlin,hquad,hdef,hsquare,hrow]
    _=_ := by dsimp only [CentrePolynomial];ring

theorem centre_polynomial_le {t : ℝ} (ht : 0≤t) : CentrePolynomial t≤Polynomial t := by
  dsimp only [CentrePolynomial,Polynomial]
  nlinarith only [ht]

theorem polynomial_nonneg {t : ℝ} (ht : 0≤t) : 0≤Polynomial t := by
  dsimp only [Polynomial]
  positivity

theorem polynomial_mono {x y : ℝ} (hx : 0≤x) (hxy : x≤y) : Polynomial x≤Polynomial y := by
  dsimp only [Polynomial]
  gcongr

theorem scaled_polynomial_mono {c L : ℝ} (hc : 1≤c) (hcl : c≤L) :
    c*Polynomial (Real.log c)≤L*Polynomial (Real.log L) := by
  have hc0 : (0 : ℝ)<c := by linarith only [hc]
  have hl:=Real.log_le_log hc0 hcl
  have hlogc:=Real.log_nonneg hc
  have hp:=polynomial_mono hlogc hl
  exact mul_le_mul hcl hp (polynomial_nonneg hlogc) (by linarith only [hc,hcl])

theorem log64_upper : Real.log (64 : ℝ)≤9/2 := by
  have he : (64 : ℝ)=(2 : ℝ)^6 := by norm_num
  rw [he,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  have hh:=HarmonicLog55.actual_log_two_upper
  linarith only [hh]

theorem log_linear_large {L : ℝ} (hL : 64≤L) : Real.log L≤(9/128)*L := by
  have hpos : (0 : ℝ)<L := by linarith only [hL]
  have hh:=Real.log_le_sub_one_of_pos (div_pos hpos (by norm_num : (0 : ℝ)<64))
  rw [Real.log_div hpos.ne' (by norm_num : (64 : ℝ)≠0)] at hh
  have hl:=log64_upper
  linarith only [hh,hl,hL]

theorem old_new_gap (t : ℝ) :
    FrontierSum208.Polynomial t-Polynomial t=(219/100)*t+9660409/4000000 := by
  dsimp only [FrontierSum208.Polynomial,Polynomial]
  ring

theorem low_phase_absorption {L : ℝ} (hL : 64≤L) :
    -L^2/2+L*FrontierSum208.Polynomial (Real.log L)≤
      -K*L^2+L*Polynomial (Real.log L) := by
  have hl:=log_linear_large hL
  have hper : (219/100 : ℝ)*Real.log L+9660409/4000000≤(1/2-K)*L := by
    dsimp only [K]
    nlinarith only [hl,hL]
  have hmul:=mul_le_mul_of_nonneg_left hper (show (0 : ℝ)≤L by linarith only [hL])
  have hg:=old_new_gap (Real.log L)
  have hgm:=congrArg (fun x : ℝ=>L*x) hg
  nlinarith only [hmul,hgm]

/-- For small L the old resource bound may be retained.  The allowance850
also covers the old actual profile consumer's extra constant3. -/
theorem small_phase_absorption {L : ℕ} (hL : 1≤L) (hsmall : L≤63) :
    (L : ℝ)*FrontierSum208.Polynomial (Real.log L)+3≤
      (L : ℝ)*Polynomial (Real.log L)+850 := by
  have hLpos : (0 : ℝ)<L := by exact_mod_cast (show 0<L by omega)
  have hL63 : (L : ℝ)≤63 := by exact_mod_cast hsmall
  have hl : Real.log L≤5 := by
    have hh:=Real.log_le_log hLpos (show (L : ℝ)≤64 by linarith only [hL63])
    linarith only [hh,log64_upper]
  have hm:=mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg (α := ℝ) L)
  have hg:=old_new_gap (Real.log L)
  nlinarith only [hm,hg,hL63]

#print axioms quadratic_main
#print axioms central_deficit
#print axioms central_total
#print axioms centre_polynomial_le
#print axioms scaled_polynomial_mono
#print axioms log64_upper
#print axioms log_linear_large
#print axioms low_phase_absorption
#print axioms small_phase_absorption
end
end JSP233.CovarianceScalar213
