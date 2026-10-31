import Erdos272.Resources.FrontierGrid208

namespace JSP233.FiniteFrontier209
open CoprimeDensity52 HarmonicAbel29 ResourceSymmetry56 LocalizedMiddle208 FrontierGrid208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_triangle_coarse {N e : ℕ} (hN : 1≤N) (he : 1≤e) (heN : e≤N) :
    (3/10 : ℝ)*(e : ℝ)^2-2*(e : ℝ)*Harmonic N-1/2 ≤ TotientTriangle e := by
  have hz := reciprocalSquareSum_bounds hN
  have hzpos : (0 : ℝ)<reciprocalSquareSum N := by linarith only [hz.1]
  have hdensity : (3/5 : ℝ)≤finiteCoprimeDensity N := by
    change (3/5 : ℝ)≤(reciprocalSquareSum N)⁻¹
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hzpos).mpr
    nlinarith only [hz.2]
  have hharm : reciprocalSum N=Harmonic N := by simp only [reciprocalSum,Harmonic,one_div]
  have herr := (abs_le.mp (coprimeRectangle_density_error hN heN heN)).1
  rw [hharm] at herr
  have hs : 2*(TotientTriangle e : ℝ)+1=(coprimeRectangle e e).card := by
    have hs := actual_square_symmetry e
    rw [if_pos (by omega : 0<e),actual_triangle_totient] at hs
    exact_mod_cast hs
  have hprod := mul_le_mul_of_nonneg_right hdensity (sq_nonneg (e : ℝ))
  nlinarith only [herr,hs,hprod]

theorem actual_large_triangle {N e : ℕ} (hN : 1≤N) (he : 4000≤e)
    (heN : e≤N) (hH : Harmonic N≤19) :
    (29/100 : ℝ)*(e : ℝ)^2≤TotientTriangle e := by
  have hu := actual_triangle_coarse hN (by omega : 1≤e) heN
  have heR : (4000 : ℝ)≤e := by exact_mod_cast he
  have he0 : (0 : ℝ)≤e := Nat.cast_nonneg e
  have hsq := mul_le_mul_of_nonneg_right heR he0
  have hh := mul_le_mul_of_nonneg_left hH (show (0 : ℝ)≤2*e by positivity)
  nlinarith only [hu,heR,hsq,hh]

theorem coarse_frontier_le_main {rho C A e : ℝ}
    (hrho : 3/5≤rho) (hrho1 : rho≤1) (hC : 0≤C) (hA : 0≤A)
    (he : 43≤e) (hscale : 25*(C+A)≤18*e) :
    -C*A+(1-rho)*C*e-(29/100)*e^2+(17/200)*e ≤ FrontierMain rho C A := by
  have he0 : 0≤e := by linarith only [he]
  have hce := mul_le_mul_of_nonneg_right (show 1-rho≤(2/5 : ℝ) by linarith only [hrho])
    (mul_nonneg hC he0)
  have hca := mul_nonneg (sub_nonneg.mpr hrho1) (mul_nonneg hC hA)
  have haa := mul_le_mul_of_nonneg_right hrho1 (sq_nonneg A)
  have hscaled := mul_le_mul_of_nonneg_right hscale he0
  have hAlimit : 25*A≤18*e := by linarith only [hscale,hC]
  have hAsq := mul_le_mul_of_nonneg_right hAlimit hA
  have hAe := mul_nonneg hA he0
  have heSq := mul_le_mul_of_nonneg_right he he0
  have hq : -C*A+(1-rho)*C*e-(29/100)*e^2+(17/200)*e ≤ Objective rho C A A := by
    dsimp only [Objective]
    nlinarith only [hce,hca,haa,hscaled,hAsq,hAe,heSq]
  exact hq.trans (objective_le_main (by linarith only [hrho] : 0<rho) le_rfl)

theorem actual_resource_frontier_hybrid {rho : ℝ} {N H C A M e : ℕ}
    (hrho : 200/329≤rho) (hrho1 : rho≤1) (hN : 1≤N) (hH : 4000≤H)
    (hHarm : Harmonic N≤19) (hscale : 25*(C+A)≤18*H)
    (hAe : A≤e) (heM : e≤M) (heN : e≤N)
    (hF : rho*C-17/200≤TotientRows208.TotientMass C)
    (hU : e≤H → rho*(e : ℝ)^2/2-(61/200)*e≤TotientTriangle e) :
    (MiddleJoint51.ResourceCount C A M e : ℝ) ≤
      (coprimeRectangle C M).card+(TotientTriangle M : ℝ)+FrontierMain rho C A+
      (39/100 : ℝ)*max (A : ℝ) ((1/rho-1)*C)+(39/100 : ℝ)^2/(2*rho)+
      (C : ℝ)/2*Real.log C := by
  have hr0 : 0<rho := by linarith only [hrho]
  by_cases heH : e≤H
  · exact LocalizedMiddle208.actual_resource_frontier_bound hr0 hAe heM hF (hU heH)
  · have hUlarge := actual_large_triangle hN (by omega : 4000≤e) heN hHarm
    have hP := TotientRows208.rectangle_local_lower (e:=e) hF
    have hscR : 25*((C : ℝ)+A)≤18*(e : ℝ) := by
      exact_mod_cast (show 25*(C+A)≤18*e by omega)
    have hq := coarse_frontier_le_main (by linarith only [hrho] : 3/5≤rho) hrho1
      (Nat.cast_nonneg C) (Nat.cast_nonneg A) (by exact_mod_cast (show 43≤e by omega)) hscR
    have hv : 0≤max (A : ℝ) ((1/rho-1)*C) := (Nat.cast_nonneg A).trans (le_max_left _ _)
    have hanchor : 0≤(39/100 : ℝ)*max (A : ℝ) ((1/rho-1)*C) := by positivity
    have hquad : 0≤(39/100 : ℝ)^2/(2*rho) := by positivity
    rw [resource_frontier_identity hAe heM]
    nlinarith only [hP,hUlarge,hq,hanchor,hquad]

#print axioms actual_triangle_coarse
#print axioms actual_large_triangle
#print axioms coarse_frontier_le_main
#print axioms actual_resource_frontier_hybrid
end
end JSP233.FiniteFrontier209
