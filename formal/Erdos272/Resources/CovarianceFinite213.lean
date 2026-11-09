module

public import Erdos272.Arithmetic.CovarianceScalar213
public import Erdos272.Resources.TotientCovariance212
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

/-! Finite covariance moments.  F bounds are genuine bounds on TotientMass,
and the only reciprocal-square estimate used is the finite 1,670,000 bound. -/
namespace JSP233.CovarianceFinite213
open CoprimeDensity52 HarmonicAbel29 TotientRows208 FrontierDensity208
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def Epsilon : ℝ := 73/1000000
def Theta (c d : ℕ) : ℝ := (c : ℝ)/d-(c/d : ℕ)
def Zeta (c d : ℕ) : ℝ :=
  61/200-(TotientMass (c/d)-Rho*(c/d : ℕ))-(1-Rho)*Theta c d

theorem theta_bounds (c : ℕ) {d : ℕ} (hd : 0<d) :
    0≤Theta c d ∧ Theta c d≤1 := by
  have hh:=TotientFloor29.nat_div_bounds c d hd
  dsimp only [Theta]
  constructor <;> linarith only [hh.1,hh.2]

theorem zeta_identity (c d : ℕ) :
    Zeta c d=61/200-TotientMass (c/d)+Rho*((c : ℝ)/d)-Theta c d := by
  dsimp only [Zeta,Theta]
  ring

theorem centred_row_identity (c d : ℕ) :
    (c/d : ℕ)-TotientMass (c/d)+(61/200 : ℝ)=
      (1-Rho)*(c : ℝ)/d+Zeta c d := by
  dsimp only [Zeta,Theta]
  ring

theorem weighted_zeta {c : ℕ} (hhigh : c≤1670000) :
    (∑d∈Finset.Icc 1 c,Zeta c d/(d : ℝ))≤(61/200)*Harmonic c := by
  have ht : ∀d∈Finset.Icc 1 c,Zeta c d/(d : ℝ)≤
      (61/200)/(d : ℝ)-TotientMass (c/d)/(d : ℝ)+
        Rho*c*((d : ℝ)^2)⁻¹ := by
    intro d hd
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hh:=(theta_bounds c (show 0<d by have h:=Finset.mem_Icc.mp hd;omega)).1
    have hm:=div_nonneg hh hd0.le
    rw [zeta_identity]
    have he : ((61/200-TotientMass (c/d)+Rho*((c : ℝ)/d)-Theta c d)/(d : ℝ))=
        (61/200)/(d : ℝ)-TotientMass (c/d)/(d : ℝ)+
          Rho*c*((d : ℝ)^2)⁻¹-Theta c d/d := by
      field_simp
    rw [he]
    linarith only [hm]
  have hZ:=actual_square_upper hhigh
  have hm:=mul_le_mul_of_nonneg_left hZ
    (show (0 : ℝ)≤Rho*c by exact mul_nonneg CovarianceScalar213.rho_pos.le (Nat.cast_nonneg c))
  have hrho0:=CovarianceScalar213.rho_pos
  have he : Rho*(c : ℝ)*(1/Rho)=(c : ℝ) := by field_simp
  rw [he] at hm
  have hb : (∑d∈Finset.Icc 1 c,(61/200 : ℝ)/(d : ℝ))=(61/200)*Harmonic c := by
    simp only [Harmonic,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  -- Keep the constant-over-d sum in harmonic form.
  have hs' : (∑d∈Finset.Icc 1 c,Zeta c d/(d : ℝ))≤
      (61/200)*Harmonic c-c+Rho*c*reciprocalSquareSum c := by
    calc
      _≤∑d∈Finset.Icc 1 c,
          ((61/200)/(d : ℝ)-TotientMass (c/d)/(d : ℝ)+Rho*c*((d : ℝ)^2)⁻¹) :=
        Finset.sum_le_sum ht
      _=_ := by rw [Finset.sum_add_distrib,Finset.sum_sub_distrib,hb,
        TotientCovariance212.mass_convolution,←Finset.mul_sum];rfl
  linarith only [hs',hm]

theorem zeta_abs {N c d : ℕ} (hcN : c≤N) (hd : 0<d)
    (hF : ∀t≤N,Rho*t-17/200≤TotientMass t)
    (hFu : ∀t≤N,TotientMass t≤(76/125 : ℝ)*t+579/1000) :
    |Zeta c d|≤2/3+Epsilon*((c : ℝ)/d) := by
  have hfloor : c/d≤N := (Nat.div_le_self _ _).trans hcN
  have hfl:=hF (c/d) hfloor
  have hfu:=hFu (c/d) hfloor
  have hth:=theta_bounds c hd
  have hC : (0 : ℝ)≤(c/d : ℕ) := Nat.cast_nonneg _
  have hdiv : (0 : ℝ)≤(c : ℝ)/d := by positivity
  have hd0 : (0 : ℝ)<d := by exact_mod_cast hd
  have hCD:=Nat.cast_div_le (α := ℝ) (m:=c) (n:=d)
  have hr : (0 : ℝ)≤1-Rho := by norm_num [Rho]
  have ht0:=mul_nonneg hr hth.1
  have ht1:=mul_le_mul_of_nonneg_left hth.2 hr
  have heps : (0 : ℝ)≤Epsilon := by norm_num [Epsilon]
  have hm:=mul_le_mul_of_nonneg_left hCD heps
  have herr : (76/125 : ℝ)-Rho≤Epsilon := by norm_num [Rho,Epsilon]
  have herrC:=mul_le_mul_of_nonneg_right herr hC
  have hlo : - (2/3+Epsilon*((c : ℝ)/d))≤Zeta c d := by
    dsimp only [Zeta]
    norm_num only [Rho] at *
    nlinarith only [hfu,ht1,herrC,hm]
  have hhi : Zeta c d≤2/3+Epsilon*((c : ℝ)/d) := by
    have hnon:=mul_nonneg heps hdiv
    dsimp only [Zeta]
    nlinarith only [hfl,ht0,hnon]
  exact abs_le.mpr ⟨hlo,hhi⟩

theorem harmonic_small {c : ℕ} (hc : 1≤c) (hhigh : c≤1670000) :
    Harmonic c≤22 := by
  have hc0 : (0 : ℝ)<c := by exact_mod_cast (show 0<c by omega)
  have hcp : (c : ℝ)≤(2 : ℝ)^21 := by
    have hh : (c : ℝ)≤1670000 := by exact_mod_cast hhigh
    norm_num at *
    linarith only [hh]
  have hl:=Real.log_le_log hc0 hcp
  rw [Real.log_pow] at hl
  have htwo:=HarmonicLog55.actual_log_two_upper
  have hH:=HarmonicAbel29.harmonic_le_one_add_log c
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl,htwo,hH]

theorem square_zeta {N c : ℕ} (hc : 1≤c) (hcN : c≤N) (hhigh : c≤1670000)
    (hF : ∀t≤N,Rho*t-17/200≤TotientMass t)
    (hFu : ∀t≤N,TotientMass t≤(76/125 : ℝ)*t+579/1000) :
    (∑d∈Finset.Icc 1 c,(Zeta c d)^2/(2*Rho))≤(19/50)*(c : ℝ) := by
  have ht : ∀d∈Finset.Icc 1 c,(Zeta c d)^2≤
      (4/9 : ℝ)+(4/3)*Epsilon*c*(1/(d : ℝ))+Epsilon^2*c^2*((d : ℝ)^2)⁻¹ := by
    intro d hd
    have hd0 : 0<d := by have hh:=Finset.mem_Icc.mp hd;omega
    have ha:=zeta_abs hcN hd0 hF hFu
    have hB : (0 : ℝ)≤2/3+Epsilon*((c : ℝ)/d) := by dsimp only [Epsilon];positivity
    have hh:=(sq_le_sq₀ (abs_nonneg (Zeta c d)) hB).mpr ha
    rw [sq_abs] at hh
    calc
      _≤(2/3+Epsilon*((c : ℝ)/d))^2 := hh
      _=_ := by field_simp;ring
  have hs:=Finset.sum_le_sum ht
  have he : (∑d∈Finset.Icc 1 c,
      ((4/9 : ℝ)+(4/3)*Epsilon*c*(1/(d : ℝ))+Epsilon^2*c^2*((d : ℝ)^2)⁻¹))=
      (4/9)*(c : ℝ)+(4/3)*Epsilon*c*Harmonic c+
        Epsilon^2*c^2*reciprocalSquareSum c := by
    simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
      Nat.card_Icc,Nat.add_sub_cancel,nsmul_eq_mul,Harmonic,reciprocalSquareSum]
    ring
  rw [he] at hs
  have hH:=harmonic_small hc hhigh
  have hZ:=actual_square_upper hhigh
  have hHm:=mul_le_mul_of_nonneg_left hH
    (show (0 : ℝ)≤(4/3)*Epsilon*c by dsimp only [Epsilon];positivity)
  have hZm:=mul_le_mul_of_nonneg_left hZ
    (show (0 : ℝ)≤Epsilon^2*c^2 by positivity)
  have hcR : (c : ℝ)≤1670000 := by exact_mod_cast hhigh
  have hcc:=mul_le_mul_of_nonneg_right hcR (Nat.cast_nonneg (α:=ℝ) c)
  have hs' : (∑d∈Finset.Icc 1 c,(Zeta c d)^2)≤(19/50)*(c : ℝ)*(2*Rho) := by
    dsimp only [Rho,Epsilon] at hs hHm hZm ⊢
    nlinarith only [hs,hHm,hZm,hcc,Nat.cast_nonneg (α:=ℝ) c]
  rw [←Finset.sum_div]
  exact (div_le_iff₀ (by exact mul_pos (by norm_num) CovarianceScalar213.rho_pos)).mpr hs'

theorem row_error_sum {c : ℕ} (hc : 1≤c) :
    (∑d∈Finset.Icc 1 c,RowError (c/d))≤
      (c : ℝ)*((Real.log c)^2/4+Real.log c/2) := by
  have ht : ∀d∈Finset.Icc 1 c,RowError (c/d)≤
      ((c : ℝ)/(2*d))*Real.log ((c : ℝ)/d) := by
    intro d hd
    exact (row_error_log (c/d)).trans (FrontierSum208.row_error_physical le_rfl hd)
  have hs:=Finset.sum_le_sum ht
  have he : (∑d∈Finset.Icc 1 c,((c : ℝ)/(2*d))*Real.log ((c : ℝ)/d))=
      ((c : ℝ)/2)*(∑d∈Finset.Icc 1 c,SimplexMoment57.LogKernel c 1 d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    have hd0 : (0 : ℝ)<d := by exact_mod_cast (Finset.mem_Icc.mp hd).1
    have hc0 : (0 : ℝ)<c := by exact_mod_cast (show 0<c by omega)
    dsimp only [SimplexMoment57.LogKernel]
    rw [Real.log_div hc0.ne' hd0.ne']
    norm_num only [pow_one]
    ring
  rw [he] at hs
  have hk:=SimplexMoment57.actual_log_kernel_sum hc 1
  norm_num only [pow_one,Nat.reduceAdd,Nat.cast_ofNat] at hk
  have hm:=mul_le_mul_of_nonneg_left hk
    (show (0 : ℝ)≤(c : ℝ)/2 by positivity)
  nlinarith only [hs,hm]

#print axioms weighted_zeta
#print axioms zeta_abs
#print axioms square_zeta
#print axioms row_error_sum
end
end JSP233.CovarianceFinite213
