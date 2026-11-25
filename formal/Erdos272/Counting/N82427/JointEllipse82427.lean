module

public import Erdos272.Resources.Recovery208

@[expose] public section

namespace JSP233.JointEllipse82427
open Recovery208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Parameters where
  A : ℝ
  B : ℝ
  W : ℝ
  C : ℝ
  rho : ℝ
  tau : ℝ
  multiplier : ℝ

def U (p : Parameters) : ℝ := p.multiplier*(114959/80000)+1
def V (p : Parameters) : ℝ := -p.multiplier*(329/400)
def Z (p : Parameters) : ℝ := p.multiplier/2-1/4
def Determinant (p : Parameters) : ℝ := U p*Z p-(V p)^2
def X (p : Parameters) (n : ℝ) : ℝ := n+1+p.multiplier*p.B
def Y (p : Parameters) : ℝ := 1+p.multiplier*p.W
def Fraction (p : Parameters) (n : ℝ) : ℝ :=
  (Z p*(X p n)^2-2*V p*X p n*Y p+U p*(Y p)^2)/(4*Determinant p)
def Upper (p : Parameters) (n : ℝ) : ℝ := p.multiplier*(p.A*n+p.C)+Fraction p n
def DensityDelta (p : Parameters) : ℝ := 271/800-p.tau+p.tau^2/2
def Gap (p : Parameters) (h n : ℝ) : ℝ :=
  DensityDelta p*n^2-(h-1/2+p.rho)*n-Upper p n
def Leading (p : Parameters) : ℝ := DensityDelta p-Z p/(4*Determinant p)
def Linear (p : Parameters) (h : ℝ) : ℝ := h-1/2+p.rho+p.multiplier*p.A+
  (2*Z p*X p 0-2*V p*Y p)/(4*Determinant p)

theorem square_identity (p : Parameters) (hD : Determinant p ≠ 0) (n L w : ℝ) :
    4*U p*Determinant p*(Fraction p n+U p*L^2+2*V p*L*w+Z p*w^2-X p n*L-Y p*w)=
      Determinant p*(2*U p*L+2*V p*w-X p n)^2+
        (2*Determinant p*w-(U p*Y p-V p*X p n))^2 := by
  unfold Fraction
  field_simp [hD]
  unfold Determinant
  ring

theorem loss_bound (p : Parameters) (hlambda : 0≤p.multiplier)
    (hU : 0<U p) (hD : 0<Determinant p) {n L w : ℝ}
    (hp : WidthProfile L w≤p.A*n+p.B*L+p.W*w+p.C) :
    L*(n-L)+w^2/4+L+w≤Upper p n := by
  have hs := square_identity p hD.ne' n L w
  have hnon := mul_nonneg hD.le (sq_nonneg (2*U p*L+2*V p*w-X p n))
  have hsq := sq_nonneg (2*Determinant p*w-(U p*Y p-V p*X p n))
  have hscale : 0<4*U p*Determinant p := by positivity
  have hmul : 0≤(4*U p*Determinant p)*
      (Fraction p n+U p*L^2+2*V p*L*w+Z p*w^2-X p n*L-Y p*w) := by
    linarith only [hs, hnon, hsq]
  have hf := nonneg_of_mul_nonneg_right hmul hscale
  have hpaid := mul_le_mul_of_nonneg_left hp hlambda
  dsimp only [WidthProfile] at hpaid
  dsimp only [Upper, U, V, Z, X, Y] at hf ⊢
  nlinarith only [hf, hpaid]

def Certificate (p : Parameters) (h n0 : ℝ) : Prop :=
  0≤p.multiplier ∧ 0<U p ∧ 0<Determinant p ∧ 0≤Leading p ∧
    0<Gap p h n0 ∧ 0≤2*Leading p*n0-Linear p h

theorem gap_expansion (p : Parameters) (h n0 n : ℝ) :
    Gap p h n=Gap p h n0+Leading p*(n-n0)^2+
      (2*Leading p*n0-Linear p h)*(n-n0) := by
  dsimp only [Gap, Upper, Fraction, Leading, Linear, X, Y]
  ring

theorem gap_positive (p : Parameters) {h n0 n : ℝ}
    (hc : Certificate p h n0) (hn : n0≤n) : 0<Gap p h n := by
  have hq := mul_nonneg hc.2.2.2.1 (sq_nonneg (n-n0))
  have hl := mul_nonneg hc.2.2.2.2.2 (sub_nonneg.mpr hn)
  rw [gap_expansion p h n0 n]
  linarith only [hc.2.2.2.2.1, hq, hl]

#print axioms square_identity
#print axioms loss_bound
#print axioms gap_expansion
#print axioms gap_positive
end
end JSP233.JointEllipse82427
