module

public import Erdos272.Retention.N109474.RecoveryCertificates109474

@[expose] public section

namespace JSP233.JointEllipse109474
open LocalRecovery118533 RecoveryCertificates109474 Recovery208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def U : ℝ := 3123893/20000
def V : ℝ := -8883/100
def Z : ℝ := 215/4
def Determinant : ℝ := 40375483/80000
def X (n : ℝ) : ℝ := n+1+108*BLocal 16
def Y : ℝ := 1+108*HLocal
def Fraction (n : ℝ) : ℝ :=
  (Z*(X n)^2-2*V*X n*Y+U*Y^2)/(4*Determinant)
def Upper (n : ℝ) : ℝ := 108*(StrongA*n+872)+Fraction n
def Gap (n : ℝ) : ℝ := (439/7200 : ℝ)*n^2-(HLocal-1/2+19/2)*n-Upper n
def Leading : ℝ := 9984837037/290703477600
def Linear : ℝ :=
  HLocal-1/2+19/2+108*StrongA+(2*Z*X 0-2*V*Y)/(4*Determinant)

theorem square_identity (n L w : ℝ) :
    4*U*Determinant*(Fraction n+U*L^2+2*V*L*w+Z*w^2-X n*L-Y*w) =
      Determinant*(2*U*L+2*V*w-X n)^2+(2*Determinant*w-(U*Y-V*X n))^2 := by
  norm_num [Fraction, U, V, Z, Determinant]
  ring

theorem loss_bound {n L w : ℝ}
    (hp : WidthProfile L w ≤ StrongA*n+BLocal 16*L+HLocal*w+872) :
    L*(n-L)+w^2/4+L+w ≤ Upper n := by
  have hs := square_identity n L w
  have hnon := mul_nonneg (show (0 : ℝ) ≤ Determinant by norm_num [Determinant])
    (sq_nonneg (2*U*L+2*V*w-X n))
  have hsq := sq_nonneg (2*Determinant*w-(U*Y-V*X n))
  have hscale : (0 : ℝ) < 4*U*Determinant := by norm_num [U, Determinant]
  have hf : 0 ≤ Fraction n+U*L^2+2*V*L*w+Z*w^2-X n*L-Y*w := by
    nlinarith only [hs, hnon, hsq, hscale]
  dsimp only [WidthProfile] at hp
  dsimp only [Upper, U, V, Z, X, Y] at hf ⊢
  nlinarith only [hf, hp]

theorem gap_expansion (n : ℝ) :
    Gap n = Gap 109474+Leading*(n-109474)^2+
      (2*Leading*109474-Linear)*(n-109474) := by
  norm_num [Gap, Upper, Fraction, X, Y, U, V, Z, Determinant, Leading, Linear,
    StrongA, HLocal, BLocal, LogLocal, RecoveryParameters291012.Lower,
    CovarianceScalar213.Polynomial]
  ring

theorem gap_positive {n : ℝ} (hn : 109474 ≤ n) : 0 < Gap n := by
  have hb : 0 < Gap 109474 := by
    norm_num [Gap, Upper, Fraction, X, Y, U, V, Z, Determinant, StrongA,
      HLocal, BLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]
  have hquadratic := mul_nonneg (show (0 : ℝ) ≤ Leading by norm_num [Leading])
    (sq_nonneg (n-109474))
  have hlinear := mul_nonneg (show (0 : ℝ) ≤ 2*Leading*109474-Linear by
    norm_num [Leading, Linear, X, Y, U, V, Z, Determinant, StrongA, HLocal,
      BLocal, LogLocal, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial])
    (sub_nonneg.mpr hn)
  rw [gap_expansion]
  linarith only [hb, hquadratic, hlinear]

#print axioms square_identity
#print axioms loss_bound
#print axioms gap_expansion
#print axioms gap_positive
end
end JSP233.JointEllipse109474
