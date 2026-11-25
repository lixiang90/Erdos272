module

public import Erdos272.Retention.N86412.RecoveryCertificates86412

@[expose] public section

namespace JSP233.JointEllipse86412
open LocalRecovery86412 RecoveryCertificates86412 Recovery208
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def Multiplier (k : ℕ) : ℝ := 100
def U (k : ℕ) : ℝ := Multiplier k*(114959/80000)+1
def V (k : ℕ) : ℝ := -Multiplier k*(329/400)
def Z (k : ℕ) : ℝ := Multiplier k/2-1/4
def Determinant (k : ℕ) : ℝ := U k*Z k-(V k)^2
def X (k : ℕ) (n : ℝ) : ℝ := n+1+Multiplier k*BLocal k 16
def Y (k : ℕ) : ℝ := 1+Multiplier k*HLocal k
def Fraction (k : ℕ) (n : ℝ) : ℝ :=
  (Z k*(X k n)^2-2*V k*X k n*Y k+U k*(Y k)^2)/(4*Determinant k)
def Upper (k : ℕ) (n : ℝ) : ℝ := Multiplier k*(StrongA k*n+872)+Fraction k n
def Gap (k : ℕ) (n : ℝ) : ℝ :=
  (439/7200 : ℝ)*n^2-(HLocal k-1/2+25/4)*n-Upper k n
def Leading (k : ℕ) : ℝ := 439/7200-Z k/(4*Determinant k)
def Linear (k : ℕ) : ℝ := HLocal k-1/2+25/4+Multiplier k*StrongA k+
  (2*Z k*X k 0-2*V k*Y k)/(4*Determinant k)

theorem square_identity (k : ℕ) (hk : k<1) (n L w : ℝ) :
    4*U k*Determinant k*(Fraction k n+U k*L^2+2*V k*L*w+Z k*w^2-X k n*L-Y k*w) =
      Determinant k*(2*U k*L+2*V k*w-X k n)^2+
        (2*Determinant k*w-(U k*Y k-V k*X k n))^2 := by
  interval_cases k <;> norm_num [Fraction, U, V, Z, Determinant, Multiplier] <;> ring

theorem loss_bound {k : ℕ} (hk : k<1) {n L w : ℝ}
    (hp : WidthProfile L w ≤ StrongA k*n+BLocal k 16*L+HLocal k*w+872) :
    L*(n-L)+w^2/4+L+w ≤ Upper k n := by
  have hs := square_identity k hk n L w
  have hnon := mul_nonneg
    (show (0 : ℝ) ≤ Determinant k by interval_cases k <;> norm_num [Determinant, U, V, Z, Multiplier])
    (sq_nonneg (2*U k*L+2*V k*w-X k n))
  have hsq := sq_nonneg (2*Determinant k*w-(U k*Y k-V k*X k n))
  have hscale : (0 : ℝ) < 4*U k*Determinant k := by
    interval_cases k <;> norm_num [U, V, Z, Determinant, Multiplier]
  have hf : 0 ≤ Fraction k n+U k*L^2+2*V k*L*w+Z k*w^2-X k n*L-Y k*w := by
    nlinarith only [hs, hnon, hsq, hscale]
  dsimp only [WidthProfile] at hp
  dsimp only [Upper, U, V, Z, X, Y] at hf ⊢
  interval_cases k <;> norm_num [Multiplier] at hf hp ⊢ <;>
    nlinarith only [hf, hp]

theorem gap_expansion (k : ℕ) (hk : k<1) (n : ℝ) :
    Gap k n = Gap k (Low k)+Leading k*(n-Low k)^2+
      (2*Leading k*(Low k)-Linear k)*(n-Low k) := by
  interval_cases k <;>
    norm_num [Gap, Upper, Fraction, X, Y, U, V, Z, Determinant, Leading, Linear, Multiplier,
      StrongA, HLocal, BLocal, LogLocal, Low, RecoveryParameters291012.Lower,
      CovarianceScalar213.Polynomial] <;> ring

theorem gap_positive {k : ℕ} (hk : k<1) {n : ℝ} (hn : (Low k : ℝ) ≤ n) :
    0 < Gap k n := by
  have hb : 0 < Gap k (Low k) := by
    interval_cases k <;>
      norm_num [Gap, Upper, Fraction, X, Y, U, V, Z, Determinant, Multiplier, StrongA,
        HLocal, BLocal, LogLocal, Low, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial]
  have hquadratic := mul_nonneg
    (show (0 : ℝ) ≤ Leading k by interval_cases k <;>
      norm_num [Leading, Z, U, V, Determinant, Multiplier])
    (sq_nonneg (n-Low k))
  have hlinear := mul_nonneg
    (show (0 : ℝ) ≤ 2*Leading k*(Low k)-Linear k by
      interval_cases k <;>
        norm_num [Leading, Linear, X, Y, U, V, Z, Determinant, Multiplier, StrongA, HLocal,
          BLocal, LogLocal, Low, RecoveryParameters291012.Lower, CovarianceScalar213.Polynomial])
    (sub_nonneg.mpr hn)
  rw [gap_expansion k hk]
  linarith only [hb, hquadratic, hlinear]

#print axioms square_identity
#print axioms loss_bound
#print axioms gap_expansion
#print axioms gap_positive
end
end JSP233.JointEllipse86412
