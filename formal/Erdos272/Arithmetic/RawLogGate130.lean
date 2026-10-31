import Erdos272.Arithmetic.DirectGate130
import Erdos272.Resources.CoarseEndpoint130
namespace JSP233.RawLogGate130
open StarCompletion RawEndpoint112
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 20000

theorem raw_restore_gate_real {n : ℝ} (hn : 107277000≤n) :
    (900/23:ℝ)^2*(n*RawEndpoint130.BootstrapPolynomial (Real.log n))≤n^2 := by
  have hg := DirectGate130.fine_gate_real hn
  have hp := mul_le_mul_of_nonneg_left hg (show (0:ℝ)≤n by linarith only [hn])
  dsimp only [RawEndpoint130.BootstrapPolynomial,RawEndpoint130.BootstrapCorePolynomial,
    DirectGate130.Rho,DirectGate130.P,DirectMoment130.P] at hp ⊢
  nlinarith only [hp]

theorem coarse_gate_real {n : ℝ} (hn : 107277000≤n) :
    (32:ℝ)^2*(n*CoarseEndpoint130.CoarsePolynomial (Real.log n))≤n^2 := by
  have hg := DirectGate130.coarse_gate_real hn
  have hp := mul_le_mul_of_nonneg_left hg (show (0:ℝ)≤n by linarith only [hn])
  dsimp only [CoarseEndpoint130.CoarsePolynomial,CoarseEndpoint130.CoarseCorePolynomial,
    RawEndpoint130.BootstrapCorePolynomial,DirectGate130.Rho,DirectGate130.Pc,
    DirectGate130.P,DirectMoment130.P] at hp ⊢
  nlinarith only [hp]

theorem actual_preliminary_width_payment {N w : ℕ} (hN : 107277000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*CoarseEndpoint130.CoarsePolynomial (Real.log N)) : 32*w≤N := by
  have hg := coarse_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(32:ℝ)^2)
  have hs : ((32:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hg]
  have hl : (32:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  exact_mod_cast hl

theorem actual_balanced_width_payment {N w : ℕ} (hN : 107277000≤N)
    (hwidth : (w:ℝ)^2≤(N:ℝ)*RawEndpoint130.BootstrapPolynomial (Real.log N)) : 900*w≤23*N := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hm := mul_le_mul_of_nonneg_left hwidth (by norm_num : (0:ℝ)≤(900/23:ℝ)^2)
  have hs : ((900/23:ℝ)*(w:ℝ))^2≤(N:ℝ)^2 := by nlinarith only [hm,hg]
  have hl : (900/23:ℝ)*(w:ℝ)≤(N:ℝ) :=
    (sq_le_sq₀ (by positivity) (Nat.cast_nonneg N)).mp hs
  have hh : (900:ℝ)*w≤23*(N:ℝ) := by linarith only [hl]
  exact_mod_cast hh

theorem actual_bootstrap_profile_payment {N : ℕ} {D : ℝ} (hN : 107277000≤N)
    (hprofile : D≤(N:ℝ)*RawEndpoint130.BootstrapCorePolynomial (Real.log N)) :
    810000*D≤529*DeficitCoeff*(N:ℝ)^2 := by
  have hg := raw_restore_gate_real (n:=(N:ℝ)) (by exact_mod_cast hN)
  have hc : 810000*((N:ℝ)*RawEndpoint130.BootstrapCorePolynomial (Real.log N))≤
      529*DeficitCoeff*(N:ℝ)^2 := by
    dsimp only [RawEndpoint130.BootstrapPolynomial,DeficitCoeff] at hg ⊢
    nlinarith only [hg]
  exact (mul_le_mul_of_nonneg_left hprofile (by norm_num : (0:ℝ)≤810000)).trans hc
#print axioms raw_restore_gate_real
#print axioms coarse_gate_real
#print axioms actual_preliminary_width_payment
#print axioms actual_balanced_width_payment
#print axioms actual_bootstrap_profile_payment
end
end JSP233.RawLogGate130
