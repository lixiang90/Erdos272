import Erdos272.Arithmetic.UniformMoment208
import Erdos272.Resources.APResidual208
import Erdos272.Resources.NeighborJoint208

/-! The analytic uniform source is supplied by the same actual intrinsic pool. -/
namespace JSP233.UniformActual208
open StarCompletion SourceBridge208 IntrinsicTriples208 UniformSourceCore208
open UniformAbel208 UniformMoment208 StepWeightShape208 NeighborMass208 NeighborJoint208
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0

theorem actual_Jstar {S : Finset ℤ} {e : ℝ} (hs : 31≤S.card)
    (he : 0≤e) (hecap : e≤4*(S.card : ℝ)/5)
    (heDefect : e≤(Defect S : ℝ))
    (hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ))
    (hW : (SigmaPrefix209.W S.card : ℝ)≤UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
      (S.card : ℝ)^2/4+14/5*S.card) :
    Jstar S.card e≤(Pool S).card := by
  have hdef : (Defect S : ℝ)=(S.card : ℝ)-(MaxAPSize S : ℝ) := by
    exact Nat.cast_sub (maxAPSize_le_card S)
  have hm0 : (MaxAPSize S : ℝ)≤(S.card : ℝ)-e := by linarith only [hdef,heDefect]
  have hp := real_prefix_bound hs hm0 (by linarith only [hecap])
    (by linarith only [he] : (S.card : ℝ)-e≤S.card) hW
  have ha := actual_intrinsic_frontier (by omega : 2≤S.card) Delta (579/1000) hF
  have hp' := mul_le_mul_of_nonneg_left hp (by norm_num [Delta] : 0≤Delta)
  rw [physical_weight_one,APResidual208.cast_choose_three] at ha
  change _≤_ at hp'
  unfold Jstar Delta at *
  dsimp only [PrefixW] at hp'
  have hsize : (0 : ℝ)≤S.card := by positivity
  nlinarith only [hp',ha,hsize]

def P (y z M : ℝ) : ℝ := Q y z (7*M/25)+160/M*Jstar y z

theorem actual_analytic_joint {N : ℕ} {S : Finset ℤ} {v M e : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 31≤S.card)
    (hv : 0<v) (hM : 0<M) (he : 0≤e) (hecap : e≤4*(S.card : ℝ)/5)
    (heDefect : e≤(Defect S : ℝ))
    (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25)
    (hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ))
    (hW : (SigmaPrefix209.W S.card : ℝ)≤UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
      (S.card : ℝ)^2/4+14/5*S.card) :
    Q S.card e (7*v*M/25)+160/(v*M)*Jstar S.card e ≤
      UniformCapacity208.JointMass N v M S := by
  have hq := (Q_mono_defect heDefect hfirst).trans
    (actual_Q_mass hN hS (by omega : 4≤S.card) (by positivity : 0≤7*v*M/25))
  have hj := mul_le_mul_of_nonneg_left (actual_Jstar hs he hecap heDefect hF hW)
    (by positivity : 0≤160/(v*M))
  exact add_le_add hq hj

#print axioms actual_Jstar
#print axioms actual_analytic_joint
end
end JSP233.UniformActual208
