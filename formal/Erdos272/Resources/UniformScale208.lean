import Erdos272.Resources.UniformActual208

/-! The actual mixed source scales by v², hence its global fee scales by v⁻³. -/
namespace JSP233.UniformScale208
open StarCompletion SourceBridge208 UniformSourceCore208 UniformActual208 NeighborMass208
open UniformAbel208 IntrinsicTriples208
noncomputable section
set_option maxHeartbeats 0

theorem max_scale_loss {v c : ℝ} (hv : 1≤v) (hc : 0≤c) (A : ℝ) :
    v*max (A-c) 0≤max (v*A-c) 0 := by
  rw [mul_max_of_nonneg _ _ (by linarith only [hv] : 0≤v),mul_zero]
  apply max_le_max _ le_rfl
  nlinarith only [mul_nonneg (by linarith only [hv] : 0≤v-1) hc]

theorem Q_scale {v y z t : ℝ} (hv : 1≤v) (hz : 0≤z) :
    v^2*Q y z t≤Q (v*y) (v*z) (v*t) := by
  have hv0 : 0≤v := by linarith only [hv]
  have hfirst : v^2*(z*(y-1-t))≤(v*z)*(v*y-1-v*t) := by
    have hh := mul_nonneg (mul_nonneg hv0 hz) (by linarith only [hv] : 0≤v-1)
    nlinarith only [hh]
  have h2 := mul_le_mul
    (max_scale_loss hv (by norm_num : (0 : ℝ)≤1) (3*z-y))
    (max_scale_loss hv (by norm_num : (0 : ℝ)≤2) (y-2*t))
    (by positivity : 0≤v*max (y-2*t-2) 0) (le_max_right _ _)
  have h3 := mul_le_mul
    (max_scale_loss hv (by norm_num : (0 : ℝ)≤2) (5*z-2*y))
    (max_scale_loss hv (by norm_num : (0 : ℝ)≤3) (y-3*t))
    (by positivity : 0≤v*max (y-3*t-3) 0) (le_max_right _ _)
  have he2a : 3*(v*z)-v*y-1=v*(3*z-y)-1 := by ring
  have he2b : v*y-2-2*(v*t)=v*(y-2*t)-2 := by ring
  have he3a : 5*(v*z)-2*(v*y)-2=v*(5*z-2*y)-2 := by ring
  have he3b : v*y-3-3*(v*t)=v*(y-3*t)-3 := by ring
  have he2c : y-2-2*t=y-2*t-2 := by ring
  have he3c : y-3-3*t=y-3*t-3 := by ring
  unfold Q
  rw [he2a,he2b,he3a,he3b,he2c,he3c]
  nlinarith only [hfirst,h2,h3]

theorem P_scale {v y z M : ℝ} (hv : 1≤v) (hy : 0≤y) (hz : 0≤z)
    (hzy : z≤4*y/5) (hM : 0<M) :
    v^2*P y z M≤Q (v*y) (v*z) (7*v*M/25)+160/(v*M)*Jstar (v*y) (v*z) := by
  have hv0 : 0<v := by linarith only [hv]
  have hq := Q_scale (y := y) (t := 7*M/25) hv hz
  have hj := mul_le_mul_of_nonneg_left (Jstar_scale hv hy hz hzy)
    (by positivity : 0≤160/(v*M))
  have he : 160/(v*M)*(v^3*Jstar y z)=v^2*(160/M*Jstar y z) := by field_simp
  rw [he] at hj
  have het : v*(7*M/25)=7*v*M/25 := by ring
  rw [het] at hq
  unfold P
  nlinarith only [hq,hj]

theorem actual_scaled_P {N : ℕ} {S : Finset ℤ} {v M y z : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 31≤S.card)
    (hv : 1≤v) (hM : 0<M) (hy : 0≤y) (hz : 0≤z) (hzy : z≤4*y/5)
    (hsize : (S.card : ℝ)=v*y) (hdef : v*z≤(Defect S : ℝ))
    (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25)
    (hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ))
    (hW : (SigmaPrefix209.W S.card : ℝ)≤UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
      (S.card : ℝ)^2/4+14/5*S.card) :
    v^2*P y z M≤UniformCapacity208.JointMass N v M S := by
  have hv0 : 0<v := by linarith only [hv]
  have hecap : v*z≤4*(S.card : ℝ)/5 := by rw [hsize]; nlinarith only [mul_le_mul_of_nonneg_left hzy hv0.le]
  have hj := actual_analytic_joint hN hS hs hv0 hM (by positivity : 0≤v*z) hecap hdef hfirst hF hW
  rw [hsize] at hj
  exact (P_scale hv hy hz hzy hM).trans hj

def Baseline (y z M : ℝ) : ℝ := z*(y-1-7*M/25)

theorem actual_scaled_baseline {N : ℕ} {S : Finset ℤ} {v M y z : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 4≤S.card)
    (hv : 1≤v) (hM : 0<M) (hz : 0≤z)
    (hsize : (S.card : ℝ)=v*y) (hdef : v*z≤(Defect S : ℝ))
    (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25) :
    v^2*Baseline y z M≤UniformCapacity208.JointMass N v M S := by
  have hv0 : 0<v := by linarith only [hv]
  have hb : Baseline y z M≤Q y z (7*M/25) := by
    unfold Baseline Q
    have h2 : 0≤max (3*z-y-1) 0/2*max (y-2-2*(7*M/25)) 0 := by positivity
    have h3 : 0≤max (5*z-2*y-2) 0/3*max (y-3-3*(7*M/25)) 0 := by positivity
    linarith only [h2,h3]
  have hq := (mul_le_mul_of_nonneg_left hb (sq_nonneg v)).trans (Q_scale hv hz)
  have het : v*(7*M/25)=7*v*M/25 := by ring
  rw [het,← hsize] at hq
  have ha := (NeighborJoint208.Q_mono_defect hdef hfirst).trans
    (actual_Q_mass hN hS hs (by positivity : 0≤7*v*M/25))
  have hp : 0≤160/(v*M)*((Pool S).card : ℝ) := by positivity
  unfold UniformCapacity208.JointMass
  exact hq.trans (ha.trans (le_add_of_nonneg_right hp))

theorem actual_scaled_max {N : ℕ} {S : Finset ℤ} {v M y z : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 31≤S.card)
    (hv : 1≤v) (hM : 0<M) (hy : 0≤y) (hz : 0≤z) (hzy : z≤4*y/5)
    (hsize : (S.card : ℝ)=v*y) (hdef : v*z≤(Defect S : ℝ))
    (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25)
    (hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ))
    (hW : (SigmaPrefix209.W S.card : ℝ)≤UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
      (S.card : ℝ)^2/4+14/5*S.card) :
    v^2*max (Baseline y z M) (P y z M)≤UniformCapacity208.JointMass N v M S := by
  rw [mul_max_of_nonneg _ _ (sq_nonneg v)]
  exact max_le (actual_scaled_baseline hN hS (by omega : 4≤S.card) hv hM hz hsize hdef hfirst)
    (actual_scaled_P hN hS hs hv hM hy hz hzy hsize hdef hfirst hF hW)

#print axioms Q_scale
#print axioms P_scale
#print axioms actual_scaled_P
#print axioms actual_scaled_max
end
end JSP233.UniformScale208
