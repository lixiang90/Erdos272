module

public import Erdos272.Arithmetic.UniformPotential208
public import Erdos272.Arithmetic.TotientWindow209
public import Erdos272.Arithmetic.SigmaCertificate209

@[expose] public section

namespace JSP233.UniformActualWindow209
open StarCompletion APGeometry SourceBridge208 UniformSourceCore208 UniformAbel208
open UniformEnvelope208 UniformPotential208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 65536

theorem actual_inputs {N : ℕ} {S : Finset ℤ}
    (hhigh : N ≤ 720896) (hS : S ⊆ Ground N) (hs : 31 ≤ S.card) :
    (∀ k, 1 ≤ k → k < MaxAPSize S → F k ≤ Delta*k+(579/1000 : ℝ)) ∧
      (SigmaPrefix209.W S.card : ℝ) ≤ UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
        (S.card : ℝ)^2/4+14/5*S.card := by
  have hc : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hS
  constructor
  · intro k hk hkm
    have hm := maxAPSize_le_card S
    simpa only [UniformAbel208.F,Delta] using TotientWindow209.mass_upper k (by omega)
  · exact SigmaCertificate209.actual_bound S.card hs (by omega)

theorem actual_checked_height {N : ℕ} {S : Finset ℤ} {v M T y z q : ℝ}
    (hhigh : N ≤ 720896) (hS : S ⊆ Ground N) (hs : 31 ≤ S.card)
    (hv : 1 ≤ v) (hM : 31 ≤ M) (hT : M ≤ T) (hy : T ≤ y)
    (hz : 0 ≤ z) (hzcap : z ≤ 4*M/5) (hsize : (S.card : ℝ)=v*y)
    (hdef : v*z ≤ (Defect S : ℝ)) (hc : Decision M T z q) :
    v^2*q ≤ UniformCapacity208.JointMass N v M S := by
  have hcard : S.card ≤ N := by simpa only [ground_card] using Finset.card_le_card hS
  have hN : 2 ≤ N := by omega
  obtain ⟨hF,hW⟩ := actual_inputs hhigh hS hs
  have hM0 : 0 ≤ M := by linarith only [hM]
  have hvm : M ≤ v*M := by nlinarith only [mul_nonneg (by linarith only [hv] : 0 ≤ v-1) hM0]
  have hvmS : v*M ≤ S.card := by
    rw [hsize]
    exact mul_le_mul_of_nonneg_left (hT.trans hy) (by linarith only [hv])
  have hfirst : 0 ≤ (S.card : ℝ)-1-7*v*M/25 := by nlinarith only [hM,hvm,hvmS]
  exact UniformEnvelope208.actual_checked_height hN hS hs hv hM hT hy hz hzcap
    hsize hdef hfirst hF hW hc

theorem actual_row242 {N : ℕ} {S : Finset ℤ} {v y : ℝ}
    (hhigh : N ≤ 720896) (hS : S ⊆ Ground N) (hs : 31 ≤ S.card)
    (i : Fin 183) (j : Fin 7) (hv : 1 ≤ v)
    (hy : ((edges242[i.val]!)[j.val]! : ℝ) ≤ y)
    (hsize : (S.card : ℝ)=v*y)
    (hdef : v*((cuts242[i.val]!)[j.val]! : ℝ) ≤ (Defect S : ℝ)) :
    v^2*(heights242[i.val+1]! : ℝ) ≤ UniformCapacity208.JointMass N v 242 S := by
  obtain ⟨hT,hcut,hcap⟩ := row_domain242 i j
  apply actual_checked_height hhigh hS hs hv (by norm_num : (31 : ℝ) ≤ 242)
    (by exact_mod_cast hT) hy (by positivity) _ hsize hdef (source242 i j)
  have hh : (5 : ℝ)*((cuts242[i.val]!)[j.val]! : ℝ) ≤ 4*242 := by exact_mod_cast hcap
  linarith only [hh]

theorem actual_row243 {N : ℕ} {S : Finset ℤ} {v y : ℝ}
    (hhigh : N ≤ 720896) (hS : S ⊆ Ground N) (hs : 31 ≤ S.card)
    (i : Fin 184) (j : Fin 7) (hv : 1 ≤ v)
    (hy : ((edges243[i.val]!)[j.val]! : ℝ) ≤ y)
    (hsize : (S.card : ℝ)=v*y)
    (hdef : v*((cuts243[i.val]!)[j.val]! : ℝ) ≤ (Defect S : ℝ)) :
    v^2*(heights243[i.val+1]! : ℝ) ≤ UniformCapacity208.JointMass N v 243 S := by
  obtain ⟨hT,hcut,hcap⟩ := row_domain243 i j
  apply actual_checked_height hhigh hS hs hv (by norm_num : (31 : ℝ) ≤ 243)
    (by exact_mod_cast hT) hy (by positivity) _ hsize hdef (source243 i j)
  have hh : (5 : ℝ)*((cuts243[i.val]!)[j.val]! : ℝ) ≤ 4*243 := by exact_mod_cast hcap
  linarith only [hh]

#print axioms actual_inputs
#print axioms actual_checked_height
#print axioms actual_row242
#print axioms actual_row243
end
end JSP233.UniformActualWindow209
