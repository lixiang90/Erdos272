module

public import Erdos272.Resources.UniformActualWindow209

@[expose] public section

namespace JSP233.UniformFiniteCut209
open StarCompletion APGeometry SourceBridge208 UniformSourceCore208 UniformAbel208
open UniformScale208 UniformEnvelope208
open scoped Classical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0

theorem actual_checked_height_cut {N : ℕ} {S : Finset ℤ} {v M T y z q : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 31≤S.card)
    (hv : 1≤v) (hvhi : v≤155) (hM : 31≤M) (hT : M≤T) (hy : T≤y)
    (hz : 0≤z) (hzcap : z≤4*M/5) (hsize : (S.card : ℝ)=v*y)
    (hdef : v*z≤(Defect S : ℝ)) (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25)
    (hfinite : ∀ (k : ℕ), k≤1540096 → F k≤Delta*k+(579/1000 : ℝ))
    (hcut : q≤Baseline T z M ∨ HeightEnd M z q≤9900) (hc : Decision M T z q) :
    v^2*q≤UniformCapacity208.JointMass N v M S := by
  have hbase (hb : q≤Baseline T z M) : v^2*q≤UniformCapacity208.JointMass N v M S := by
    have hm := mul_le_mul_of_nonneg_left hy hz
    have hqy : q≤Baseline y z M := by unfold Baseline at *; linarith only [hb,hm]
    exact (mul_le_mul_of_nonneg_left hqy (sq_nonneg v)).trans
      (actual_scaled_baseline hN hS (by omega : 4≤S.card) hv
        (by linarith only [hM] : 0<M) hz hsize hdef hfirst)
  by_cases hb : q≤Baseline T z M
  · exact hbase hb
  · have hcap := hcut.resolve_left hb
    rcases hc with hcB | ⟨hzpos,hqT,hqY,hc1,hc2⟩
    · exact hbase hcB
    · by_cases hY : HeightEnd M z q≤y
      · have he : Baseline (HeightEnd M z q) z M=q := by
          unfold Baseline HeightEnd
          field_simp
          <;> ring
        have hm := mul_le_mul_of_nonneg_left hY hz
        have hqy : q≤Baseline y z M := by unfold Baseline at *; linarith only [he,hm]
        exact (mul_le_mul_of_nonneg_left hqy (sq_nonneg v)).trans
          (actual_scaled_baseline hN hS (by omega : 4≤S.card) hv
            (by linarith only [hM] : 0<M) hz hsize hdef hfirst)
      · have hyhi : y≤9900 := (le_of_not_ge hY).trans hcap
        have hy0 : 0≤y := by linarith only [hM,hT,hy]
        have hv0 : 0≤v := by linarith only [hv]
        have hcardR : (S.card : ℝ)≤1540096 := by
          have hm := mul_le_mul hvhi hyhi hy0 (by norm_num : (0 : ℝ)≤155)
          nlinarith only [hm,hsize]
        have hcard : S.card≤1540096 := by exact_mod_cast hcardR
        have hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ) := by
          intro k _hk hkm
          exact hfinite k (by have := maxAPSize_le_card S; omega)
        have hW := SigmaCertificate209.actual_bound S.card hs (by omega : S.card≤1670000)
        apply UniformEnvelope208.actual_checked_height hN hS hs hv hM hT hy hz hzcap hsize hdef hfirst hF hW
        exact Or.inr ⟨hzpos,hqT,hqY,hc1,hc2⟩

#print axioms actual_checked_height_cut
end
end JSP233.UniformFiniteCut209
