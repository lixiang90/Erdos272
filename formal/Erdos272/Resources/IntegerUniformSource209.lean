import Erdos272.Resources.UniformActualGlobal209

namespace JSP233.IntegerUniformSource209
open StarCompletion APGeometry SourceBridge208 UniformSourceCore208 UniformAbel208
open UniformScale208 UniformEnvelope208
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option autoImplicit false

/-- A fixed physical M needs finite arithmetic only in the region where the
analytic source beats its elementary baseline. The endpoint cutoff here is
the actual sealed totient domain, rather than a scaled-menu cutoff. -/
theorem actual_checked_height {N : ℕ} {S : Finset ℤ} {M T z q : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hM : 31≤M) (hMT : M≤T)
    (hT : T≤S.card) (hz : 0≤z) (hzcap : z≤4*M/5) (hdef : z≤(Defect S : ℝ))
    (hcut : q≤Baseline T z M ∨ HeightEnd M z q≤1540096)
    (hc : Decision M T z q) : q≤UniformCapacity208.JointMass N 1 M S := by
  have hs : 31≤S.card := by
    have hh : (31 : ℝ)≤S.card := hM.trans (hMT.trans hT)
    exact_mod_cast hh
  have hfirst : 0≤(S.card : ℝ)-1-7*1*M/25 := by
    nlinarith only [hM,hMT,hT]
  have hbase (hb : q≤Baseline T z M) : q≤UniformCapacity208.JointMass N 1 M S := by
    have hm := mul_le_mul_of_nonneg_right hT hz
    have hqy : q≤Baseline S.card z M := by unfold Baseline at *; linarith only [hb,hm]
    have hh := actual_scaled_baseline hN hS (by omega : 4≤S.card)
      (v := 1) (by norm_num) (by linarith only [hM] : 0<M) hz
      (by ring : (S.card : ℝ)=1*S.card) (by simpa using hdef) hfirst
    simp only [one_pow,one_mul] at hh
    exact hqy.trans hh
  by_cases hb : q≤Baseline T z M
  · exact hbase hb
  · have hcap := hcut.resolve_left hb
    rcases hc with hcB | ⟨hzpos,hqT,hqY,hc1,hc2⟩
    · exact hbase hcB
    · by_cases hY : HeightEnd M z q≤S.card
      · have he : Baseline (HeightEnd M z q) z M=q := by
          unfold Baseline HeightEnd
          field_simp
          <;> ring
        have hm := mul_le_mul_of_nonneg_right hY hz
        have hqy : q≤Baseline S.card z M := by unfold Baseline at *; linarith only [he,hm]
        have hh := actual_scaled_baseline hN hS (by omega : 4≤S.card)
          (v := 1) (by norm_num) (by linarith only [hM] : 0<M) hz
          (by ring : (S.card : ℝ)=1*S.card) (by simpa using hdef) hfirst
        simp only [one_pow,one_mul] at hh
        exact hqy.trans hh
      · have hcard : S.card≤1540096 := by
          have hh : (S.card : ℝ)≤1540096 := (le_of_not_ge hY).trans hcap
          exact_mod_cast hh
        have hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ) := by
          intro k _hk hkm
          have hk : k≤1540096 := by have := maxAPSize_le_card S; omega
          simpa only [UniformAbel208.F,Delta] using TotientExtended209.mass_upper k hk
        have hW := SigmaCertificate209.actual_bound S.card hs (by omega : S.card≤1670000)
        have hh := UniformEnvelope208.actual_checked_height hN hS hs (v := 1) (by norm_num)
          hM hMT hT hz hzcap (by ring : (S.card : ℝ)=1*S.card)
          (by simpa using hdef) hfirst hF hW (Or.inr ⟨hzpos,hqT,hqY,hc1,hc2⟩)
        simpa only [one_pow,one_mul] using hh

#print axioms actual_checked_height
end
end JSP233.IntegerUniformSource209

