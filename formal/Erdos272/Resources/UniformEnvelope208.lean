module

public import Erdos272.Arithmetic.UniformHigh208
public import Erdos272.Arithmetic.UniformConcave208
public import Erdos272.Resources.UniformScale208

@[expose] public section

/-! A finite rational height test controls the entire continuous source domain. -/
namespace JSP233.UniformEnvelope208
open UniformSourceCore208 UniformActual208 UniformScale208 UniformConcave208 UniformHigh208
open StarCompletion SourceBridge208 UniformAbel208 Set
noncomputable section
set_option maxHeartbeats 0

theorem pay_min {f : ℝ→ℝ} {a b c q : ℝ} (hac : a≤c)
    (hb : q≤f b) (hc : c∈Icc a b → q≤f c) : q≤f (min b c) := by
  by_cases hbc : b≤c
  · simpa only [min_eq_left hbc] using hb
  · simpa only [min_eq_right (le_of_lt (lt_of_not_ge hbc))] using hc ⟨hac,le_of_lt (lt_of_not_ge hbc)⟩

theorem pay_max {f : ℝ→ℝ} {a b c q : ℝ} (hcb : c≤b)
    (ha : q≤f a) (hc : c∈Icc a b → q≤f c) : q≤f (max a c) := by
  by_cases hca : c≤a
  · simpa only [max_eq_left hca] using ha
  · simpa only [max_eq_right (le_of_lt (lt_of_not_ge hca))] using hc ⟨le_of_lt (lt_of_not_ge hca),hcb⟩

theorem low_interval_min {a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a)
    (hz : 0≤z) (hza : 2*z≤a) (hax : a≤x) (hxb : x≤b)
    (hqa : q≤P a z M) (hqb : q≤P b z M)
    (hc1 : 3*z-1∈Icc a b → q≤P (3*z-1) z M)
    (hc2 : (5*z-2)/2∈Icc a b → q≤P ((5*z-2)/2) z M) : q≤P x z M := by
  by_cases hx2 : x≤(5*z-2)/2
  · have hright := pay_min (f:=fun y=>P y z M) (hax.trans hx2) hqb hc2
    exact P_min_11 hM hMa hz hza hax (le_min hxb hx2) (min_le_right _ _) hqa hright
  · have h2x : (5*z-2)/2≤x := (lt_of_not_ge hx2).le
    by_cases hx1 : x≤3*z-1
    · have hleft := pay_max (f:=fun y=>P y z M) (h2x.trans hxb) hqa hc2
      have hright := pay_min (f:=fun y=>P y z M) (hax.trans hx1) hqb hc1
      exact P_min_10 hM (hMa.trans (le_max_left _ _)) hz (hza.trans (le_max_left _ _))
        (max_le hax h2x) (le_min hxb hx1) (le_max_right _ _) (min_le_right _ _) hleft hright
    · have h1x : 3*z-1≤x := (lt_of_not_ge hx1).le
      have hleft := pay_max (f:=fun y=>P y z M) (h1x.trans hxb) hqa hc1
      exact P_min_00 hM (hMa.trans (le_max_left _ _)) hz (hza.trans (le_max_left _ _))
        (max_le hax h1x) hxb (le_max_right _ _) hleft hqb

theorem interval_min {a b x z M q : ℝ} (hM : 31≤M) (hMa : M≤a)
    (hz : 0≤z) (hzcap : z≤4*M/5) (hax : a≤x) (hxb : x≤b)
    (hqa : q≤P a z M) (hqb : q≤P b z M)
    (hc1 : 3*z-1∈Icc a b → q≤P (3*z-1) z M)
    (hc2 : (5*z-2)/2∈Icc a b → q≤P ((5*z-2)/2) z M) : q≤P x z M := by
  by_cases hx : x≤2*z
  · exact hqa.trans (P_high_mono hM hMa hax hx hzcap)
  · have hzx : 2*z≤x := (lt_of_not_ge hx).le
    have hleft : q≤P (max a (2*z)) z M := by
      by_cases hza : 2*z≤a
      · simpa only [max_eq_left hza] using hqa
      · rw [max_eq_right (le_of_lt (lt_of_not_ge hza))]
        exact hqa.trans (P_high_mono hM hMa (le_of_lt (lt_of_not_ge hza)) le_rfl hzcap)
    exact low_interval_min hM (hMa.trans (le_max_left _ _)) hz (le_max_right _ _)
      (max_le hax hzx) hxb hleft hqb
      (fun hh=>hc1 ⟨(le_max_left _ _).trans hh.1,hh.2⟩)
      (fun hh=>hc2 ⟨(le_max_left _ _).trans hh.1,hh.2⟩)

def HeightEnd (M z q : ℝ) : ℝ := q/z+7*M/25+1

def Decision (M T z q : ℝ) : Prop :=
  q≤Baseline T z M ∨ 0<z ∧
    q≤P T z M ∧ q≤P (HeightEnd M z q) z M ∧
    (3*z-1∈Icc T (HeightEnd M z q) → q≤P (3*z-1) z M) ∧
    ((5*z-2)/2∈Icc T (HeightEnd M z q) → q≤P ((5*z-2)/2) z M)

theorem decision_sound {M T z q y : ℝ} (hM : 31≤M) (hT : M≤T) (hz : 0≤z)
    (hzcap : z≤4*M/5) (hy : T≤y) (hc : Decision M T z q) :
    q≤max (Baseline y z M) (P y z M) := by
  rcases hc with hb | ⟨hzpos,hqT,hqY,hc1,hc2⟩
  · have hm := mul_le_mul_of_nonneg_left hy hz
    have hb' : q≤Baseline y z M := by unfold Baseline at *;linarith only [hb,hm]
    exact hb'.trans (le_max_left _ _)
  · by_cases hY : HeightEnd M z q≤y
    · have he : Baseline (HeightEnd M z q) z M=q := by unfold Baseline HeightEnd;field_simp;ring
      have hm := mul_le_mul_of_nonneg_left hY hz
      have hb : q≤Baseline y z M := by unfold Baseline at *;linarith only [he,hm]
      exact hb.trans (le_max_left _ _)
    · have hyY : y≤HeightEnd M z q := (lt_of_not_ge hY).le
      exact (interval_min hM hT hz hzcap hy hyY hqT hqY hc1 hc2).trans (le_max_right _ _)

theorem actual_checked_height {N : ℕ} {S : Finset ℤ} {v M T y z q : ℝ}
    (hN : 2≤N) (hS : S⊆Ground N) (hs : 31≤S.card)
    (hv : 1≤v) (hM : 31≤M) (hT : M≤T) (hy : T≤y)
    (hz : 0≤z) (hzcap : z≤4*M/5) (hsize : (S.card : ℝ)=v*y)
    (hdef : v*z≤(Defect S : ℝ)) (hfirst : 0≤(S.card : ℝ)-1-7*v*M/25)
    (hF : ∀ k,1≤k → k<MaxAPSize S → F k≤Delta*k+(579/1000 : ℝ))
    (hW : (SigmaPrefix209.W S.card : ℝ)≤UniformSourceCore208.Sigma*(S.card : ℝ)^3/6-
      (S.card : ℝ)^2/4+14/5*S.card) (hc : Decision M T z q) :
    v^2*q≤UniformCapacity208.JointMass N v M S := by
  have hpaid := actual_scaled_max hN hS hs hv (by linarith only [hM] : 0<M)
    (by linarith only [hM,hT,hy] : 0≤y) hz (by linarith only [hzcap,hT,hy]) hsize hdef hfirst hF hW
  exact (mul_le_mul_of_nonneg_left (decision_sound hM hT hz hzcap hy hc) (sq_nonneg v)).trans hpaid

#print axioms interval_min
#print axioms decision_sound
#print axioms actual_checked_height
end
end JSP233.UniformEnvelope208
