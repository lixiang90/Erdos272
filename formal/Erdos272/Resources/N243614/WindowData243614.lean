module

public import Erdos272.Resources.N243614.SourceWindowData243614

@[expose] public section

namespace JSP233.WindowData243614
open SourceWindowData243614 (CoeffA CoeffB CoeffC SourceUpper)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

structure Info where
  low : ℕ
  high : ℕ
  memberFloor : ℕ

def info (w : ℕ) : Info :=
  if w=0 then ⟨243614,246007,148⟩ else ⟨246007,250261,148⟩
def HCommon : ℝ := 5271/400
def G (_w : ℕ) : ℝ := SourceWindowData243614.G
def FeeA (w : ℕ) : ℝ := if w=0 then 0 else CoeffA
def FeeB (w : ℕ) : ℝ := if w=0 then 0 else CoeffB
def FeeC (w : ℕ) : ℝ := if w=0 then SourceUpper 246007 else CoeffC
def Fee (N w : ℕ) : ℝ := FeeA w*(N : ℝ)^2+FeeB w*N+FeeC w
def Response (w : ℕ) : ℝ :=
  ShadowResponse291012.Response (G w*(((info w).high-1 : ℕ) : ℝ))
def Delta (w : ℕ) : ℝ := 1/2-129/800-Response w-FeeA w
def Loss (w : ℕ) : ℝ := 594+289/2+HCommon+FeeB w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)

structure Gates (w : ℕ) : Prop where
  low_bound : 243614 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 250261
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  response_nonnegative : 0 ≤ Response w
  delta_nonnegative : 0 ≤ Delta w
  low_gap : 0 < Delta w*((info w).low : ℝ)^2-Loss w*(info w).low-FeeC w-1295
  low_slope : 0 ≤ 2*Delta w*(info w).low-Loss w
  small_gap : 0 < (71/800 : ℝ)*(info w).low-
    ((SmallCount w : ℝ)+289/2+HCommon)-1296/(info w).low

theorem gate0 : Gates 0 := by
  constructor <;> norm_num [G, SourceWindowData243614.G, Response, ShadowResponse291012.Response, Delta, Loss, SmallCount, HCommon, info, FeeA, FeeB, FeeC, SourceUpper, CoeffA, CoeffB, CoeffC]
#print axioms gate0

theorem gate1 : Gates 1 := by
  constructor <;> norm_num [G, SourceWindowData243614.G, Response, ShadowResponse291012.Response, Delta, Loss, SmallCount, HCommon, info, FeeA, FeeB, FeeC, SourceUpper, CoeffA, CoeffB, CoeffC]
#print axioms gate1

theorem gates {w : ℕ} (hw : w < 2) : Gates w := by
  interval_cases w
  · exact gate0
  · exact gate1

theorem cover {N : ℕ} (hlo : 243614 ≤ N) (hhi : N ≤ 250261) :
    ∃ w : ℕ, w < 2 ∧ (info w).low ≤ N ∧ N ≤ (info w).high := by
  by_cases h : N ≤ 246007
  · exact ⟨0, by decide, by simpa [info] using hlo, by simpa [info] using h⟩
  · exact ⟨1, by decide, by simp [info]; omega, by simpa [info] using hhi⟩

#print axioms gates
#print axioms cover
end
end JSP233.WindowData243614
