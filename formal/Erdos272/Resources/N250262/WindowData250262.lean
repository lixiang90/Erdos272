module

public import Erdos272.Resources.N250262.SourceWindowData250262

@[expose] public section

namespace JSP233.WindowData250262
open SourceWindowData250262 (Info)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def info00 : Info :=
  ⟨250262, 251008, 150, 237924, SourceWindowData250262.info00.fee⟩
def info01 : Info := SourceWindowData250262.info00
def info02 : Info := SourceWindowData250262.info01
def info03 : Info := SourceWindowData250262.info02
def info04 : Info := SourceWindowData250262.info03

def info (w : ℕ) : Info := match w with
  | 0 => info00
  | 1 => info01
  | 2 => info02
  | 3 => info03
  | 4 => info04
  | _ => info00

def sourceIndex (w : ℕ) : ℕ := if w = 0 then 0 else w-1
def HCommon : ℝ := 5271/400
def G (w : ℕ) : ℝ := SourceWindowData250262.G (sourceIndex w)
def Response (w : ℕ) : ℝ :=
  ShadowResponse291012.Response (G w*(((info w).high-1 : ℕ) : ℝ))
def Delta (w : ℕ) : ℝ := 1/2-129/800-Response w
def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)

theorem links {w : ℕ} (hw : w < 5) :
    sourceIndex w < 4 ∧
    (SourceWindowData250262.info (sourceIndex w)).memberFloor = (info w).memberFloor ∧
    (SourceWindowData250262.info (sourceIndex w)).fee = (info w).fee ∧
    (info w).high ≤ (SourceWindowData250262.info (sourceIndex w)).high := by
  interval_cases w <;> decide

structure Gates (w : ℕ) : Prop where
  low_bound : 250262 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 291011
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  response_nonnegative : 0 ≤ Response w
  delta_nonnegative : 0 ≤ Delta w
  low_gap : 0 < Delta w*((info w).low : ℝ)^2-
    (900+289/2+HCommon)*(info w).low-(info w).fee-1295
  low_slope : 0 ≤ 2*Delta w*(info w).low-(900+289/2+HCommon)
  small_gap : 0 < (71/800 : ℝ)*(info w).low-
    ((SmallCount w : ℝ)+289/2+HCommon)-1296/(info w).low

theorem gate00 : Gates 0 := by
  constructor <;> norm_num [G, sourceIndex, SourceWindowData250262.G, Response, ShadowResponse291012.Response, Delta, SmallCount, HCommon, info, info00, info01, info02, info03, info04, SourceWindowData250262.info, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03]
#print axioms gate00

theorem gate01 : Gates 1 := by
  constructor <;> norm_num [G, sourceIndex, SourceWindowData250262.G, Response, ShadowResponse291012.Response, Delta, SmallCount, HCommon, info, info00, info01, info02, info03, info04, SourceWindowData250262.info, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03]
#print axioms gate01

theorem gate02 : Gates 2 := by
  constructor <;> norm_num [G, sourceIndex, SourceWindowData250262.G, Response, ShadowResponse291012.Response, Delta, SmallCount, HCommon, info, info00, info01, info02, info03, info04, SourceWindowData250262.info, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03]
#print axioms gate02

theorem gate03 : Gates 3 := by
  constructor <;> norm_num [G, sourceIndex, SourceWindowData250262.G, Response, ShadowResponse291012.Response, Delta, SmallCount, HCommon, info, info00, info01, info02, info03, info04, SourceWindowData250262.info, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03]
#print axioms gate03

theorem gate04 : Gates 4 := by
  constructor <;> norm_num [G, sourceIndex, SourceWindowData250262.G, Response, ShadowResponse291012.Response, Delta, SmallCount, HCommon, info, info00, info01, info02, info03, info04, SourceWindowData250262.info, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03]
#print axioms gate04

theorem gates {w : ℕ} (hw : w < 5) : Gates w := by
  interval_cases w
  · exact gate00
  · exact gate01
  · exact gate02
  · exact gate03
  · exact gate04

theorem cover {N : ℕ} (hlo : 250262 ≤ N) (hhi : N ≤ 291011) :
    ∃ w : ℕ, w < 5 ∧ (info w).low ≤ N ∧ N ≤ (info w).high := by
  by_cases h0 : N ≤ 251008
  · refine ⟨0, by decide, ?_, ?_⟩ <;> norm_num [info, info00, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03] <;> omega
  by_cases h1 : N ≤ 261008
  · refine ⟨1, by decide, ?_, ?_⟩ <;> norm_num [info, info01, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03] <;> omega
  by_cases h2 : N ≤ 271009
  · refine ⟨2, by decide, ?_, ?_⟩ <;> norm_num [info, info02, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03] <;> omega
  by_cases h3 : N ≤ 281010
  · refine ⟨3, by decide, ?_, ?_⟩ <;> norm_num [info, info03, SourceWindowData250262.info00, SourceWindowData250262.info01, SourceWindowData250262.info02, SourceWindowData250262.info03] <;> omega
  refine ⟨4, by decide, ?_, ?_⟩ <;> norm_num [info, info04, SourceWindowData250262.info03] <;> omega

#print axioms links
#print axioms gates
#print axioms cover
end
end JSP233.WindowData250262
