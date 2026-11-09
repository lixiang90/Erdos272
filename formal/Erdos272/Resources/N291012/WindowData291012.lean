module

public import Erdos272.Arithmetic.N291012.RowGeometry291012
public import Erdos272.Arithmetic.N291012.ShadowResponse291012

@[expose] public section

namespace JSP233.WindowData291012
open CleanupRows291012
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

structure Info where
  low : ℕ
  high : ℕ
  memberFloor : ℕ
  lastPotential : ℕ
  fee : ℕ

def info00 : Info := ⟨291012, 301012, 161, 275614, 6152995403⟩
def info01 : Info := ⟨301013, 321013, 164, 297730, 6973969908⟩
def info02 : Info := ⟨321014, 341014, 169, 314900, 7480571467⟩
def info03 : Info := ⟨341015, 361015, 175, 333570, 7884697728⟩
def info04 : Info := ⟨361016, 381016, 180, 359440, 8488205193⟩
def info05 : Info := ⟨381017, 401017, 184, 375018, 9086698848⟩
def info06 : Info := ⟨401018, 441018, 189, 414356, 10812555785⟩
def info07 : Info := ⟨441019, 481019, 198, 448962, 11896036662⟩
def info08 : Info := ⟨481020, 521020, 207, 499684, 13170944402⟩
def info09 : Info := ⟨521021, 561021, 216, 535456, 14245557179⟩
def info10 : Info := ⟨561022, 601022, 224, 580480, 15573133095⟩
def info11 : Info := ⟨601023, 641023, 232, 613250, 16742570524⟩
def info12 : Info := ⟨641024, 642498, 239, 632824, 15879600201⟩

def info (w : ℕ) : Info := match w with
  | 0 => info00
  | 1 => info01
  | 2 => info02
  | 3 => info03
  | 4 => info04
  | 5 => info05
  | 6 => info06
  | 7 => info07
  | 8 => info08
  | 9 => info09
  | 10 => info10
  | 11 => info11
  | 12 => info12
  | _ => info00

def potential (w n : ℕ) : ℕ :=
  if n=0 then 0 else (data (7*w+min (n-1) 6)).potential

def Psi (w n : ℕ) : ℝ := potential w n

def G (w : ℕ) : ℝ := 1/(6*((info w).lastPotential : ℝ))

def Response (w : ℕ) : ℝ := ShadowResponse291012.Response (G w*(((info w).high-1 : ℕ) : ℝ))

def Delta (w : ℕ) : ℝ := 1/2-129/800-Response w

def SmallCount (w : ℕ) : ℕ := ((info w).memberFloor-2)^2+((info w).memberFloor-1)

theorem links {w i : ℕ} (hw : w < 13) (hi : i < 7) :
    7*w+i < 91 ∧ (data (7*w+i)).row.low = (info w).low ∧
    (data (7*w+i)).row.high = (info w).high ∧
    (data (7*w+i)).memberFloor = (info w).memberFloor ∧
    potential w (i+1) = (data (7*w+i)).potential := by
  interval_cases w <;> interval_cases i <;> decide +kernel

theorem psi_mono {w : ℕ} (hw : w < 13) : Monotone (Psi w) := by
  apply monotone_nat_of_le_succ
  intro n
  by_cases hn : n < 7
  · have hh : potential w n ≤ potential w (n+1) := by
      interval_cases w <;> interval_cases n <;> decide +kernel
    dsimp only [Psi]
    exact_mod_cast hh
  · have h0 : n ≠ 0 := by omega
    have h1 : n+1 ≠ 0 := by omega
    have hm0 : min (n-1) 6 = 6 := by omega
    have hm1 : min (n+1-1) 6 = 6 := by omega
    simp only [Psi, potential, if_neg h0, if_neg h1, hm0, hm1, le_refl]

theorem psi_zero (w : ℕ) : Psi w 0 = 0 := by simp [Psi, potential]

theorem reciprocal {w : ℕ} (hw : w < 13) : 6*G w*Psi w 7 = 1 := by
  interval_cases w <;> norm_num [G, Psi, potential, info,info00, info01, info02, info03, info04, info05, info06, info07, info08, info09, info10, info11, info12, data,data06, data13, data20, data27, data34, data41, data48, data55, data62, data69, data76, data83, data90]

structure Gates (w : ℕ) : Prop where
  low_bound : 291012 ≤ (info w).low
  low_high : (info w).low ≤ (info w).high
  high_bound : (info w).high ≤ 642498
  member_three : 3 ≤ (info w).memberFloor
  g_positive : 0 < G w
  response_nonnegative : 0 ≤ Response w
  delta_nonnegative : 0 ≤ Delta w
  low_gap : 0 < Delta w*((info w).low : ℝ)^2-(4317/2 : ℝ)*(info w).low-(info w).fee-1295
  low_slope : 0 ≤ 2*Delta w*(info w).low-(4317/2 : ℝ)
  small_gap : 0 < (71/800 : ℝ)*(info w).low-(SmallCount w+317/2 : ℝ)-1296/(info w).low

theorem gate00 : Gates 0 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info00]
#print axioms gate00

theorem gate01 : Gates 1 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info01]
#print axioms gate01

theorem gate02 : Gates 2 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info02]
#print axioms gate02

theorem gate03 : Gates 3 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info03]
#print axioms gate03

theorem gate04 : Gates 4 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info04]
#print axioms gate04

theorem gate05 : Gates 5 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info05]
#print axioms gate05

theorem gate06 : Gates 6 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info06]
#print axioms gate06

theorem gate07 : Gates 7 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info07]
#print axioms gate07

theorem gate08 : Gates 8 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info08]
#print axioms gate08

theorem gate09 : Gates 9 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info09]
#print axioms gate09

theorem gate10 : Gates 10 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info10]
#print axioms gate10

theorem gate11 : Gates 11 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info11]
#print axioms gate11

theorem gate12 : Gates 12 := by
  constructor <;> norm_num [G, Response, ShadowResponse291012.Response, Delta, SmallCount, info, info12]
#print axioms gate12

theorem gates {w : ℕ} (hw : w < 13) : Gates w := by
  interval_cases w
  · exact gate00
  · exact gate01
  · exact gate02
  · exact gate03
  · exact gate04
  · exact gate05
  · exact gate06
  · exact gate07
  · exact gate08
  · exact gate09
  · exact gate10
  · exact gate11
  · exact gate12

theorem cover {N : ℕ} (hlo : 291012 ≤ N) (hhi : N ≤ 642498) :
    ∃ w : ℕ, w < 13 ∧ (info w).low ≤ N ∧ N ≤ (info w).high := by
  by_cases h0 : N ≤ 301012
  · refine ⟨0, by decide, ?_, ?_⟩ <;> norm_num [info, info00] <;> omega
  by_cases h1 : N ≤ 321013
  · refine ⟨1, by decide, ?_, ?_⟩ <;> norm_num [info, info01] <;> omega
  by_cases h2 : N ≤ 341014
  · refine ⟨2, by decide, ?_, ?_⟩ <;> norm_num [info, info02] <;> omega
  by_cases h3 : N ≤ 361015
  · refine ⟨3, by decide, ?_, ?_⟩ <;> norm_num [info, info03] <;> omega
  by_cases h4 : N ≤ 381016
  · refine ⟨4, by decide, ?_, ?_⟩ <;> norm_num [info, info04] <;> omega
  by_cases h5 : N ≤ 401017
  · refine ⟨5, by decide, ?_, ?_⟩ <;> norm_num [info, info05] <;> omega
  by_cases h6 : N ≤ 441018
  · refine ⟨6, by decide, ?_, ?_⟩ <;> norm_num [info, info06] <;> omega
  by_cases h7 : N ≤ 481019
  · refine ⟨7, by decide, ?_, ?_⟩ <;> norm_num [info, info07] <;> omega
  by_cases h8 : N ≤ 521020
  · refine ⟨8, by decide, ?_, ?_⟩ <;> norm_num [info, info08] <;> omega
  by_cases h9 : N ≤ 561021
  · refine ⟨9, by decide, ?_, ?_⟩ <;> norm_num [info, info09] <;> omega
  by_cases h10 : N ≤ 601022
  · refine ⟨10, by decide, ?_, ?_⟩ <;> norm_num [info, info10] <;> omega
  by_cases h11 : N ≤ 641023
  · refine ⟨11, by decide, ?_, ?_⟩ <;> norm_num [info, info11] <;> omega
  refine ⟨12, by decide, ?_, ?_⟩ <;> norm_num [info, info12] <;> omega

#print axioms links
#print axioms psi_mono
#print axioms psi_zero
#print axioms reciprocal
#print axioms gates
#print axioms cover
end
end JSP233.WindowData291012
