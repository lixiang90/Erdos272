module

public import Erdos272.Arithmetic.N158375.UnitFloorData158375

@[expose] public section

namespace JSP233.UnitFloorChecks158375G0
open CoreUnionSource200000 UnitFloorData158375 PrimeTable158375
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : (List.range 16).all (fun i => decide (unitFloor (0+i) ≤ smallUnit (0+i))) = true := by decide +kernel
#print axioms checked00

theorem piece00 {a : ℕ} (hlo : 0 ≤ a) (hhi : a < 16) : unitFloor a ≤ UnitBound a := by
  have hm : a-0 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked00 (a-0) hm)
  have he : 0+(a-0) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece00

theorem checked01 : (List.range 16).all (fun i => decide (unitFloor (16+i) ≤ smallUnit (16+i))) = true := by decide +kernel
#print axioms checked01

theorem piece01 {a : ℕ} (hlo : 16 ≤ a) (hhi : a < 32) : unitFloor a ≤ UnitBound a := by
  have hm : a-16 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked01 (a-16) hm)
  have he : 16+(a-16) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece01

theorem checked02 : (List.range 16).all (fun i => decide (unitFloor (32+i) ≤ smallUnit (32+i))) = true := by decide +kernel
#print axioms checked02

theorem piece02 {a : ℕ} (hlo : 32 ≤ a) (hhi : a < 48) : unitFloor a ≤ UnitBound a := by
  have hm : a-32 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked02 (a-32) hm)
  have he : 32+(a-32) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece02

theorem checked03 : (List.range 16).all (fun i => decide (unitFloor (48+i) ≤ smallUnit (48+i))) = true := by decide +kernel
#print axioms checked03

theorem piece03 {a : ℕ} (hlo : 48 ≤ a) (hhi : a < 64) : unitFloor a ≤ UnitBound a := by
  have hm : a-48 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked03 (a-48) hm)
  have he : 48+(a-48) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece03

theorem checked04 : (List.range 16).all (fun i => decide (unitFloor (64+i) ≤ smallUnit (64+i))) = true := by decide +kernel
#print axioms checked04

theorem piece04 {a : ℕ} (hlo : 64 ≤ a) (hhi : a < 80) : unitFloor a ≤ UnitBound a := by
  have hm : a-64 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked04 (a-64) hm)
  have he : 64+(a-64) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece04

theorem checked05 : (List.range 16).all (fun i => decide (unitFloor (80+i) ≤ smallUnit (80+i))) = true := by decide +kernel
#print axioms checked05

theorem piece05 {a : ℕ} (hlo : 80 ≤ a) (hhi : a < 96) : unitFloor a ≤ UnitBound a := by
  have hm : a-80 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked05 (a-80) hm)
  have he : 80+(a-80) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece05

theorem checked06 : (List.range 16).all (fun i => decide (unitFloor (96+i) ≤ smallUnit (96+i))) = true := by decide +kernel
#print axioms checked06

theorem piece06 {a : ℕ} (hlo : 96 ≤ a) (hhi : a < 112) : unitFloor a ≤ UnitBound a := by
  have hm : a-96 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked06 (a-96) hm)
  have he : 96+(a-96) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece06

theorem checked07 : (List.range 16).all (fun i => decide (unitFloor (112+i) ≤ smallUnit (112+i))) = true := by decide +kernel
#print axioms checked07

theorem piece07 {a : ℕ} (hlo : 112 ≤ a) (hhi : a < 128) : unitFloor a ≤ UnitBound a := by
  have hm : a-112 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked07 (a-112) hm)
  have he : 112+(a-112) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece07

theorem checked08 : (List.range 16).all (fun i => decide (unitFloor (128+i) ≤ smallUnit (128+i))) = true := by decide +kernel
#print axioms checked08

theorem piece08 {a : ℕ} (hlo : 128 ≤ a) (hhi : a < 144) : unitFloor a ≤ UnitBound a := by
  have hm : a-128 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked08 (a-128) hm)
  have he : 128+(a-128) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece08

theorem checked09 : (List.range 16).all (fun i => decide (unitFloor (144+i) ≤ smallUnit (144+i))) = true := by decide +kernel
#print axioms checked09

theorem piece09 {a : ℕ} (hlo : 144 ≤ a) (hhi : a < 160) : unitFloor a ≤ UnitBound a := by
  have hm : a-144 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked09 (a-144) hm)
  have he : 144+(a-144) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece09

theorem checked10 : (List.range 16).all (fun i => decide (unitFloor (160+i) ≤ smallUnit (160+i))) = true := by decide +kernel
#print axioms checked10

theorem piece10 {a : ℕ} (hlo : 160 ≤ a) (hhi : a < 176) : unitFloor a ≤ UnitBound a := by
  have hm : a-160 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked10 (a-160) hm)
  have he : 160+(a-160) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece10

theorem checked11 : (List.range 16).all (fun i => decide (unitFloor (176+i) ≤ smallUnit (176+i))) = true := by decide +kernel
#print axioms checked11

theorem piece11 {a : ℕ} (hlo : 176 ≤ a) (hhi : a < 192) : unitFloor a ≤ UnitBound a := by
  have hm : a-176 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked11 (a-176) hm)
  have he : 176+(a-176) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece11

theorem bound {a : ℕ} (hlo : 0 ≤ a) (hhi : a < 192) : unitFloor a ≤ UnitBound a := by
  by_cases h0 : a < 16
  · exact piece00 (by omega) h0
  by_cases h1 : a < 32
  · exact piece01 (by omega) h1
  by_cases h2 : a < 48
  · exact piece02 (by omega) h2
  by_cases h3 : a < 64
  · exact piece03 (by omega) h3
  by_cases h4 : a < 80
  · exact piece04 (by omega) h4
  by_cases h5 : a < 96
  · exact piece05 (by omega) h5
  by_cases h6 : a < 112
  · exact piece06 (by omega) h6
  by_cases h7 : a < 128
  · exact piece07 (by omega) h7
  by_cases h8 : a < 144
  · exact piece08 (by omega) h8
  by_cases h9 : a < 160
  · exact piece09 (by omega) h9
  by_cases h10 : a < 176
  · exact piece10 (by omega) h10
  exact piece11 (by omega) hhi
#print axioms bound
end JSP233.UnitFloorChecks158375G0
