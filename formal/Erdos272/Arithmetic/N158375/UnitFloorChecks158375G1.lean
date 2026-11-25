module

public import Erdos272.Arithmetic.N158375.UnitFloorData158375

@[expose] public section

namespace JSP233.UnitFloorChecks158375G1
open CoreUnionSource200000 UnitFloorData158375 PrimeTable158375
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : (List.range 16).all (fun i => decide (unitFloor (192+i) ≤ smallUnit (192+i))) = true := by decide +kernel
#print axioms checked00

theorem piece00 {a : ℕ} (hlo : 192 ≤ a) (hhi : a < 208) : unitFloor a ≤ UnitBound a := by
  have hm : a-192 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked00 (a-192) hm)
  have he : 192+(a-192) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece00

theorem checked01 : (List.range 16).all (fun i => decide (unitFloor (208+i) ≤ smallUnit (208+i))) = true := by decide +kernel
#print axioms checked01

theorem piece01 {a : ℕ} (hlo : 208 ≤ a) (hhi : a < 224) : unitFloor a ≤ UnitBound a := by
  have hm : a-208 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked01 (a-208) hm)
  have he : 208+(a-208) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece01

theorem checked02 : (List.range 16).all (fun i => decide (unitFloor (224+i) ≤ smallUnit (224+i))) = true := by decide +kernel
#print axioms checked02

theorem piece02 {a : ℕ} (hlo : 224 ≤ a) (hhi : a < 240) : unitFloor a ≤ UnitBound a := by
  have hm : a-224 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked02 (a-224) hm)
  have he : 224+(a-224) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece02

theorem checked03 : (List.range 16).all (fun i => decide (unitFloor (240+i) ≤ smallUnit (240+i))) = true := by decide +kernel
#print axioms checked03

theorem piece03 {a : ℕ} (hlo : 240 ≤ a) (hhi : a < 256) : unitFloor a ≤ UnitBound a := by
  have hm : a-240 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked03 (a-240) hm)
  have he : 240+(a-240) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece03

theorem checked04 : (List.range 16).all (fun i => decide (unitFloor (256+i) ≤ smallUnit (256+i))) = true := by decide +kernel
#print axioms checked04

theorem piece04 {a : ℕ} (hlo : 256 ≤ a) (hhi : a < 272) : unitFloor a ≤ UnitBound a := by
  have hm : a-256 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked04 (a-256) hm)
  have he : 256+(a-256) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece04

theorem checked05 : (List.range 16).all (fun i => decide (unitFloor (272+i) ≤ smallUnit (272+i))) = true := by decide +kernel
#print axioms checked05

theorem piece05 {a : ℕ} (hlo : 272 ≤ a) (hhi : a < 288) : unitFloor a ≤ UnitBound a := by
  have hm : a-272 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked05 (a-272) hm)
  have he : 272+(a-272) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece05

theorem checked06 : (List.range 16).all (fun i => decide (unitFloor (288+i) ≤ smallUnit (288+i))) = true := by decide +kernel
#print axioms checked06

theorem piece06 {a : ℕ} (hlo : 288 ≤ a) (hhi : a < 304) : unitFloor a ≤ UnitBound a := by
  have hm : a-288 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked06 (a-288) hm)
  have he : 288+(a-288) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece06

theorem checked07 : (List.range 16).all (fun i => decide (unitFloor (304+i) ≤ smallUnit (304+i))) = true := by decide +kernel
#print axioms checked07

theorem piece07 {a : ℕ} (hlo : 304 ≤ a) (hhi : a < 320) : unitFloor a ≤ UnitBound a := by
  have hm : a-304 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked07 (a-304) hm)
  have he : 304+(a-304) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece07

theorem checked08 : (List.range 16).all (fun i => decide (unitFloor (320+i) ≤ smallUnit (320+i))) = true := by decide +kernel
#print axioms checked08

theorem piece08 {a : ℕ} (hlo : 320 ≤ a) (hhi : a < 336) : unitFloor a ≤ UnitBound a := by
  have hm : a-320 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked08 (a-320) hm)
  have he : 320+(a-320) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece08

theorem checked09 : (List.range 16).all (fun i => decide (unitFloor (336+i) ≤ smallUnit (336+i))) = true := by decide +kernel
#print axioms checked09

theorem piece09 {a : ℕ} (hlo : 336 ≤ a) (hhi : a < 352) : unitFloor a ≤ UnitBound a := by
  have hm : a-336 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked09 (a-336) hm)
  have he : 336+(a-336) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece09

theorem checked10 : (List.range 16).all (fun i => decide (unitFloor (352+i) ≤ smallUnit (352+i))) = true := by decide +kernel
#print axioms checked10

theorem piece10 {a : ℕ} (hlo : 352 ≤ a) (hhi : a < 368) : unitFloor a ≤ UnitBound a := by
  have hm : a-352 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked10 (a-352) hm)
  have he : 352+(a-352) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece10

theorem checked11 : (List.range 16).all (fun i => decide (unitFloor (368+i) ≤ smallUnit (368+i))) = true := by decide +kernel
#print axioms checked11

theorem piece11 {a : ℕ} (hlo : 368 ≤ a) (hhi : a < 384) : unitFloor a ≤ UnitBound a := by
  have hm : a-368 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked11 (a-368) hm)
  have he : 368+(a-368) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece11

theorem bound {a : ℕ} (hlo : 192 ≤ a) (hhi : a < 384) : unitFloor a ≤ UnitBound a := by
  by_cases h0 : a < 208
  · exact piece00 (by omega) h0
  by_cases h1 : a < 224
  · exact piece01 (by omega) h1
  by_cases h2 : a < 240
  · exact piece02 (by omega) h2
  by_cases h3 : a < 256
  · exact piece03 (by omega) h3
  by_cases h4 : a < 272
  · exact piece04 (by omega) h4
  by_cases h5 : a < 288
  · exact piece05 (by omega) h5
  by_cases h6 : a < 304
  · exact piece06 (by omega) h6
  by_cases h7 : a < 320
  · exact piece07 (by omega) h7
  by_cases h8 : a < 336
  · exact piece08 (by omega) h8
  by_cases h9 : a < 352
  · exact piece09 (by omega) h9
  by_cases h10 : a < 368
  · exact piece10 (by omega) h10
  exact piece11 (by omega) hhi
#print axioms bound
end JSP233.UnitFloorChecks158375G1
