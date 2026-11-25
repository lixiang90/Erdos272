module

public import Erdos272.Arithmetic.N158375.UnitFloorData158375

@[expose] public section

namespace JSP233.UnitFloorChecks158375G2
open CoreUnionSource200000 UnitFloorData158375 PrimeTable158375
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : (List.range 16).all (fun i => decide (unitFloor (384+i) ≤ smallUnit (384+i))) = true := by decide +kernel
#print axioms checked00

theorem piece00 {a : ℕ} (hlo : 384 ≤ a) (hhi : a < 400) : unitFloor a ≤ UnitBound a := by
  have hm : a-384 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked00 (a-384) hm)
  have he : 384+(a-384) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece00

theorem checked01 : (List.range 16).all (fun i => decide (unitFloor (400+i) ≤ smallUnit (400+i))) = true := by decide +kernel
#print axioms checked01

theorem piece01 {a : ℕ} (hlo : 400 ≤ a) (hhi : a < 416) : unitFloor a ≤ UnitBound a := by
  have hm : a-400 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked01 (a-400) hm)
  have he : 400+(a-400) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece01

theorem checked02 : (List.range 16).all (fun i => decide (unitFloor (416+i) ≤ smallUnit (416+i))) = true := by decide +kernel
#print axioms checked02

theorem piece02 {a : ℕ} (hlo : 416 ≤ a) (hhi : a < 432) : unitFloor a ≤ UnitBound a := by
  have hm : a-416 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked02 (a-416) hm)
  have he : 416+(a-416) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece02

theorem checked03 : (List.range 16).all (fun i => decide (unitFloor (432+i) ≤ smallUnit (432+i))) = true := by decide +kernel
#print axioms checked03

theorem piece03 {a : ℕ} (hlo : 432 ≤ a) (hhi : a < 448) : unitFloor a ≤ UnitBound a := by
  have hm : a-432 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked03 (a-432) hm)
  have he : 432+(a-432) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece03

theorem checked04 : (List.range 16).all (fun i => decide (unitFloor (448+i) ≤ smallUnit (448+i))) = true := by decide +kernel
#print axioms checked04

theorem piece04 {a : ℕ} (hlo : 448 ≤ a) (hhi : a < 464) : unitFloor a ≤ UnitBound a := by
  have hm : a-448 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked04 (a-448) hm)
  have he : 448+(a-448) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece04

theorem checked05 : (List.range 16).all (fun i => decide (unitFloor (464+i) ≤ smallUnit (464+i))) = true := by decide +kernel
#print axioms checked05

theorem piece05 {a : ℕ} (hlo : 464 ≤ a) (hhi : a < 480) : unitFloor a ≤ UnitBound a := by
  have hm : a-464 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked05 (a-464) hm)
  have he : 464+(a-464) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece05

theorem checked06 : (List.range 16).all (fun i => decide (unitFloor (480+i) ≤ smallUnit (480+i))) = true := by decide +kernel
#print axioms checked06

theorem piece06 {a : ℕ} (hlo : 480 ≤ a) (hhi : a < 496) : unitFloor a ≤ UnitBound a := by
  have hm : a-480 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked06 (a-480) hm)
  have he : 480+(a-480) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece06

theorem checked07 : (List.range 16).all (fun i => decide (unitFloor (496+i) ≤ smallUnit (496+i))) = true := by decide +kernel
#print axioms checked07

theorem piece07 {a : ℕ} (hlo : 496 ≤ a) (hhi : a < 512) : unitFloor a ≤ UnitBound a := by
  have hm : a-496 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked07 (a-496) hm)
  have he : 496+(a-496) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece07

theorem checked08 : (List.range 16).all (fun i => decide (unitFloor (512+i) ≤ smallUnit (512+i))) = true := by decide +kernel
#print axioms checked08

theorem piece08 {a : ℕ} (hlo : 512 ≤ a) (hhi : a < 528) : unitFloor a ≤ UnitBound a := by
  have hm : a-512 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked08 (a-512) hm)
  have he : 512+(a-512) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece08

theorem checked09 : (List.range 16).all (fun i => decide (unitFloor (528+i) ≤ smallUnit (528+i))) = true := by decide +kernel
#print axioms checked09

theorem piece09 {a : ℕ} (hlo : 528 ≤ a) (hhi : a < 544) : unitFloor a ≤ UnitBound a := by
  have hm : a-528 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked09 (a-528) hm)
  have he : 528+(a-528) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece09

theorem checked10 : (List.range 16).all (fun i => decide (unitFloor (544+i) ≤ smallUnit (544+i))) = true := by decide +kernel
#print axioms checked10

theorem piece10 {a : ℕ} (hlo : 544 ≤ a) (hhi : a < 560) : unitFloor a ≤ UnitBound a := by
  have hm : a-544 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked10 (a-544) hm)
  have he : 544+(a-544) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece10

theorem checked11 : (List.range 16).all (fun i => decide (unitFloor (560+i) ≤ smallUnit (560+i))) = true := by decide +kernel
#print axioms checked11

theorem piece11 {a : ℕ} (hlo : 560 ≤ a) (hhi : a < 576) : unitFloor a ≤ UnitBound a := by
  have hm : a-560 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked11 (a-560) hm)
  have he : 560+(a-560) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece11

theorem bound {a : ℕ} (hlo : 384 ≤ a) (hhi : a < 576) : unitFloor a ≤ UnitBound a := by
  by_cases h0 : a < 400
  · exact piece00 (by omega) h0
  by_cases h1 : a < 416
  · exact piece01 (by omega) h1
  by_cases h2 : a < 432
  · exact piece02 (by omega) h2
  by_cases h3 : a < 448
  · exact piece03 (by omega) h3
  by_cases h4 : a < 464
  · exact piece04 (by omega) h4
  by_cases h5 : a < 480
  · exact piece05 (by omega) h5
  by_cases h6 : a < 496
  · exact piece06 (by omega) h6
  by_cases h7 : a < 512
  · exact piece07 (by omega) h7
  by_cases h8 : a < 528
  · exact piece08 (by omega) h8
  by_cases h9 : a < 544
  · exact piece09 (by omega) h9
  by_cases h10 : a < 560
  · exact piece10 (by omega) h10
  exact piece11 (by omega) hhi
#print axioms bound
end JSP233.UnitFloorChecks158375G2
