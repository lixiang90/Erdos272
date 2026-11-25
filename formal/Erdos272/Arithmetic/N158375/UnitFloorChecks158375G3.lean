module

public import Erdos272.Arithmetic.N158375.UnitFloorData158375

@[expose] public section

namespace JSP233.UnitFloorChecks158375G3
open CoreUnionSource200000 UnitFloorData158375 PrimeTable158375
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : (List.range 16).all (fun i => decide (unitFloor (576+i) ≤ smallUnit (576+i))) = true := by decide +kernel
#print axioms checked00

theorem piece00 {a : ℕ} (hlo : 576 ≤ a) (hhi : a < 592) : unitFloor a ≤ UnitBound a := by
  have hm : a-576 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked00 (a-576) hm)
  have he : 576+(a-576) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece00

theorem checked01 : (List.range 16).all (fun i => decide (unitFloor (592+i) ≤ smallUnit (592+i))) = true := by decide +kernel
#print axioms checked01

theorem piece01 {a : ℕ} (hlo : 592 ≤ a) (hhi : a < 608) : unitFloor a ≤ UnitBound a := by
  have hm : a-592 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked01 (a-592) hm)
  have he : 592+(a-592) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece01

theorem checked02 : (List.range 16).all (fun i => decide (unitFloor (608+i) ≤ smallUnit (608+i))) = true := by decide +kernel
#print axioms checked02

theorem piece02 {a : ℕ} (hlo : 608 ≤ a) (hhi : a < 624) : unitFloor a ≤ UnitBound a := by
  have hm : a-608 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked02 (a-608) hm)
  have he : 608+(a-608) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece02

theorem checked03 : (List.range 16).all (fun i => decide (unitFloor (624+i) ≤ smallUnit (624+i))) = true := by decide +kernel
#print axioms checked03

theorem piece03 {a : ℕ} (hlo : 624 ≤ a) (hhi : a < 640) : unitFloor a ≤ UnitBound a := by
  have hm : a-624 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked03 (a-624) hm)
  have he : 624+(a-624) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece03

theorem checked04 : (List.range 16).all (fun i => decide (unitFloor (640+i) ≤ smallUnit (640+i))) = true := by decide +kernel
#print axioms checked04

theorem piece04 {a : ℕ} (hlo : 640 ≤ a) (hhi : a < 656) : unitFloor a ≤ UnitBound a := by
  have hm : a-640 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked04 (a-640) hm)
  have he : 640+(a-640) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece04

theorem checked05 : (List.range 16).all (fun i => decide (unitFloor (656+i) ≤ smallUnit (656+i))) = true := by decide +kernel
#print axioms checked05

theorem piece05 {a : ℕ} (hlo : 656 ≤ a) (hhi : a < 672) : unitFloor a ≤ UnitBound a := by
  have hm : a-656 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked05 (a-656) hm)
  have he : 656+(a-656) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece05

theorem checked06 : (List.range 16).all (fun i => decide (unitFloor (672+i) ≤ smallUnit (672+i))) = true := by decide +kernel
#print axioms checked06

theorem piece06 {a : ℕ} (hlo : 672 ≤ a) (hhi : a < 688) : unitFloor a ≤ UnitBound a := by
  have hm : a-672 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked06 (a-672) hm)
  have he : 672+(a-672) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece06

theorem checked07 : (List.range 16).all (fun i => decide (unitFloor (688+i) ≤ smallUnit (688+i))) = true := by decide +kernel
#print axioms checked07

theorem piece07 {a : ℕ} (hlo : 688 ≤ a) (hhi : a < 704) : unitFloor a ≤ UnitBound a := by
  have hm : a-688 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked07 (a-688) hm)
  have he : 688+(a-688) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece07

theorem checked08 : (List.range 16).all (fun i => decide (unitFloor (704+i) ≤ smallUnit (704+i))) = true := by decide +kernel
#print axioms checked08

theorem piece08 {a : ℕ} (hlo : 704 ≤ a) (hhi : a < 720) : unitFloor a ≤ UnitBound a := by
  have hm : a-704 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked08 (a-704) hm)
  have he : 704+(a-704) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece08

theorem checked09 : (List.range 16).all (fun i => decide (unitFloor (720+i) ≤ smallUnit (720+i))) = true := by decide +kernel
#print axioms checked09

theorem piece09 {a : ℕ} (hlo : 720 ≤ a) (hhi : a < 736) : unitFloor a ≤ UnitBound a := by
  have hm : a-720 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked09 (a-720) hm)
  have he : 720+(a-720) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece09

theorem checked10 : (List.range 16).all (fun i => decide (unitFloor (736+i) ≤ smallUnit (736+i))) = true := by decide +kernel
#print axioms checked10

theorem piece10 {a : ℕ} (hlo : 736 ≤ a) (hhi : a < 752) : unitFloor a ≤ UnitBound a := by
  have hm : a-736 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked10 (a-736) hm)
  have he : 736+(a-736) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece10

theorem checked11 : (List.range 16).all (fun i => decide (unitFloor (752+i) ≤ smallUnit (752+i))) = true := by decide +kernel
#print axioms checked11

theorem piece11 {a : ℕ} (hlo : 752 ≤ a) (hhi : a < 768) : unitFloor a ≤ UnitBound a := by
  have hm : a-752 ∈ List.range 16 := List.mem_range.mpr (by omega)
  have hc := of_decide_eq_true (List.all_eq_true.mp checked11 (a-752) hm)
  have he : 752+(a-752) = a := by omega
  simp only [he] at hc
  exact hc.trans (smallUnit_le (by omega : a ≤ 768))
#print axioms piece11

theorem bound {a : ℕ} (hlo : 576 ≤ a) (hhi : a < 768) : unitFloor a ≤ UnitBound a := by
  by_cases h0 : a < 592
  · exact piece00 (by omega) h0
  by_cases h1 : a < 608
  · exact piece01 (by omega) h1
  by_cases h2 : a < 624
  · exact piece02 (by omega) h2
  by_cases h3 : a < 640
  · exact piece03 (by omega) h3
  by_cases h4 : a < 656
  · exact piece04 (by omega) h4
  by_cases h5 : a < 672
  · exact piece05 (by omega) h5
  by_cases h6 : a < 688
  · exact piece06 (by omega) h6
  by_cases h7 : a < 704
  · exact piece07 (by omega) h7
  by_cases h8 : a < 720
  · exact piece08 (by omega) h8
  by_cases h9 : a < 736
  · exact piece09 (by omega) h9
  by_cases h10 : a < 752
  · exact piece10 (by omega) h10
  exact piece11 (by omega) hhi
#print axioms bound
end JSP233.UnitFloorChecks158375G3
