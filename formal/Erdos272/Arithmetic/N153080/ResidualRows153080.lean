module

public import Erdos272.Arithmetic.N153080.CleanupRows153080
public import Erdos272.Arithmetic.N153080.RowGeometry153080
public import Erdos272.Arithmetic.ResidualCeil208

@[expose] public section

namespace JSP233.ResidualRows153080
open CleanupRows153080
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem checked00 : ResidualCeil208.Check data00.memberFloor data00.row.i data00.residualUnits = true := by decide +kernel
#print axioms checked00

theorem checked01 : ResidualCeil208.Check data01.memberFloor data01.row.i data01.residualUnits = true := by decide +kernel
#print axioms checked01

theorem checked02 : ResidualCeil208.Check data02.memberFloor data02.row.i data02.residualUnits = true := by decide +kernel
#print axioms checked02

theorem checked03 : ResidualCeil208.Check data03.memberFloor data03.row.i data03.residualUnits = true := by decide +kernel
#print axioms checked03

theorem checked04 : ResidualCeil208.Check data04.memberFloor data04.row.i data04.residualUnits = true := by decide +kernel
#print axioms checked04

theorem checked05 : ResidualCeil208.Check data05.memberFloor data05.row.i data05.residualUnits = true := by decide +kernel
#print axioms checked05

theorem checked06 : ResidualCeil208.Check data06.memberFloor data06.row.i data06.residualUnits = true := by decide +kernel
#print axioms checked06

theorem checked07 : ResidualCeil208.Check data07.memberFloor data07.row.i data07.residualUnits = true := by decide +kernel
#print axioms checked07

theorem checked08 : ResidualCeil208.Check data08.memberFloor data08.row.i data08.residualUnits = true := by decide +kernel
#print axioms checked08

theorem bound {k : ℕ} (hk : k < 9) : ResidualAggregate208.Price (data k).row.i (ResidualTwoCensus208.H (data k).memberFloor) ≤ ((data k).residualUnits : ℝ)/1000000000000 := by
  have hc : ResidualCeil208.Check (data k).memberFloor (data k).row.i (data k).residualUnits = true := by
    interval_cases k
    · exact checked00
    · exact checked01
    · exact checked02
    · exact checked03
    · exact checked04
    · exact checked05
    · exact checked06
    · exact checked07
    · exact checked08
  have hb := ResidualCeil208.check_sound hc
  norm_num [ResidualCeil208.B, if_pos (RowGeometry153080.parameters hk).defect_two, ResidualCeil208.Grid] at hb
  exact hb

#print axioms bound
end JSP233.ResidualRows153080
