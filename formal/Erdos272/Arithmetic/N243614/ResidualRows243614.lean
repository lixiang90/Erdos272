module

public import Erdos272.Arithmetic.N243614.CleanupRows243614
public import Erdos272.Arithmetic.N243614.RowGeometry243614
public import Erdos272.Arithmetic.ResidualCeil208

@[expose] public section

namespace JSP233.ResidualRows243614
open CleanupRows243614
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

theorem bound {k : ℕ} (hk : k < 5) : ResidualAggregate208.Price (data k).row.i (ResidualTwoCensus208.H (data k).memberFloor) ≤ ((data k).residualUnits : ℝ)/1000000000000 := by
  have hc : ResidualCeil208.Check (data k).memberFloor (data k).row.i (data k).residualUnits = true := by
    interval_cases k
    · exact checked00
    · exact checked01
    · exact checked02
    · exact checked03
    · exact checked04
  have hb := ResidualCeil208.check_sound hc
  norm_num [ResidualCeil208.B, if_pos (RowGeometry243614.parameters hk).defect_two, ResidualCeil208.Grid] at hb
  exact hb

#print axioms bound
end JSP233.ResidualRows243614
