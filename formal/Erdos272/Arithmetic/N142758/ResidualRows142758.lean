module

public import Erdos272.Arithmetic.N142758.CleanupRows142758
public import Erdos272.Arithmetic.N142758.RowGeometry142758
public import Erdos272.Arithmetic.ResidualCeil208

@[expose] public section

namespace JSP233.ResidualRows142758
open CleanupRows142758
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

theorem checked09 : ResidualCeil208.Check data09.memberFloor data09.row.i data09.residualUnits = true := by decide +kernel
#print axioms checked09

theorem checked10 : ResidualCeil208.Check data10.memberFloor data10.row.i data10.residualUnits = true := by decide +kernel
#print axioms checked10

theorem checked11 : ResidualCeil208.Check data11.memberFloor data11.row.i data11.residualUnits = true := by decide +kernel
#print axioms checked11

theorem checked12 : ResidualCeil208.Check data12.memberFloor data12.row.i data12.residualUnits = true := by decide +kernel
#print axioms checked12

theorem checked13 : ResidualCeil208.Check data13.memberFloor data13.row.i data13.residualUnits = true := by decide +kernel
#print axioms checked13

theorem checked14 : ResidualCeil208.Check data14.memberFloor data14.row.i data14.residualUnits = true := by decide +kernel
#print axioms checked14

theorem checked15 : ResidualCeil208.Check data15.memberFloor data15.row.i data15.residualUnits = true := by decide +kernel
#print axioms checked15

theorem checked16 : ResidualCeil208.Check data16.memberFloor data16.row.i data16.residualUnits = true := by decide +kernel
#print axioms checked16

theorem checked17 : ResidualCeil208.Check data17.memberFloor data17.row.i data17.residualUnits = true := by decide +kernel
#print axioms checked17

theorem checked18 : ResidualCeil208.Check data18.memberFloor data18.row.i data18.residualUnits = true := by decide +kernel
#print axioms checked18

theorem checked19 : ResidualCeil208.Check data19.memberFloor data19.row.i data19.residualUnits = true := by decide +kernel
#print axioms checked19

theorem checked20 : ResidualCeil208.Check data20.memberFloor data20.row.i data20.residualUnits = true := by decide +kernel
#print axioms checked20

theorem checked21 : ResidualCeil208.Check data21.memberFloor data21.row.i data21.residualUnits = true := by decide +kernel
#print axioms checked21

theorem checked22 : ResidualCeil208.Check data22.memberFloor data22.row.i data22.residualUnits = true := by decide +kernel
#print axioms checked22

theorem checked23 : ResidualCeil208.Check data23.memberFloor data23.row.i data23.residualUnits = true := by decide +kernel
#print axioms checked23

theorem checked24 : ResidualCeil208.Check data24.memberFloor data24.row.i data24.residualUnits = true := by decide +kernel
#print axioms checked24

theorem checked25 : ResidualCeil208.Check data25.memberFloor data25.row.i data25.residualUnits = true := by decide +kernel
#print axioms checked25

theorem checked26 : ResidualCeil208.Check data26.memberFloor data26.row.i data26.residualUnits = true := by decide +kernel
#print axioms checked26

theorem checked27 : ResidualCeil208.Check data27.memberFloor data27.row.i data27.residualUnits = true := by decide +kernel
#print axioms checked27

theorem checked28 : ResidualCeil208.Check data28.memberFloor data28.row.i data28.residualUnits = true := by decide +kernel
#print axioms checked28

theorem checked29 : ResidualCeil208.Check data29.memberFloor data29.row.i data29.residualUnits = true := by decide +kernel
#print axioms checked29

theorem checked30 : ResidualCeil208.Check data30.memberFloor data30.row.i data30.residualUnits = true := by decide +kernel
#print axioms checked30

theorem checked31 : ResidualCeil208.Check data31.memberFloor data31.row.i data31.residualUnits = true := by decide +kernel
#print axioms checked31

theorem checked32 : ResidualCeil208.Check data32.memberFloor data32.row.i data32.residualUnits = true := by decide +kernel
#print axioms checked32

theorem checked33 : ResidualCeil208.Check data33.memberFloor data33.row.i data33.residualUnits = true := by decide +kernel
#print axioms checked33

theorem checked34 : ResidualCeil208.Check data34.memberFloor data34.row.i data34.residualUnits = true := by decide +kernel
#print axioms checked34

theorem checked35 : ResidualCeil208.Check data35.memberFloor data35.row.i data35.residualUnits = true := by decide +kernel
#print axioms checked35

theorem checked36 : ResidualCeil208.Check data36.memberFloor data36.row.i data36.residualUnits = true := by decide +kernel
#print axioms checked36

theorem checked37 : ResidualCeil208.Check data37.memberFloor data37.row.i data37.residualUnits = true := by decide +kernel
#print axioms checked37

theorem bound {k : ℕ} (hk : k < 38) : ResidualAggregate208.Price (data k).row.i (ResidualTwoCensus208.H (data k).memberFloor) ≤ ((data k).residualUnits : ℝ)/1000000000000 := by
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
    · exact checked09
    · exact checked10
    · exact checked11
    · exact checked12
    · exact checked13
    · exact checked14
    · exact checked15
    · exact checked16
    · exact checked17
    · exact checked18
    · exact checked19
    · exact checked20
    · exact checked21
    · exact checked22
    · exact checked23
    · exact checked24
    · exact checked25
    · exact checked26
    · exact checked27
    · exact checked28
    · exact checked29
    · exact checked30
    · exact checked31
    · exact checked32
    · exact checked33
    · exact checked34
    · exact checked35
    · exact checked36
    · exact checked37
  have hb := ResidualCeil208.check_sound hc
  norm_num [ResidualCeil208.B, if_pos (RowGeometry142758.parameters hk).defect_two, ResidualCeil208.Grid] at hb
  exact hb

#print axioms bound
end JSP233.ResidualRows142758
