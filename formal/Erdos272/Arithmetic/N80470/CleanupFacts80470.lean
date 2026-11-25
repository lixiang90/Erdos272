module

public import Erdos272.Arithmetic.N80470.CleanupChecks80470G00
public import Erdos272.Arithmetic.N80470.CleanupChecks80470G01
public import Erdos272.Arithmetic.N80470.CleanupChecks80470G02
public import Erdos272.Arithmetic.N80470.CleanupChecks80470G03
public import Erdos272.Arithmetic.N80470.CleanupChecks80470G04
public import Erdos272.Arithmetic.N80470.CleanupChecks80470G05
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts80470
open CleanupRows80470
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G00.checked0000)
    (check_sound CleanupChecks80470G00.checked0001)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G00.checked0002)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G00.checked0003)
    (check_sound CleanupChecks80470G00.checked0004)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G00.checked0005)
    (check_sound CleanupChecks80470G00.checked0006)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G00.checked0007)
      (check_sound CleanupChecks80470G00.checked0008)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G00.checked0009)
      (check_sound CleanupChecks80470G00.checked0010)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G00.checked0011)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G00.checked0012)
      (check_sound CleanupChecks80470G00.checked0013)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G00.checked0014)
      (check_sound CleanupChecks80470G00.checked0015)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G01.checked0016)
    (check_sound CleanupChecks80470G01.checked0017)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G01.checked0018)
    (check_sound CleanupChecks80470G01.checked0019)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G01.checked0020)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G01.checked0021)
    (check_sound CleanupChecks80470G01.checked0022)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G01.checked0023)
    (check_sound CleanupChecks80470G01.checked0024)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G01.checked0025)
      (check_sound CleanupChecks80470G01.checked0026)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G01.checked0027)
      (check_sound CleanupChecks80470G01.checked0028)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G01.checked0029)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G01.checked0030)
      (check_sound CleanupChecks80470G01.checked0031)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G02.checked0032)
      (check_sound CleanupChecks80470G02.checked0033)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G02.checked0034)
    (check_sound CleanupChecks80470G02.checked0035)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (check_sound CleanupChecks80470G02.checked0036)
  (check_sound CleanupChecks80470G02.checked0037)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G02.checked0038)
    (check_sound CleanupChecks80470G02.checked0039)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G02.checked0040)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G02.checked0041)
    (check_sound CleanupChecks80470G02.checked0042)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G02.checked0043)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G02.checked0044)
    (check_sound CleanupChecks80470G02.checked0045)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G02.checked0046)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G02.checked0047)
    (check_sound CleanupChecks80470G03.checked0048)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G03.checked0049)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G03.checked0050)
    (check_sound CleanupChecks80470G03.checked0051)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G03.checked0052)
    (check_sound CleanupChecks80470G03.checked0053)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G03.checked0054)
    (check_sound CleanupChecks80470G03.checked0055)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G03.checked0056)
    (check_sound CleanupChecks80470G03.checked0057)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks80470G03.checked0058)
    (check_sound CleanupChecks80470G03.checked0059)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks80470G03.checked0060)
    (check_sound CleanupChecks80470G03.checked0061)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G03.checked0062)
      (check_sound CleanupChecks80470G03.checked0063)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G04.checked0064)
      (check_sound CleanupChecks80470G04.checked0065)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G04.checked0066)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G04.checked0067)
      (check_sound CleanupChecks80470G04.checked0068)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G04.checked0069)
      (check_sound CleanupChecks80470G04.checked0070)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G04.checked0071)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G04.checked0072)
      (check_sound CleanupChecks80470G04.checked0073)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G04.checked0074)
      (check_sound CleanupChecks80470G04.checked0075)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G04.checked0076)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks80470G04.checked0077)
      (check_sound CleanupChecks80470G04.checked0078)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks80470G04.checked0079)
      (check_sound CleanupChecks80470G05.checked0080)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks80470G05.checked0081)
  rfl rfl rfl)
#print axioms fact19

theorem all_facts {k : ℕ} (hk : k < 20) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
  interval_cases k
  · exact fact00
  · exact fact01
  · exact fact02
  · exact fact03
  · exact fact04
  · exact fact05
  · exact fact06
  · exact fact07
  · exact fact08
  · exact fact09
  · exact fact10
  · exact fact11
  · exact fact12
  · exact fact13
  · exact fact14
  · exact fact15
  · exact fact16
  · exact fact17
  · exact fact18
  · exact fact19

#print axioms all_facts
end JSP233.CleanupFacts80470
