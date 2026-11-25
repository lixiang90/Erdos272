module

public import Erdos272.Arithmetic.N65172.CleanupChecks65172G00
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G01
public import Erdos272.Arithmetic.N65172.CleanupChecks65172G02
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts65172G0
open CleanupRows65172
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (check_sound CleanupChecks65172G00.checked0000)
  (check_sound CleanupChecks65172G00.checked0001)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (check_sound CleanupChecks65172G00.checked0002)
  (check_sound CleanupChecks65172G00.checked0003)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (check_sound CleanupChecks65172G00.checked0004)
  (check_sound CleanupChecks65172G00.checked0005)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (check_sound CleanupChecks65172G00.checked0006)
  (check_sound CleanupChecks65172G00.checked0007)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G00.checked0008)
    (check_sound CleanupChecks65172G00.checked0009)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G00.checked0010)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G00.checked0011)
    (check_sound CleanupChecks65172G00.checked0012)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G00.checked0013)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G00.checked0014)
    (check_sound CleanupChecks65172G00.checked0015)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G00.checked0016)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G00.checked0017)
    (check_sound CleanupChecks65172G00.checked0018)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G00.checked0019)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0020)
    (check_sound CleanupChecks65172G01.checked0021)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G01.checked0022)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0023)
    (check_sound CleanupChecks65172G01.checked0024)
    rfl rfl rfl)
  (check_sound CleanupChecks65172G01.checked0025)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0026)
    (check_sound CleanupChecks65172G01.checked0027)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G01.checked0028)
    (check_sound CleanupChecks65172G01.checked0029)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0030)
    (check_sound CleanupChecks65172G01.checked0031)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G01.checked0032)
    (check_sound CleanupChecks65172G01.checked0033)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0034)
    (check_sound CleanupChecks65172G01.checked0035)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G01.checked0036)
    (check_sound CleanupChecks65172G01.checked0037)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G01.checked0038)
    (check_sound CleanupChecks65172G01.checked0039)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G02.checked0040)
    (check_sound CleanupChecks65172G02.checked0041)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G02.checked0042)
    (check_sound CleanupChecks65172G02.checked0043)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G02.checked0044)
    (check_sound CleanupChecks65172G02.checked0045)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65172G02.checked0046)
    (check_sound CleanupChecks65172G02.checked0047)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65172G02.checked0048)
    (check_sound CleanupChecks65172G02.checked0049)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

end
end JSP233.CleanupFacts65172G0
