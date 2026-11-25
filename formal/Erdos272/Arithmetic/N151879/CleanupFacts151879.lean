module

public import Erdos272.Arithmetic.N151879.CleanupChecks151879G00
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G01
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G02
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G03
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G04
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G05
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G06
public import Erdos272.Arithmetic.N151879.CleanupChecks151879G07
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts151879
open CleanupRows151879
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks151879G00.checked0000)
    (check_sound CleanupChecks151879G00.checked0001)
    rfl rfl rfl)
  (check_sound CleanupChecks151879G00.checked0002)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks151879G00.checked0003)
    (check_sound CleanupChecks151879G00.checked0004)
    rfl rfl rfl)
  (check_sound CleanupChecks151879G00.checked0005)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks151879G00.checked0006)
    (check_sound CleanupChecks151879G00.checked0007)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks151879G01.checked0008)
    (check_sound CleanupChecks151879G01.checked0009)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks151879G01.checked0010)
    (check_sound CleanupChecks151879G01.checked0011)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks151879G01.checked0012)
    (check_sound CleanupChecks151879G01.checked0013)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G01.checked0014)
      (check_sound CleanupChecks151879G01.checked0015)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G02.checked0016)
      (check_sound CleanupChecks151879G02.checked0017)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks151879G02.checked0018)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G02.checked0019)
      (check_sound CleanupChecks151879G02.checked0020)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G02.checked0021)
      (check_sound CleanupChecks151879G02.checked0022)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks151879G02.checked0023)
    (check_sound CleanupChecks151879G03.checked0024)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G03.checked0025)
      (check_sound CleanupChecks151879G03.checked0026)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G03.checked0027)
      (check_sound CleanupChecks151879G03.checked0028)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks151879G03.checked0029)
    (check_sound CleanupChecks151879G03.checked0030)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G03.checked0031)
      (check_sound CleanupChecks151879G04.checked0032)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G04.checked0033)
      (check_sound CleanupChecks151879G04.checked0034)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G04.checked0035)
      (check_sound CleanupChecks151879G04.checked0036)
      rfl rfl rfl)
    (check_sound CleanupChecks151879G04.checked0037)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G04.checked0038)
      (check_sound CleanupChecks151879G04.checked0039)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G05.checked0040)
      (check_sound CleanupChecks151879G05.checked0041)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G05.checked0042)
      (check_sound CleanupChecks151879G05.checked0043)
      rfl rfl rfl)
    (check_sound CleanupChecks151879G05.checked0044)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G05.checked0045)
      (check_sound CleanupChecks151879G05.checked0046)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G05.checked0047)
      (check_sound CleanupChecks151879G06.checked0048)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G06.checked0049)
      (check_sound CleanupChecks151879G06.checked0050)
      rfl rfl rfl)
    (check_sound CleanupChecks151879G06.checked0051)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G06.checked0052)
      (check_sound CleanupChecks151879G06.checked0053)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G06.checked0054)
      (check_sound CleanupChecks151879G06.checked0055)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks151879G07.checked0056)
      (check_sound CleanupChecks151879G07.checked0057)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks151879G07.checked0058)
      (check_sound CleanupChecks151879G07.checked0059)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact10

theorem all_facts {k : ℕ} (hk : k < 11) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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

#print axioms all_facts
end JSP233.CleanupFacts151879
