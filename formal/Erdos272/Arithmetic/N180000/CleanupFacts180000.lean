module

public import Erdos272.Arithmetic.N180000.CleanupChecks180000G00
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G01
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G02
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G03
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G04
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G05
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G06
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G07
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G08
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G09
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G10
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G11
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G12
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G13
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G14
public import Erdos272.Arithmetic.N180000.CleanupChecks180000G15
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts180000
open CleanupChecks180000G00 CleanupChecks180000G01 CleanupChecks180000G02 CleanupChecks180000G03 CleanupChecks180000G04 CleanupChecks180000G05 CleanupChecks180000G06 CleanupChecks180000G07 CleanupChecks180000G08 CleanupChecks180000G09 CleanupChecks180000G10 CleanupChecks180000G11 CleanupChecks180000G12 CleanupChecks180000G13 CleanupChecks180000G14 CleanupChecks180000G15
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
open CleanupRows180000
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
set_option maxHeartbeats 0
set_option maxRecDepth 180000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0000)
      (check_sound checked0001)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0002)
      (check_sound checked0003)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0004)
      (check_sound checked0005)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0006)
      (check_sound checked0007)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0008)
        (check_sound checked0009)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0010)
        (check_sound checked0011)
        rfl rfl rfl)
      rfl rfl rfl)
    (check_sound checked0012)
    rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0013)
        (check_sound checked0014)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0015)
        (check_sound checked0016)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0017)
      (check_sound checked0018)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0019)
        (check_sound checked0020)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0021)
        (check_sound checked0022)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0023)
        (check_sound checked0024)
        rfl rfl rfl)
      (check_sound checked0025)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0026)
        (check_sound checked0027)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0028)
        (check_sound checked0029)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0030)
        (check_sound checked0031)
        rfl rfl rfl)
      (check_sound checked0032)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0033)
        (check_sound checked0034)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0035)
        (check_sound checked0036)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0037)
        (check_sound checked0038)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0039)
        (check_sound checked0040)
        rfl rfl rfl)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0041)
      (check_sound checked0042)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0043)
      (check_sound checked0044)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0045)
      (check_sound checked0046)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0047)
      (check_sound checked0048)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0049)
        (check_sound checked0050)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0051)
        (check_sound checked0052)
        rfl rfl rfl)
      rfl rfl rfl)
    (check_sound checked0053)
    rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0054)
        (check_sound checked0055)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0056)
        (check_sound checked0057)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0058)
      (check_sound checked0059)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0060)
        (check_sound checked0061)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0062)
        (check_sound checked0063)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0064)
        (check_sound checked0065)
        rfl rfl rfl)
      (check_sound checked0066)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0067)
        (check_sound checked0068)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0069)
        (check_sound checked0070)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0071)
        (check_sound checked0072)
        rfl rfl rfl)
      (check_sound checked0073)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0074)
        (check_sound checked0075)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0076)
        (check_sound checked0077)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0078)
        (check_sound checked0079)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0080)
        (check_sound checked0081)
        rfl rfl rfl)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0082)
      (check_sound checked0083)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0084)
      (check_sound checked0085)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) := by
  exact (append_exact
    (append_exact
      (check_sound checked0086)
      (check_sound checked0087)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0088)
      (check_sound checked0089)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0090)
        (check_sound checked0091)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0092)
        (check_sound checked0093)
        rfl rfl rfl)
      rfl rfl rfl)
    (check_sound checked0094)
    rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0095)
        (check_sound checked0096)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0097)
        (check_sound checked0098)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (check_sound checked0099)
      (check_sound checked0100)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0101)
        (check_sound checked0102)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0103)
        (check_sound checked0104)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0105)
        (check_sound checked0106)
        rfl rfl rfl)
      (check_sound checked0107)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0108)
        (check_sound checked0109)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0110)
        (check_sound checked0111)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0112)
        (check_sound checked0113)
        rfl rfl rfl)
      (check_sound checked0114)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) := by
  exact (append_exact
    (append_exact
      (append_exact
        (check_sound checked0115)
        (check_sound checked0116)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0117)
        (check_sound checked0118)
        rfl rfl rfl)
      rfl rfl rfl)
    (append_exact
      (append_exact
        (check_sound checked0119)
        (check_sound checked0120)
        rfl rfl rfl)
      (append_exact
        (check_sound checked0121)
        (check_sound checked0122)
        rfl rfl rfl)
      rfl rfl rfl)
    rfl rfl rfl)
#print axioms fact20

theorem all_facts {k : ℕ} (hk : k < 21) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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
  · exact fact20

#print axioms all_facts
end JSP233.CleanupFacts180000
