module

public import Erdos272.Arithmetic.N158375.CleanupChecks158375G00
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G01
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G02
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G03
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G04
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G05
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G06
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G07
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G08
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G09
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G10
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G11
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G12
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G13
public import Erdos272.Arithmetic.N158375.CleanupChecks158375G14
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts158375
open CleanupRows158375
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G00.checked0000)
    (check_sound CleanupChecks158375G00.checked0001)
    rfl rfl rfl)
  (check_sound CleanupChecks158375G00.checked0002)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G00.checked0003)
    (check_sound CleanupChecks158375G00.checked0004)
    rfl rfl rfl)
  (check_sound CleanupChecks158375G00.checked0005)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G00.checked0006)
    (check_sound CleanupChecks158375G00.checked0007)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G01.checked0008)
    (check_sound CleanupChecks158375G01.checked0009)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G01.checked0010)
    (check_sound CleanupChecks158375G01.checked0011)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G01.checked0012)
    (check_sound CleanupChecks158375G01.checked0013)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G01.checked0014)
      (check_sound CleanupChecks158375G01.checked0015)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G02.checked0016)
      (check_sound CleanupChecks158375G02.checked0017)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G02.checked0018)
    (check_sound CleanupChecks158375G02.checked0019)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G02.checked0020)
      (check_sound CleanupChecks158375G02.checked0021)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G02.checked0022)
      (check_sound CleanupChecks158375G02.checked0023)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G03.checked0024)
    (check_sound CleanupChecks158375G03.checked0025)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G03.checked0026)
      (check_sound CleanupChecks158375G03.checked0027)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G03.checked0028)
      (check_sound CleanupChecks158375G03.checked0029)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G03.checked0030)
      (check_sound CleanupChecks158375G03.checked0031)
      rfl rfl rfl)
    (check_sound CleanupChecks158375G04.checked0032)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G04.checked0033)
      (check_sound CleanupChecks158375G04.checked0034)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G04.checked0035)
      (check_sound CleanupChecks158375G04.checked0036)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G04.checked0037)
      (check_sound CleanupChecks158375G04.checked0038)
      rfl rfl rfl)
    (check_sound CleanupChecks158375G04.checked0039)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G05.checked0040)
      (check_sound CleanupChecks158375G05.checked0041)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G05.checked0042)
      (check_sound CleanupChecks158375G05.checked0043)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G05.checked0044)
      (check_sound CleanupChecks158375G05.checked0045)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G05.checked0046)
      (check_sound CleanupChecks158375G05.checked0047)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G06.checked0048)
    (check_sound CleanupChecks158375G06.checked0049)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G06.checked0050)
    (check_sound CleanupChecks158375G06.checked0051)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G06.checked0052)
    (check_sound CleanupChecks158375G06.checked0053)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G06.checked0054)
    (check_sound CleanupChecks158375G06.checked0055)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G07.checked0056)
      (check_sound CleanupChecks158375G07.checked0057)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G07.checked0058)
      (check_sound CleanupChecks158375G07.checked0059)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G07.checked0060)
    (check_sound CleanupChecks158375G07.checked0061)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G07.checked0062)
      (check_sound CleanupChecks158375G07.checked0063)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G08.checked0064)
      (check_sound CleanupChecks158375G08.checked0065)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G08.checked0066)
      (check_sound CleanupChecks158375G08.checked0067)
      rfl rfl rfl)
    (check_sound CleanupChecks158375G08.checked0068)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G08.checked0069)
      (check_sound CleanupChecks158375G08.checked0070)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G08.checked0071)
      (check_sound CleanupChecks158375G09.checked0072)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G09.checked0073)
      (check_sound CleanupChecks158375G09.checked0074)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G09.checked0075)
      (check_sound CleanupChecks158375G09.checked0076)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G09.checked0077)
      (check_sound CleanupChecks158375G09.checked0078)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G09.checked0079)
      (check_sound CleanupChecks158375G10.checked0080)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G10.checked0081)
      (check_sound CleanupChecks158375G10.checked0082)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G10.checked0083)
      (check_sound CleanupChecks158375G10.checked0084)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G10.checked0085)
    (check_sound CleanupChecks158375G10.checked0086)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G10.checked0087)
    (check_sound CleanupChecks158375G11.checked0088)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks158375G11.checked0089)
    (check_sound CleanupChecks158375G11.checked0090)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G11.checked0091)
    (check_sound CleanupChecks158375G11.checked0092)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G11.checked0093)
      (check_sound CleanupChecks158375G11.checked0094)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G11.checked0095)
      (check_sound CleanupChecks158375G12.checked0096)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks158375G12.checked0097)
    (check_sound CleanupChecks158375G12.checked0098)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G12.checked0099)
      (check_sound CleanupChecks158375G12.checked0100)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G12.checked0101)
      (check_sound CleanupChecks158375G12.checked0102)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G12.checked0103)
      (check_sound CleanupChecks158375G13.checked0104)
      rfl rfl rfl)
    (check_sound CleanupChecks158375G13.checked0105)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G13.checked0106)
      (check_sound CleanupChecks158375G13.checked0107)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G13.checked0108)
      (check_sound CleanupChecks158375G13.checked0109)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks158375G13.checked0110)
      (check_sound CleanupChecks158375G13.checked0111)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks158375G14.checked0112)
      (check_sound CleanupChecks158375G14.checked0113)
      rfl rfl rfl)
    rfl rfl rfl)
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
end JSP233.CleanupFacts158375
