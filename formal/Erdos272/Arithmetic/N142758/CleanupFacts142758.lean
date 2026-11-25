module

public import Erdos272.Arithmetic.N142758.CleanupChecks142758G00
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G01
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G02
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G03
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G04
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G05
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G06
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G07
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G08
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G09
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G10
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G11
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G12
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G13
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G14
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G15
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G16
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G17
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G18
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G19
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G20
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G21
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G22
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G23
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G24
public import Erdos272.Arithmetic.N142758.CleanupChecks142758G25
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts142758
open CleanupRows142758
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G00.checked0000)
    (check_sound CleanupChecks142758G00.checked0001)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G00.checked0002)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G00.checked0003)
    (check_sound CleanupChecks142758G00.checked0004)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G00.checked0005)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G00.checked0006)
    (check_sound CleanupChecks142758G00.checked0007)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G01.checked0008)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G01.checked0009)
    (check_sound CleanupChecks142758G01.checked0010)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G01.checked0011)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G01.checked0012)
    (check_sound CleanupChecks142758G01.checked0013)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G01.checked0014)
    (check_sound CleanupChecks142758G01.checked0015)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G02.checked0016)
    (check_sound CleanupChecks142758G02.checked0017)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G02.checked0018)
    (check_sound CleanupChecks142758G02.checked0019)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G02.checked0020)
      (check_sound CleanupChecks142758G02.checked0021)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G02.checked0022)
      (check_sound CleanupChecks142758G02.checked0023)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G03.checked0024)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G03.checked0025)
      (check_sound CleanupChecks142758G03.checked0026)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G03.checked0027)
      (check_sound CleanupChecks142758G03.checked0028)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G03.checked0029)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G03.checked0030)
      (check_sound CleanupChecks142758G03.checked0031)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G04.checked0032)
      (check_sound CleanupChecks142758G04.checked0033)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G04.checked0034)
    (check_sound CleanupChecks142758G04.checked0035)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G04.checked0036)
      (check_sound CleanupChecks142758G04.checked0037)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G04.checked0038)
      (check_sound CleanupChecks142758G04.checked0039)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G05.checked0040)
    (check_sound CleanupChecks142758G05.checked0041)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G05.checked0042)
      (check_sound CleanupChecks142758G05.checked0043)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G05.checked0044)
      (check_sound CleanupChecks142758G05.checked0045)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G05.checked0046)
    (check_sound CleanupChecks142758G05.checked0047)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G06.checked0048)
      (check_sound CleanupChecks142758G06.checked0049)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G06.checked0050)
      (check_sound CleanupChecks142758G06.checked0051)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G06.checked0052)
      (check_sound CleanupChecks142758G06.checked0053)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G06.checked0054)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G06.checked0055)
      (check_sound CleanupChecks142758G07.checked0056)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G07.checked0057)
      (check_sound CleanupChecks142758G07.checked0058)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G07.checked0059)
      (check_sound CleanupChecks142758G07.checked0060)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G07.checked0061)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G07.checked0062)
      (check_sound CleanupChecks142758G07.checked0063)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G08.checked0064)
      (check_sound CleanupChecks142758G08.checked0065)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G08.checked0066)
      (check_sound CleanupChecks142758G08.checked0067)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G08.checked0068)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G08.checked0069)
      (check_sound CleanupChecks142758G08.checked0070)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G08.checked0071)
      (check_sound CleanupChecks142758G09.checked0072)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G09.checked0073)
      (check_sound CleanupChecks142758G09.checked0074)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G09.checked0075)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G09.checked0076)
      (check_sound CleanupChecks142758G09.checked0077)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G09.checked0078)
      (check_sound CleanupChecks142758G09.checked0079)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G10.checked0080)
      (check_sound CleanupChecks142758G10.checked0081)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G10.checked0082)
      (check_sound CleanupChecks142758G10.checked0083)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G10.checked0084)
    (check_sound CleanupChecks142758G10.checked0085)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G10.checked0086)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G10.checked0087)
    (check_sound CleanupChecks142758G11.checked0088)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G11.checked0089)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G11.checked0090)
    (check_sound CleanupChecks142758G11.checked0091)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G11.checked0092)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G11.checked0093)
    (check_sound CleanupChecks142758G11.checked0094)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G11.checked0095)
    (check_sound CleanupChecks142758G12.checked0096)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G12.checked0097)
    (check_sound CleanupChecks142758G12.checked0098)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G12.checked0099)
    (check_sound CleanupChecks142758G12.checked0100)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact20

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G12.checked0101)
    (check_sound CleanupChecks142758G12.checked0102)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G12.checked0103)
    (check_sound CleanupChecks142758G13.checked0104)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact21

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G13.checked0105)
      (check_sound CleanupChecks142758G13.checked0106)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G13.checked0107)
      (check_sound CleanupChecks142758G13.checked0108)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G13.checked0109)
  rfl rfl rfl)
#print axioms fact22

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G13.checked0110)
      (check_sound CleanupChecks142758G13.checked0111)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G14.checked0112)
      (check_sound CleanupChecks142758G14.checked0113)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G14.checked0114)
  rfl rfl rfl)
#print axioms fact23

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G14.checked0115)
      (check_sound CleanupChecks142758G14.checked0116)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G14.checked0117)
      (check_sound CleanupChecks142758G14.checked0118)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G14.checked0119)
    (check_sound CleanupChecks142758G15.checked0120)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact24

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G15.checked0121)
      (check_sound CleanupChecks142758G15.checked0122)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G15.checked0123)
      (check_sound CleanupChecks142758G15.checked0124)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G15.checked0125)
    (check_sound CleanupChecks142758G15.checked0126)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact25

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G15.checked0127)
      (check_sound CleanupChecks142758G16.checked0128)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G16.checked0129)
      (check_sound CleanupChecks142758G16.checked0130)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G16.checked0131)
    (check_sound CleanupChecks142758G16.checked0132)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact26

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G16.checked0133)
      (check_sound CleanupChecks142758G16.checked0134)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G16.checked0135)
      (check_sound CleanupChecks142758G17.checked0136)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G17.checked0137)
    (check_sound CleanupChecks142758G17.checked0138)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact27

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G17.checked0139)
      (check_sound CleanupChecks142758G17.checked0140)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G17.checked0141)
      (check_sound CleanupChecks142758G17.checked0142)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G17.checked0143)
    (check_sound CleanupChecks142758G18.checked0144)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact28

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G18.checked0145)
      (check_sound CleanupChecks142758G18.checked0146)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G18.checked0147)
      (check_sound CleanupChecks142758G18.checked0148)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G18.checked0149)
      (check_sound CleanupChecks142758G18.checked0150)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G18.checked0151)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact29

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G19.checked0152)
      (check_sound CleanupChecks142758G19.checked0153)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G19.checked0154)
      (check_sound CleanupChecks142758G19.checked0155)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G19.checked0156)
      (check_sound CleanupChecks142758G19.checked0157)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G19.checked0158)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact30

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G19.checked0159)
      (check_sound CleanupChecks142758G20.checked0160)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G20.checked0161)
      (check_sound CleanupChecks142758G20.checked0162)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G20.checked0163)
      (check_sound CleanupChecks142758G20.checked0164)
      rfl rfl rfl)
    (check_sound CleanupChecks142758G20.checked0165)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact31

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G20.checked0166)
      (check_sound CleanupChecks142758G20.checked0167)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G21.checked0168)
      (check_sound CleanupChecks142758G21.checked0169)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G21.checked0170)
      (check_sound CleanupChecks142758G21.checked0171)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G21.checked0172)
      (check_sound CleanupChecks142758G21.checked0173)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact32

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G21.checked0174)
      (check_sound CleanupChecks142758G21.checked0175)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G22.checked0176)
      (check_sound CleanupChecks142758G22.checked0177)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G22.checked0178)
      (check_sound CleanupChecks142758G22.checked0179)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G22.checked0180)
      (check_sound CleanupChecks142758G22.checked0181)
      rfl rfl rfl)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact33

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G22.checked0182)
    (check_sound CleanupChecks142758G22.checked0183)
    rfl rfl rfl)
  (check_sound CleanupChecks142758G23.checked0184)
  rfl rfl rfl)
#print axioms fact34

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks142758G23.checked0185)
    (check_sound CleanupChecks142758G23.checked0186)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G23.checked0187)
    (check_sound CleanupChecks142758G23.checked0188)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact35

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G23.checked0189)
      (check_sound CleanupChecks142758G23.checked0190)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G23.checked0191)
      (check_sound CleanupChecks142758G24.checked0192)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G24.checked0193)
    (check_sound CleanupChecks142758G24.checked0194)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact36

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks142758G24.checked0195)
      (check_sound CleanupChecks142758G24.checked0196)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks142758G24.checked0197)
      (check_sound CleanupChecks142758G24.checked0198)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks142758G24.checked0199)
    (check_sound CleanupChecks142758G25.checked0200)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact37

theorem all_facts {k : ℕ} (hk : k < 38) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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
  · exact fact21
  · exact fact22
  · exact fact23
  · exact fact24
  · exact fact25
  · exact fact26
  · exact fact27
  · exact fact28
  · exact fact29
  · exact fact30
  · exact fact31
  · exact fact32
  · exact fact33
  · exact fact34
  · exact fact35
  · exact fact36
  · exact fact37

#print axioms all_facts
end JSP233.CleanupFacts142758
