module

public import Erdos272.Arithmetic.N86412.CleanupChecks86412G00
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G01
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G02
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G03
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G04
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G05
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G06
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G07
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G08
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G09
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G10
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G11
public import Erdos272.Arithmetic.N86412.CleanupChecks86412G12
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts86412
open CleanupRows86412
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (check_sound CleanupChecks86412G00.checked0000)
  (check_sound CleanupChecks86412G00.checked0001)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G00.checked0002)
    (check_sound CleanupChecks86412G00.checked0003)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G00.checked0004)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G00.checked0005)
    (check_sound CleanupChecks86412G00.checked0006)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G00.checked0007)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G00.checked0008)
    (check_sound CleanupChecks86412G00.checked0009)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G00.checked0010)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G00.checked0011)
    (check_sound CleanupChecks86412G00.checked0012)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G00.checked0013)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G00.checked0014)
    (check_sound CleanupChecks86412G00.checked0015)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0016)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G01.checked0017)
    (check_sound CleanupChecks86412G01.checked0018)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0019)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G01.checked0020)
    (check_sound CleanupChecks86412G01.checked0021)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0022)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G01.checked0023)
    (check_sound CleanupChecks86412G01.checked0024)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0025)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G01.checked0026)
    (check_sound CleanupChecks86412G01.checked0027)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0028)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G01.checked0029)
    (check_sound CleanupChecks86412G01.checked0030)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G01.checked0031)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G02.checked0032)
    (check_sound CleanupChecks86412G02.checked0033)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G02.checked0034)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G02.checked0035)
    (check_sound CleanupChecks86412G02.checked0036)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G02.checked0037)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G02.checked0038)
    (check_sound CleanupChecks86412G02.checked0039)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G02.checked0040)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G02.checked0041)
    (check_sound CleanupChecks86412G02.checked0042)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G02.checked0043)
    (check_sound CleanupChecks86412G02.checked0044)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G02.checked0045)
    (check_sound CleanupChecks86412G02.checked0046)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G02.checked0047)
    (check_sound CleanupChecks86412G03.checked0048)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G03.checked0049)
    (check_sound CleanupChecks86412G03.checked0050)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G03.checked0051)
    (check_sound CleanupChecks86412G03.checked0052)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G03.checked0053)
    (check_sound CleanupChecks86412G03.checked0054)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G03.checked0055)
    (check_sound CleanupChecks86412G03.checked0056)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G03.checked0057)
    (check_sound CleanupChecks86412G03.checked0058)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G03.checked0059)
    (check_sound CleanupChecks86412G03.checked0060)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G03.checked0061)
    (check_sound CleanupChecks86412G03.checked0062)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G03.checked0063)
    (check_sound CleanupChecks86412G04.checked0064)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G04.checked0065)
    (check_sound CleanupChecks86412G04.checked0066)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G04.checked0067)
    (check_sound CleanupChecks86412G04.checked0068)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact20

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G04.checked0069)
    (check_sound CleanupChecks86412G04.checked0070)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G04.checked0071)
    (check_sound CleanupChecks86412G04.checked0072)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact21

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G04.checked0073)
    (check_sound CleanupChecks86412G04.checked0074)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G04.checked0075)
    (check_sound CleanupChecks86412G04.checked0076)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact22

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G04.checked0077)
    (check_sound CleanupChecks86412G04.checked0078)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G04.checked0079)
    (check_sound CleanupChecks86412G05.checked0080)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact23

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G05.checked0081)
    (check_sound CleanupChecks86412G05.checked0082)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G05.checked0083)
    (check_sound CleanupChecks86412G05.checked0084)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact24

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G05.checked0085)
      (check_sound CleanupChecks86412G05.checked0086)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G05.checked0087)
      (check_sound CleanupChecks86412G05.checked0088)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G05.checked0089)
  rfl rfl rfl)
#print axioms fact25

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G05.checked0090)
      (check_sound CleanupChecks86412G05.checked0091)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G05.checked0092)
      (check_sound CleanupChecks86412G05.checked0093)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G05.checked0094)
  rfl rfl rfl)
#print axioms fact26

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G05.checked0095)
      (check_sound CleanupChecks86412G06.checked0096)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G06.checked0097)
      (check_sound CleanupChecks86412G06.checked0098)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G06.checked0099)
  rfl rfl rfl)
#print axioms fact27

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G06.checked0100)
      (check_sound CleanupChecks86412G06.checked0101)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G06.checked0102)
      (check_sound CleanupChecks86412G06.checked0103)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G06.checked0104)
  rfl rfl rfl)
#print axioms fact28

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G06.checked0105)
      (check_sound CleanupChecks86412G06.checked0106)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G06.checked0107)
      (check_sound CleanupChecks86412G06.checked0108)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G06.checked0109)
  rfl rfl rfl)
#print axioms fact29

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G06.checked0110)
      (check_sound CleanupChecks86412G06.checked0111)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G07.checked0112)
      (check_sound CleanupChecks86412G07.checked0113)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G07.checked0114)
  rfl rfl rfl)
#print axioms fact30

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G07.checked0115)
      (check_sound CleanupChecks86412G07.checked0116)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G07.checked0117)
      (check_sound CleanupChecks86412G07.checked0118)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G07.checked0119)
  rfl rfl rfl)
#print axioms fact31

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G07.checked0120)
      (check_sound CleanupChecks86412G07.checked0121)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G07.checked0122)
      (check_sound CleanupChecks86412G07.checked0123)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G07.checked0124)
  rfl rfl rfl)
#print axioms fact32

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G07.checked0125)
      (check_sound CleanupChecks86412G07.checked0126)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G07.checked0127)
      (check_sound CleanupChecks86412G08.checked0128)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G08.checked0129)
  rfl rfl rfl)
#print axioms fact33

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G08.checked0130)
      (check_sound CleanupChecks86412G08.checked0131)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G08.checked0132)
      (check_sound CleanupChecks86412G08.checked0133)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G08.checked0134)
    (check_sound CleanupChecks86412G08.checked0135)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact34

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G08.checked0136)
      (check_sound CleanupChecks86412G08.checked0137)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G08.checked0138)
      (check_sound CleanupChecks86412G08.checked0139)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G08.checked0140)
    (check_sound CleanupChecks86412G08.checked0141)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact35

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G08.checked0142)
    (check_sound CleanupChecks86412G08.checked0143)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G09.checked0144)
  rfl rfl rfl)
#print axioms fact36

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G09.checked0145)
    (check_sound CleanupChecks86412G09.checked0146)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G09.checked0147)
  rfl rfl rfl)
#print axioms fact37

theorem fact38 : ChunkFacts (toRow data38.row) 1 data38.steps (toTotals data38.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G09.checked0148)
    (check_sound CleanupChecks86412G09.checked0149)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G09.checked0150)
  rfl rfl rfl)
#print axioms fact38

theorem fact39 : ChunkFacts (toRow data39.row) 1 data39.steps (toTotals data39.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G09.checked0151)
    (check_sound CleanupChecks86412G09.checked0152)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G09.checked0153)
  rfl rfl rfl)
#print axioms fact39

theorem fact40 : ChunkFacts (toRow data40.row) 1 data40.steps (toTotals data40.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G09.checked0154)
    (check_sound CleanupChecks86412G09.checked0155)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G09.checked0156)
    (check_sound CleanupChecks86412G09.checked0157)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact40

theorem fact41 : ChunkFacts (toRow data41.row) 1 data41.steps (toTotals data41.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G09.checked0158)
    (check_sound CleanupChecks86412G09.checked0159)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G10.checked0160)
    (check_sound CleanupChecks86412G10.checked0161)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact41

theorem fact42 : ChunkFacts (toRow data42.row) 1 data42.steps (toTotals data42.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G10.checked0162)
    (check_sound CleanupChecks86412G10.checked0163)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks86412G10.checked0164)
    (check_sound CleanupChecks86412G10.checked0165)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact42

theorem fact43 : ChunkFacts (toRow data43.row) 1 data43.steps (toTotals data43.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G10.checked0166)
      (check_sound CleanupChecks86412G10.checked0167)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G10.checked0168)
      (check_sound CleanupChecks86412G10.checked0169)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G10.checked0170)
  rfl rfl rfl)
#print axioms fact43

theorem fact44 : ChunkFacts (toRow data44.row) 1 data44.steps (toTotals data44.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G10.checked0171)
      (check_sound CleanupChecks86412G10.checked0172)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G10.checked0173)
      (check_sound CleanupChecks86412G10.checked0174)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G10.checked0175)
  rfl rfl rfl)
#print axioms fact44

theorem fact45 : ChunkFacts (toRow data45.row) 1 data45.steps (toTotals data45.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G11.checked0176)
      (check_sound CleanupChecks86412G11.checked0177)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G11.checked0178)
      (check_sound CleanupChecks86412G11.checked0179)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G11.checked0180)
  rfl rfl rfl)
#print axioms fact45

theorem fact46 : ChunkFacts (toRow data46.row) 1 data46.steps (toTotals data46.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G11.checked0181)
      (check_sound CleanupChecks86412G11.checked0182)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G11.checked0183)
      (check_sound CleanupChecks86412G11.checked0184)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G11.checked0185)
  rfl rfl rfl)
#print axioms fact46

theorem fact47 : ChunkFacts (toRow data47.row) 1 data47.steps (toTotals data47.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks86412G11.checked0186)
      (check_sound CleanupChecks86412G11.checked0187)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks86412G11.checked0188)
      (check_sound CleanupChecks86412G11.checked0189)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G11.checked0190)
  rfl rfl rfl)
#print axioms fact47

theorem fact48 : ChunkFacts (toRow data48.row) 1 data48.steps (toTotals data48.total) :=
  (append_exact
  (check_sound CleanupChecks86412G11.checked0191)
  (check_sound CleanupChecks86412G12.checked0192)
  rfl rfl rfl)
#print axioms fact48

theorem fact49 : ChunkFacts (toRow data49.row) 1 data49.steps (toTotals data49.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G12.checked0193)
    (check_sound CleanupChecks86412G12.checked0194)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G12.checked0195)
  rfl rfl rfl)
#print axioms fact49

theorem fact50 : ChunkFacts (toRow data50.row) 1 data50.steps (toTotals data50.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks86412G12.checked0196)
    (check_sound CleanupChecks86412G12.checked0197)
    rfl rfl rfl)
  (check_sound CleanupChecks86412G12.checked0198)
  rfl rfl rfl)
#print axioms fact50

theorem all_facts {k : ℕ} (hk : k < 51) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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
  · exact fact38
  · exact fact39
  · exact fact40
  · exact fact41
  · exact fact42
  · exact fact43
  · exact fact44
  · exact fact45
  · exact fact46
  · exact fact47
  · exact fact48
  · exact fact49
  · exact fact50

#print axioms all_facts
end JSP233.CleanupFacts86412
