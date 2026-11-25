module

public import Erdos272.Arithmetic.N65968.CleanupChecks65968G00
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G01
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G02
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G03
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G04
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G05
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G06
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G07
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G08
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G09
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G10
public import Erdos272.Arithmetic.N65968.CleanupChecks65968G11
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts65968G0
open CleanupRows65968
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
  (check_sound CleanupChecks65968G00.checked0000)
  (check_sound CleanupChecks65968G00.checked0001)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (check_sound CleanupChecks65968G00.checked0002)
  (check_sound CleanupChecks65968G00.checked0003)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (check_sound CleanupChecks65968G00.checked0004)
  (check_sound CleanupChecks65968G00.checked0005)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G00.checked0006)
    (check_sound CleanupChecks65968G00.checked0007)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G00.checked0008)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G00.checked0009)
    (check_sound CleanupChecks65968G00.checked0010)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G00.checked0011)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G00.checked0012)
    (check_sound CleanupChecks65968G00.checked0013)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G00.checked0014)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G00.checked0015)
    (check_sound CleanupChecks65968G00.checked0016)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G00.checked0017)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G00.checked0018)
    (check_sound CleanupChecks65968G00.checked0019)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G01.checked0020)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G01.checked0021)
    (check_sound CleanupChecks65968G01.checked0022)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G01.checked0023)
    (check_sound CleanupChecks65968G01.checked0024)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G01.checked0025)
    (check_sound CleanupChecks65968G01.checked0026)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G01.checked0027)
    (check_sound CleanupChecks65968G01.checked0028)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G01.checked0029)
    (check_sound CleanupChecks65968G01.checked0030)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G01.checked0031)
    (check_sound CleanupChecks65968G01.checked0032)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G01.checked0033)
    (check_sound CleanupChecks65968G01.checked0034)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G01.checked0035)
    (check_sound CleanupChecks65968G01.checked0036)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G01.checked0037)
    (check_sound CleanupChecks65968G01.checked0038)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G01.checked0039)
    (check_sound CleanupChecks65968G02.checked0040)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G02.checked0041)
    (check_sound CleanupChecks65968G02.checked0042)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G02.checked0043)
    (check_sound CleanupChecks65968G02.checked0044)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G02.checked0045)
      (check_sound CleanupChecks65968G02.checked0046)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G02.checked0047)
      (check_sound CleanupChecks65968G02.checked0048)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G02.checked0049)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G02.checked0050)
      (check_sound CleanupChecks65968G02.checked0051)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G02.checked0052)
      (check_sound CleanupChecks65968G02.checked0053)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G02.checked0054)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G02.checked0055)
      (check_sound CleanupChecks65968G02.checked0056)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G02.checked0057)
      (check_sound CleanupChecks65968G02.checked0058)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G02.checked0059)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G03.checked0060)
      (check_sound CleanupChecks65968G03.checked0061)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G03.checked0062)
      (check_sound CleanupChecks65968G03.checked0063)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G03.checked0064)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G03.checked0065)
      (check_sound CleanupChecks65968G03.checked0066)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G03.checked0067)
      (check_sound CleanupChecks65968G03.checked0068)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G03.checked0069)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G03.checked0070)
      (check_sound CleanupChecks65968G03.checked0071)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G03.checked0072)
      (check_sound CleanupChecks65968G03.checked0073)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G03.checked0074)
    (check_sound CleanupChecks65968G03.checked0075)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) :=
  (append_exact
  (check_sound CleanupChecks65968G03.checked0076)
  (check_sound CleanupChecks65968G03.checked0077)
  rfl rfl rfl)
#print axioms fact20

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) :=
  (append_exact
  (check_sound CleanupChecks65968G03.checked0078)
  (check_sound CleanupChecks65968G03.checked0079)
  rfl rfl rfl)
#print axioms fact21

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) :=
  (append_exact
  (check_sound CleanupChecks65968G04.checked0080)
  (check_sound CleanupChecks65968G04.checked0081)
  rfl rfl rfl)
#print axioms fact22

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) :=
  (append_exact
  (check_sound CleanupChecks65968G04.checked0082)
  (check_sound CleanupChecks65968G04.checked0083)
  rfl rfl rfl)
#print axioms fact23

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) :=
  (append_exact
  (check_sound CleanupChecks65968G04.checked0084)
  (check_sound CleanupChecks65968G04.checked0085)
  rfl rfl rfl)
#print axioms fact24

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G04.checked0086)
    (check_sound CleanupChecks65968G04.checked0087)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G04.checked0088)
  rfl rfl rfl)
#print axioms fact25

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G04.checked0089)
    (check_sound CleanupChecks65968G04.checked0090)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G04.checked0091)
  rfl rfl rfl)
#print axioms fact26

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G04.checked0092)
    (check_sound CleanupChecks65968G04.checked0093)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G04.checked0094)
  rfl rfl rfl)
#print axioms fact27

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G04.checked0095)
    (check_sound CleanupChecks65968G04.checked0096)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G04.checked0097)
  rfl rfl rfl)
#print axioms fact28

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G04.checked0098)
    (check_sound CleanupChecks65968G04.checked0099)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G05.checked0100)
  rfl rfl rfl)
#print axioms fact29

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0101)
    (check_sound CleanupChecks65968G05.checked0102)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G05.checked0103)
  rfl rfl rfl)
#print axioms fact30

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0104)
    (check_sound CleanupChecks65968G05.checked0105)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G05.checked0106)
  rfl rfl rfl)
#print axioms fact31

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0107)
    (check_sound CleanupChecks65968G05.checked0108)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G05.checked0109)
  rfl rfl rfl)
#print axioms fact32

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0110)
    (check_sound CleanupChecks65968G05.checked0111)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G05.checked0112)
  rfl rfl rfl)
#print axioms fact33

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0113)
    (check_sound CleanupChecks65968G05.checked0114)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G05.checked0115)
    (check_sound CleanupChecks65968G05.checked0116)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact34

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G05.checked0117)
    (check_sound CleanupChecks65968G05.checked0118)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G05.checked0119)
    (check_sound CleanupChecks65968G06.checked0120)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact35

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G06.checked0121)
    (check_sound CleanupChecks65968G06.checked0122)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G06.checked0123)
    (check_sound CleanupChecks65968G06.checked0124)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact36

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G06.checked0125)
    (check_sound CleanupChecks65968G06.checked0126)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G06.checked0127)
    (check_sound CleanupChecks65968G06.checked0128)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact37

theorem fact38 : ChunkFacts (toRow data38.row) 1 data38.steps (toTotals data38.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G06.checked0129)
    (check_sound CleanupChecks65968G06.checked0130)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G06.checked0131)
    (check_sound CleanupChecks65968G06.checked0132)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact38

theorem fact39 : ChunkFacts (toRow data39.row) 1 data39.steps (toTotals data39.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G06.checked0133)
    (check_sound CleanupChecks65968G06.checked0134)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G06.checked0135)
    (check_sound CleanupChecks65968G06.checked0136)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact39

theorem fact40 : ChunkFacts (toRow data40.row) 1 data40.steps (toTotals data40.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G06.checked0137)
    (check_sound CleanupChecks65968G06.checked0138)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G06.checked0139)
    (check_sound CleanupChecks65968G07.checked0140)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact40

theorem fact41 : ChunkFacts (toRow data41.row) 1 data41.steps (toTotals data41.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G07.checked0141)
    (check_sound CleanupChecks65968G07.checked0142)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G07.checked0143)
    (check_sound CleanupChecks65968G07.checked0144)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact41

theorem fact42 : ChunkFacts (toRow data42.row) 1 data42.steps (toTotals data42.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G07.checked0145)
    (check_sound CleanupChecks65968G07.checked0146)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G07.checked0147)
    (check_sound CleanupChecks65968G07.checked0148)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact42

theorem fact43 : ChunkFacts (toRow data43.row) 1 data43.steps (toTotals data43.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G07.checked0149)
    (check_sound CleanupChecks65968G07.checked0150)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G07.checked0151)
    (check_sound CleanupChecks65968G07.checked0152)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact43

theorem fact44 : ChunkFacts (toRow data44.row) 1 data44.steps (toTotals data44.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G07.checked0153)
      (check_sound CleanupChecks65968G07.checked0154)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G07.checked0155)
      (check_sound CleanupChecks65968G07.checked0156)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G07.checked0157)
  rfl rfl rfl)
#print axioms fact44

theorem fact45 : ChunkFacts (toRow data45.row) 1 data45.steps (toTotals data45.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G07.checked0158)
      (check_sound CleanupChecks65968G07.checked0159)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G08.checked0160)
      (check_sound CleanupChecks65968G08.checked0161)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G08.checked0162)
  rfl rfl rfl)
#print axioms fact45

theorem fact46 : ChunkFacts (toRow data46.row) 1 data46.steps (toTotals data46.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G08.checked0163)
      (check_sound CleanupChecks65968G08.checked0164)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G08.checked0165)
      (check_sound CleanupChecks65968G08.checked0166)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G08.checked0167)
  rfl rfl rfl)
#print axioms fact46

theorem fact47 : ChunkFacts (toRow data47.row) 1 data47.steps (toTotals data47.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G08.checked0168)
      (check_sound CleanupChecks65968G08.checked0169)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G08.checked0170)
      (check_sound CleanupChecks65968G08.checked0171)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G08.checked0172)
  rfl rfl rfl)
#print axioms fact47

theorem fact48 : ChunkFacts (toRow data48.row) 1 data48.steps (toTotals data48.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G08.checked0173)
      (check_sound CleanupChecks65968G08.checked0174)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G08.checked0175)
      (check_sound CleanupChecks65968G08.checked0176)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G08.checked0177)
  rfl rfl rfl)
#print axioms fact48

theorem fact49 : ChunkFacts (toRow data49.row) 1 data49.steps (toTotals data49.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G08.checked0178)
      (check_sound CleanupChecks65968G08.checked0179)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G09.checked0180)
      (check_sound CleanupChecks65968G09.checked0181)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G09.checked0182)
  rfl rfl rfl)
#print axioms fact49

theorem fact50 : ChunkFacts (toRow data50.row) 1 data50.steps (toTotals data50.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G09.checked0183)
      (check_sound CleanupChecks65968G09.checked0184)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G09.checked0185)
      (check_sound CleanupChecks65968G09.checked0186)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G09.checked0187)
  rfl rfl rfl)
#print axioms fact50

theorem fact51 : ChunkFacts (toRow data51.row) 1 data51.steps (toTotals data51.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks65968G09.checked0188)
      (check_sound CleanupChecks65968G09.checked0189)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks65968G09.checked0190)
      (check_sound CleanupChecks65968G09.checked0191)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G09.checked0192)
    (check_sound CleanupChecks65968G09.checked0193)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact51

theorem fact52 : ChunkFacts (toRow data52.row) 1 data52.steps (toTotals data52.total) :=
  (append_exact
  (check_sound CleanupChecks65968G09.checked0194)
  (check_sound CleanupChecks65968G09.checked0195)
  rfl rfl rfl)
#print axioms fact52

theorem fact53 : ChunkFacts (toRow data53.row) 1 data53.steps (toTotals data53.total) :=
  (append_exact
  (check_sound CleanupChecks65968G09.checked0196)
  (check_sound CleanupChecks65968G09.checked0197)
  rfl rfl rfl)
#print axioms fact53

theorem fact54 : ChunkFacts (toRow data54.row) 1 data54.steps (toTotals data54.total) :=
  (append_exact
  (check_sound CleanupChecks65968G09.checked0198)
  (check_sound CleanupChecks65968G09.checked0199)
  rfl rfl rfl)
#print axioms fact54

theorem fact55 : ChunkFacts (toRow data55.row) 1 data55.steps (toTotals data55.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0200)
    (check_sound CleanupChecks65968G10.checked0201)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0202)
  rfl rfl rfl)
#print axioms fact55

theorem fact56 : ChunkFacts (toRow data56.row) 1 data56.steps (toTotals data56.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0203)
    (check_sound CleanupChecks65968G10.checked0204)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0205)
  rfl rfl rfl)
#print axioms fact56

theorem fact57 : ChunkFacts (toRow data57.row) 1 data57.steps (toTotals data57.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0206)
    (check_sound CleanupChecks65968G10.checked0207)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0208)
  rfl rfl rfl)
#print axioms fact57

theorem fact58 : ChunkFacts (toRow data58.row) 1 data58.steps (toTotals data58.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0209)
    (check_sound CleanupChecks65968G10.checked0210)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0211)
  rfl rfl rfl)
#print axioms fact58

theorem fact59 : ChunkFacts (toRow data59.row) 1 data59.steps (toTotals data59.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0212)
    (check_sound CleanupChecks65968G10.checked0213)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0214)
  rfl rfl rfl)
#print axioms fact59

theorem fact60 : ChunkFacts (toRow data60.row) 1 data60.steps (toTotals data60.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0215)
    (check_sound CleanupChecks65968G10.checked0216)
    rfl rfl rfl)
  (check_sound CleanupChecks65968G10.checked0217)
  rfl rfl rfl)
#print axioms fact60

theorem fact61 : ChunkFacts (toRow data61.row) 1 data61.steps (toTotals data61.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G10.checked0218)
    (check_sound CleanupChecks65968G10.checked0219)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G11.checked0220)
    (check_sound CleanupChecks65968G11.checked0221)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact61

theorem fact62 : ChunkFacts (toRow data62.row) 1 data62.steps (toTotals data62.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G11.checked0222)
    (check_sound CleanupChecks65968G11.checked0223)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G11.checked0224)
    (check_sound CleanupChecks65968G11.checked0225)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact62

theorem fact63 : ChunkFacts (toRow data63.row) 1 data63.steps (toTotals data63.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks65968G11.checked0226)
    (check_sound CleanupChecks65968G11.checked0227)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks65968G11.checked0228)
    (check_sound CleanupChecks65968G11.checked0229)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact63

end
end JSP233.CleanupFacts65968G0
