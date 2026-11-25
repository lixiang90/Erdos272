module

public import Erdos272.Arithmetic.N82427.CleanupChecks82427G00
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G01
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G02
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G03
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G04
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G05
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G06
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G07
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G08
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G09
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G10
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G11
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G12
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G13
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G14
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G15
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G16
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G17
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G18
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G19
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G20
public import Erdos272.Arithmetic.N82427.CleanupChecks82427G21
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts82427
open CleanupRows82427
open CleanupEval208 (ChunkFacts)
open CleanupMachineSound208 (toRow toTotals)
open CleanupSegments208 (append_exact)
open CleanupFastSound208 (check_sound)
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) :=
  (append_exact
  (check_sound CleanupChecks82427G00.checked0000)
  (check_sound CleanupChecks82427G00.checked0001)
  rfl rfl rfl)
#print axioms fact00

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) :=
  (append_exact
  (check_sound CleanupChecks82427G00.checked0002)
  (check_sound CleanupChecks82427G00.checked0003)
  rfl rfl rfl)
#print axioms fact01

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) :=
  (append_exact
  (check_sound CleanupChecks82427G00.checked0004)
  (check_sound CleanupChecks82427G00.checked0005)
  rfl rfl rfl)
#print axioms fact02

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) :=
  (append_exact
  (check_sound CleanupChecks82427G00.checked0006)
  (check_sound CleanupChecks82427G00.checked0007)
  rfl rfl rfl)
#print axioms fact03

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G00.checked0008)
    (check_sound CleanupChecks82427G00.checked0009)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G00.checked0010)
  rfl rfl rfl)
#print axioms fact04

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G00.checked0011)
    (check_sound CleanupChecks82427G00.checked0012)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G00.checked0013)
  rfl rfl rfl)
#print axioms fact05

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G00.checked0014)
    (check_sound CleanupChecks82427G00.checked0015)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0016)
  rfl rfl rfl)
#print axioms fact06

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G01.checked0017)
    (check_sound CleanupChecks82427G01.checked0018)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0019)
  rfl rfl rfl)
#print axioms fact07

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G01.checked0020)
    (check_sound CleanupChecks82427G01.checked0021)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0022)
  rfl rfl rfl)
#print axioms fact08

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G01.checked0023)
    (check_sound CleanupChecks82427G01.checked0024)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0025)
  rfl rfl rfl)
#print axioms fact09

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G01.checked0026)
    (check_sound CleanupChecks82427G01.checked0027)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0028)
  rfl rfl rfl)
#print axioms fact10

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G01.checked0029)
    (check_sound CleanupChecks82427G01.checked0030)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G01.checked0031)
  rfl rfl rfl)
#print axioms fact11

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G02.checked0032)
    (check_sound CleanupChecks82427G02.checked0033)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G02.checked0034)
  rfl rfl rfl)
#print axioms fact12

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G02.checked0035)
    (check_sound CleanupChecks82427G02.checked0036)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G02.checked0037)
  rfl rfl rfl)
#print axioms fact13

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G02.checked0038)
    (check_sound CleanupChecks82427G02.checked0039)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G02.checked0040)
    (check_sound CleanupChecks82427G02.checked0041)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact14

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G02.checked0042)
    (check_sound CleanupChecks82427G02.checked0043)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G02.checked0044)
    (check_sound CleanupChecks82427G02.checked0045)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact15

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G02.checked0046)
    (check_sound CleanupChecks82427G02.checked0047)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G03.checked0048)
    (check_sound CleanupChecks82427G03.checked0049)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact16

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G03.checked0050)
    (check_sound CleanupChecks82427G03.checked0051)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G03.checked0052)
    (check_sound CleanupChecks82427G03.checked0053)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact17

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G03.checked0054)
    (check_sound CleanupChecks82427G03.checked0055)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G03.checked0056)
    (check_sound CleanupChecks82427G03.checked0057)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact18

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G03.checked0058)
    (check_sound CleanupChecks82427G03.checked0059)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G03.checked0060)
    (check_sound CleanupChecks82427G03.checked0061)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact19

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G03.checked0062)
    (check_sound CleanupChecks82427G03.checked0063)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G04.checked0064)
    (check_sound CleanupChecks82427G04.checked0065)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact20

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G04.checked0066)
    (check_sound CleanupChecks82427G04.checked0067)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G04.checked0068)
    (check_sound CleanupChecks82427G04.checked0069)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact21

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G04.checked0070)
    (check_sound CleanupChecks82427G04.checked0071)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G04.checked0072)
    (check_sound CleanupChecks82427G04.checked0073)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact22

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G04.checked0074)
    (check_sound CleanupChecks82427G04.checked0075)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G04.checked0076)
    (check_sound CleanupChecks82427G04.checked0077)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact23

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G04.checked0078)
    (check_sound CleanupChecks82427G04.checked0079)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G05.checked0080)
    (check_sound CleanupChecks82427G05.checked0081)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact24

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G05.checked0082)
    (check_sound CleanupChecks82427G05.checked0083)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G05.checked0084)
    (check_sound CleanupChecks82427G05.checked0085)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact25

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G05.checked0086)
    (check_sound CleanupChecks82427G05.checked0087)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G05.checked0088)
    (check_sound CleanupChecks82427G05.checked0089)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact26

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G05.checked0090)
      (check_sound CleanupChecks82427G05.checked0091)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G05.checked0092)
      (check_sound CleanupChecks82427G05.checked0093)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G05.checked0094)
  rfl rfl rfl)
#print axioms fact27

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G05.checked0095)
      (check_sound CleanupChecks82427G06.checked0096)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G06.checked0097)
      (check_sound CleanupChecks82427G06.checked0098)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G06.checked0099)
  rfl rfl rfl)
#print axioms fact28

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G06.checked0100)
      (check_sound CleanupChecks82427G06.checked0101)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G06.checked0102)
      (check_sound CleanupChecks82427G06.checked0103)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G06.checked0104)
  rfl rfl rfl)
#print axioms fact29

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G06.checked0105)
      (check_sound CleanupChecks82427G06.checked0106)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G06.checked0107)
      (check_sound CleanupChecks82427G06.checked0108)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G06.checked0109)
  rfl rfl rfl)
#print axioms fact30

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G06.checked0110)
      (check_sound CleanupChecks82427G06.checked0111)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G07.checked0112)
      (check_sound CleanupChecks82427G07.checked0113)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G07.checked0114)
  rfl rfl rfl)
#print axioms fact31

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G07.checked0115)
      (check_sound CleanupChecks82427G07.checked0116)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G07.checked0117)
      (check_sound CleanupChecks82427G07.checked0118)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G07.checked0119)
  rfl rfl rfl)
#print axioms fact32

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G07.checked0120)
      (check_sound CleanupChecks82427G07.checked0121)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G07.checked0122)
      (check_sound CleanupChecks82427G07.checked0123)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G07.checked0124)
  rfl rfl rfl)
#print axioms fact33

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G07.checked0125)
      (check_sound CleanupChecks82427G07.checked0126)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G07.checked0127)
      (check_sound CleanupChecks82427G08.checked0128)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G08.checked0129)
  rfl rfl rfl)
#print axioms fact34

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G08.checked0130)
      (check_sound CleanupChecks82427G08.checked0131)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G08.checked0132)
      (check_sound CleanupChecks82427G08.checked0133)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G08.checked0134)
    (check_sound CleanupChecks82427G08.checked0135)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact35

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) :=
  (append_exact
  (check_sound CleanupChecks82427G08.checked0136)
  (check_sound CleanupChecks82427G08.checked0137)
  rfl rfl rfl)
#print axioms fact36

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) :=
  (append_exact
  (check_sound CleanupChecks82427G08.checked0138)
  (check_sound CleanupChecks82427G08.checked0139)
  rfl rfl rfl)
#print axioms fact37

theorem fact38 : ChunkFacts (toRow data38.row) 1 data38.steps (toTotals data38.total) :=
  (append_exact
  (check_sound CleanupChecks82427G08.checked0140)
  (check_sound CleanupChecks82427G08.checked0141)
  rfl rfl rfl)
#print axioms fact38

theorem fact39 : ChunkFacts (toRow data39.row) 1 data39.steps (toTotals data39.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G08.checked0142)
    (check_sound CleanupChecks82427G08.checked0143)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0144)
  rfl rfl rfl)
#print axioms fact39

theorem fact40 : ChunkFacts (toRow data40.row) 1 data40.steps (toTotals data40.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G09.checked0145)
    (check_sound CleanupChecks82427G09.checked0146)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0147)
  rfl rfl rfl)
#print axioms fact40

theorem fact41 : ChunkFacts (toRow data41.row) 1 data41.steps (toTotals data41.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G09.checked0148)
    (check_sound CleanupChecks82427G09.checked0149)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0150)
  rfl rfl rfl)
#print axioms fact41

theorem fact42 : ChunkFacts (toRow data42.row) 1 data42.steps (toTotals data42.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G09.checked0151)
    (check_sound CleanupChecks82427G09.checked0152)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0153)
  rfl rfl rfl)
#print axioms fact42

theorem fact43 : ChunkFacts (toRow data43.row) 1 data43.steps (toTotals data43.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G09.checked0154)
    (check_sound CleanupChecks82427G09.checked0155)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0156)
  rfl rfl rfl)
#print axioms fact43

theorem fact44 : ChunkFacts (toRow data44.row) 1 data44.steps (toTotals data44.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G09.checked0157)
    (check_sound CleanupChecks82427G09.checked0158)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G09.checked0159)
  rfl rfl rfl)
#print axioms fact44

theorem fact45 : ChunkFacts (toRow data45.row) 1 data45.steps (toTotals data45.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0160)
    (check_sound CleanupChecks82427G10.checked0161)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G10.checked0162)
  rfl rfl rfl)
#print axioms fact45

theorem fact46 : ChunkFacts (toRow data46.row) 1 data46.steps (toTotals data46.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0163)
    (check_sound CleanupChecks82427G10.checked0164)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G10.checked0165)
  rfl rfl rfl)
#print axioms fact46

theorem fact47 : ChunkFacts (toRow data47.row) 1 data47.steps (toTotals data47.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0166)
    (check_sound CleanupChecks82427G10.checked0167)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G10.checked0168)
  rfl rfl rfl)
#print axioms fact47

theorem fact48 : ChunkFacts (toRow data48.row) 1 data48.steps (toTotals data48.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0169)
    (check_sound CleanupChecks82427G10.checked0170)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G10.checked0171)
  rfl rfl rfl)
#print axioms fact48

theorem fact49 : ChunkFacts (toRow data49.row) 1 data49.steps (toTotals data49.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0172)
    (check_sound CleanupChecks82427G10.checked0173)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G10.checked0174)
  rfl rfl rfl)
#print axioms fact49

theorem fact50 : ChunkFacts (toRow data50.row) 1 data50.steps (toTotals data50.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G10.checked0175)
    (check_sound CleanupChecks82427G11.checked0176)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G11.checked0177)
  rfl rfl rfl)
#print axioms fact50

theorem fact51 : ChunkFacts (toRow data51.row) 1 data51.steps (toTotals data51.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G11.checked0178)
    (check_sound CleanupChecks82427G11.checked0179)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G11.checked0180)
    (check_sound CleanupChecks82427G11.checked0181)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact51

theorem fact52 : ChunkFacts (toRow data52.row) 1 data52.steps (toTotals data52.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G11.checked0182)
    (check_sound CleanupChecks82427G11.checked0183)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G11.checked0184)
    (check_sound CleanupChecks82427G11.checked0185)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact52

theorem fact53 : ChunkFacts (toRow data53.row) 1 data53.steps (toTotals data53.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G11.checked0186)
    (check_sound CleanupChecks82427G11.checked0187)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G11.checked0188)
    (check_sound CleanupChecks82427G11.checked0189)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact53

theorem fact54 : ChunkFacts (toRow data54.row) 1 data54.steps (toTotals data54.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G11.checked0190)
    (check_sound CleanupChecks82427G11.checked0191)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G12.checked0192)
    (check_sound CleanupChecks82427G12.checked0193)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact54

theorem fact55 : ChunkFacts (toRow data55.row) 1 data55.steps (toTotals data55.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G12.checked0194)
    (check_sound CleanupChecks82427G12.checked0195)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G12.checked0196)
    (check_sound CleanupChecks82427G12.checked0197)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact55

theorem fact56 : ChunkFacts (toRow data56.row) 1 data56.steps (toTotals data56.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G12.checked0198)
    (check_sound CleanupChecks82427G12.checked0199)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G12.checked0200)
    (check_sound CleanupChecks82427G12.checked0201)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact56

theorem fact57 : ChunkFacts (toRow data57.row) 1 data57.steps (toTotals data57.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G12.checked0202)
    (check_sound CleanupChecks82427G12.checked0203)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G12.checked0204)
    (check_sound CleanupChecks82427G12.checked0205)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact57

theorem fact58 : ChunkFacts (toRow data58.row) 1 data58.steps (toTotals data58.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G12.checked0206)
    (check_sound CleanupChecks82427G12.checked0207)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G13.checked0208)
    (check_sound CleanupChecks82427G13.checked0209)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact58

theorem fact59 : ChunkFacts (toRow data59.row) 1 data59.steps (toTotals data59.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G13.checked0210)
    (check_sound CleanupChecks82427G13.checked0211)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G13.checked0212)
    (check_sound CleanupChecks82427G13.checked0213)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact59

theorem fact60 : ChunkFacts (toRow data60.row) 1 data60.steps (toTotals data60.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G13.checked0214)
    (check_sound CleanupChecks82427G13.checked0215)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G13.checked0216)
    (check_sound CleanupChecks82427G13.checked0217)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact60

theorem fact61 : ChunkFacts (toRow data61.row) 1 data61.steps (toTotals data61.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G13.checked0218)
    (check_sound CleanupChecks82427G13.checked0219)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G13.checked0220)
    (check_sound CleanupChecks82427G13.checked0221)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact61

theorem fact62 : ChunkFacts (toRow data62.row) 1 data62.steps (toTotals data62.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G13.checked0222)
    (check_sound CleanupChecks82427G13.checked0223)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G14.checked0224)
    (check_sound CleanupChecks82427G14.checked0225)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact62

theorem fact63 : ChunkFacts (toRow data63.row) 1 data63.steps (toTotals data63.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G14.checked0226)
      (check_sound CleanupChecks82427G14.checked0227)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G14.checked0228)
      (check_sound CleanupChecks82427G14.checked0229)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G14.checked0230)
  rfl rfl rfl)
#print axioms fact63

theorem fact64 : ChunkFacts (toRow data64.row) 1 data64.steps (toTotals data64.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G14.checked0231)
      (check_sound CleanupChecks82427G14.checked0232)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G14.checked0233)
      (check_sound CleanupChecks82427G14.checked0234)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G14.checked0235)
  rfl rfl rfl)
#print axioms fact64

theorem fact65 : ChunkFacts (toRow data65.row) 1 data65.steps (toTotals data65.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G14.checked0236)
      (check_sound CleanupChecks82427G14.checked0237)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G14.checked0238)
      (check_sound CleanupChecks82427G14.checked0239)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G15.checked0240)
  rfl rfl rfl)
#print axioms fact65

theorem fact66 : ChunkFacts (toRow data66.row) 1 data66.steps (toTotals data66.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G15.checked0241)
      (check_sound CleanupChecks82427G15.checked0242)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G15.checked0243)
      (check_sound CleanupChecks82427G15.checked0244)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G15.checked0245)
  rfl rfl rfl)
#print axioms fact66

theorem fact67 : ChunkFacts (toRow data67.row) 1 data67.steps (toTotals data67.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G15.checked0246)
      (check_sound CleanupChecks82427G15.checked0247)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G15.checked0248)
      (check_sound CleanupChecks82427G15.checked0249)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G15.checked0250)
  rfl rfl rfl)
#print axioms fact67

theorem fact68 : ChunkFacts (toRow data68.row) 1 data68.steps (toTotals data68.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G15.checked0251)
      (check_sound CleanupChecks82427G15.checked0252)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G15.checked0253)
      (check_sound CleanupChecks82427G15.checked0254)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G15.checked0255)
  rfl rfl rfl)
#print axioms fact68

theorem fact69 : ChunkFacts (toRow data69.row) 1 data69.steps (toTotals data69.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G16.checked0256)
      (check_sound CleanupChecks82427G16.checked0257)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G16.checked0258)
      (check_sound CleanupChecks82427G16.checked0259)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G16.checked0260)
  rfl rfl rfl)
#print axioms fact69

theorem fact70 : ChunkFacts (toRow data70.row) 1 data70.steps (toTotals data70.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G16.checked0261)
      (check_sound CleanupChecks82427G16.checked0262)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G16.checked0263)
      (check_sound CleanupChecks82427G16.checked0264)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G16.checked0265)
  rfl rfl rfl)
#print axioms fact70

theorem fact71 : ChunkFacts (toRow data71.row) 1 data71.steps (toTotals data71.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G16.checked0266)
      (check_sound CleanupChecks82427G16.checked0267)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G16.checked0268)
      (check_sound CleanupChecks82427G16.checked0269)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G16.checked0270)
  rfl rfl rfl)
#print axioms fact71

theorem fact72 : ChunkFacts (toRow data72.row) 1 data72.steps (toTotals data72.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G16.checked0271)
      (check_sound CleanupChecks82427G17.checked0272)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G17.checked0273)
      (check_sound CleanupChecks82427G17.checked0274)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G17.checked0275)
    (check_sound CleanupChecks82427G17.checked0276)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact72

theorem fact73 : ChunkFacts (toRow data73.row) 1 data73.steps (toTotals data73.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G17.checked0277)
      (check_sound CleanupChecks82427G17.checked0278)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G17.checked0279)
      (check_sound CleanupChecks82427G17.checked0280)
      rfl rfl rfl)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G17.checked0281)
    (check_sound CleanupChecks82427G17.checked0282)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact73

theorem fact74 : ChunkFacts (toRow data74.row) 1 data74.steps (toTotals data74.total) :=
  (append_exact
  (check_sound CleanupChecks82427G17.checked0283)
  (check_sound CleanupChecks82427G17.checked0284)
  rfl rfl rfl)
#print axioms fact74

theorem fact75 : ChunkFacts (toRow data75.row) 1 data75.steps (toTotals data75.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G17.checked0285)
    (check_sound CleanupChecks82427G17.checked0286)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G17.checked0287)
  rfl rfl rfl)
#print axioms fact75

theorem fact76 : ChunkFacts (toRow data76.row) 1 data76.steps (toTotals data76.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G18.checked0288)
    (check_sound CleanupChecks82427G18.checked0289)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G18.checked0290)
  rfl rfl rfl)
#print axioms fact76

theorem fact77 : ChunkFacts (toRow data77.row) 1 data77.steps (toTotals data77.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G18.checked0291)
    (check_sound CleanupChecks82427G18.checked0292)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G18.checked0293)
  rfl rfl rfl)
#print axioms fact77

theorem fact78 : ChunkFacts (toRow data78.row) 1 data78.steps (toTotals data78.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G18.checked0294)
    (check_sound CleanupChecks82427G18.checked0295)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G18.checked0296)
  rfl rfl rfl)
#print axioms fact78

theorem fact79 : ChunkFacts (toRow data79.row) 1 data79.steps (toTotals data79.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G18.checked0297)
    (check_sound CleanupChecks82427G18.checked0298)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G18.checked0299)
    (check_sound CleanupChecks82427G18.checked0300)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact79

theorem fact80 : ChunkFacts (toRow data80.row) 1 data80.steps (toTotals data80.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G18.checked0301)
    (check_sound CleanupChecks82427G18.checked0302)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G18.checked0303)
    (check_sound CleanupChecks82427G19.checked0304)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact80

theorem fact81 : ChunkFacts (toRow data81.row) 1 data81.steps (toTotals data81.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G19.checked0305)
    (check_sound CleanupChecks82427G19.checked0306)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G19.checked0307)
    (check_sound CleanupChecks82427G19.checked0308)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact81

theorem fact82 : ChunkFacts (toRow data82.row) 1 data82.steps (toTotals data82.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G19.checked0309)
    (check_sound CleanupChecks82427G19.checked0310)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G19.checked0311)
    (check_sound CleanupChecks82427G19.checked0312)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact82

theorem fact83 : ChunkFacts (toRow data83.row) 1 data83.steps (toTotals data83.total) :=
  (append_exact
  (append_exact
    (check_sound CleanupChecks82427G19.checked0313)
    (check_sound CleanupChecks82427G19.checked0314)
    rfl rfl rfl)
  (append_exact
    (check_sound CleanupChecks82427G19.checked0315)
    (check_sound CleanupChecks82427G19.checked0316)
    rfl rfl rfl)
  rfl rfl rfl)
#print axioms fact83

theorem fact84 : ChunkFacts (toRow data84.row) 1 data84.steps (toTotals data84.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G19.checked0317)
      (check_sound CleanupChecks82427G19.checked0318)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G19.checked0319)
      (check_sound CleanupChecks82427G20.checked0320)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G20.checked0321)
  rfl rfl rfl)
#print axioms fact84

theorem fact85 : ChunkFacts (toRow data85.row) 1 data85.steps (toTotals data85.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G20.checked0322)
      (check_sound CleanupChecks82427G20.checked0323)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G20.checked0324)
      (check_sound CleanupChecks82427G20.checked0325)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G20.checked0326)
  rfl rfl rfl)
#print axioms fact85

theorem fact86 : ChunkFacts (toRow data86.row) 1 data86.steps (toTotals data86.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G20.checked0327)
      (check_sound CleanupChecks82427G20.checked0328)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G20.checked0329)
      (check_sound CleanupChecks82427G20.checked0330)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G20.checked0331)
  rfl rfl rfl)
#print axioms fact86

theorem fact87 : ChunkFacts (toRow data87.row) 1 data87.steps (toTotals data87.total) :=
  (append_exact
  (append_exact
    (append_exact
      (check_sound CleanupChecks82427G20.checked0332)
      (check_sound CleanupChecks82427G20.checked0333)
      rfl rfl rfl)
    (append_exact
      (check_sound CleanupChecks82427G20.checked0334)
      (check_sound CleanupChecks82427G20.checked0335)
      rfl rfl rfl)
    rfl rfl rfl)
  (check_sound CleanupChecks82427G21.checked0336)
  rfl rfl rfl)
#print axioms fact87

theorem all_facts {k : ℕ} (hk : k < 88) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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
  · exact fact51
  · exact fact52
  · exact fact53
  · exact fact54
  · exact fact55
  · exact fact56
  · exact fact57
  · exact fact58
  · exact fact59
  · exact fact60
  · exact fact61
  · exact fact62
  · exact fact63
  · exact fact64
  · exact fact65
  · exact fact66
  · exact fact67
  · exact fact68
  · exact fact69
  · exact fact70
  · exact fact71
  · exact fact72
  · exact fact73
  · exact fact74
  · exact fact75
  · exact fact76
  · exact fact77
  · exact fact78
  · exact fact79
  · exact fact80
  · exact fact81
  · exact fact82
  · exact fact83
  · exact fact84
  · exact fact85
  · exact fact86
  · exact fact87

#print axioms all_facts
end JSP233.CleanupFacts82427
