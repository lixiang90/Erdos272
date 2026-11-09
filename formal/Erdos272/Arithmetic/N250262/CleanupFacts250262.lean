module

public import Erdos272.Arithmetic.N250262.CleanupChecks250262G00
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G01
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G02
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G03
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G04
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G05
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G06
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G07
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G08
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G09
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G10
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G11
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G12
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G13
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G14
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G15
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G16
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G17
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G18
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G19
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G20
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G21
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G22
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G23
public import Erdos272.Arithmetic.N250262.CleanupChecks250262G24
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts250262
open CleanupRows250262 CleanupEval208 CleanupMachineSound208
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem piece0000 : ChunkFacts (toRow data00.row) 1 512 (toTotals ⟨923184284956352, 1263688813368, 15970544959521, 908477428810199, 1432066608⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0000
#print axioms piece0000

theorem piece0001 : ChunkFacts (toRow data00.row) 513 512 (toTotals ⟨18944320362751, 367063999888, 2130509408173, 17180874954466, 615046443⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0001
#print axioms piece0001

theorem piece0002 : ChunkFacts (toRow data00.row) 1025 512 (toTotals ⟨2114204449041, 146588954110, 733195916642, 1527597486509, 309804508⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0002
#print axioms piece0002

theorem piece0003 : ChunkFacts (toRow data00.row) 1537 512 (toTotals ⟨289640483702, 67312595968, 294243854336, 62709225334, 163465138⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0003
#print axioms piece0003

theorem piece0004 : ChunkFacts (toRow data00.row) 2049 182 (toTotals ⟨85843032653, 23927524348, 104594495096, 5176061905, 57116685⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0004
#print axioms piece0004

theorem join00_00 : ChunkFacts (toRow data00.row) 1 1024 (toTotals ⟨942128605319103, 1630752813256, 18101054367694, 925658303764665, 2047113051⟩) :=
  CleanupSegments208.append_exact piece0000 piece0001 rfl rfl rfl
#print axioms join00_00

theorem join00_01 : ChunkFacts (toRow data00.row) 1025 1024 (toTotals ⟨2403844932743, 213901550078, 1027439770978, 1590306711843, 473269646⟩) :=
  CleanupSegments208.append_exact piece0002 piece0003 rfl rfl rfl
#print axioms join00_01

theorem join00_02 : ChunkFacts (toRow data00.row) 1 2048 (toTotals ⟨944532450251846, 1844654363334, 19128494138672, 927248610476508, 2520382697⟩) :=
  CleanupSegments208.append_exact join00_00 join00_01 rfl rfl rfl
#print axioms join00_02

theorem join00_03 : ChunkFacts (toRow data00.row) 1 2230 (toTotals ⟨944618293284499, 1868581887682, 19233088633768, 927253786538413, 2577499382⟩) :=
  CleanupSegments208.append_exact join00_02 piece0004 rfl rfl rfl
#print axioms join00_03

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) := join00_03
#print axioms fact00

theorem piece0005 : ChunkFacts (toRow data01.row) 1 512 (toTotals ⟨964295382373127, 1951280447209, 16584664066499, 949661998753837, 1581029547⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0005
#print axioms piece0005

theorem piece0006 : ChunkFacts (toRow data01.row) 513 512 (toTotals ⟨24704627262208, 653859641268, 2584978236332, 22773508667144, 739977534⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0006
#print axioms piece0006

theorem piece0007 : ChunkFacts (toRow data01.row) 1025 512 (toTotals ⟨3458019470707, 282927238819, 981694046731, 2759252662795, 425980533⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G00.checked0007
#print axioms piece0007

theorem piece0008 : ChunkFacts (toRow data01.row) 1537 512 (toTotals ⟨362247634607, 104669971211, 321254520652, 145663085166, 187215432⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0008
#print axioms piece0008

theorem piece0009 : ChunkFacts (toRow data01.row) 2049 486 (toTotals ⟨214824751112, 91001084094, 279301783608, 26524051598, 173843279⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0009
#print axioms piece0009

theorem join01_00 : ChunkFacts (toRow data01.row) 1 1024 (toTotals ⟨989000009635335, 2605140088477, 19169642302831, 972435507420981, 2321007081⟩) :=
  CleanupSegments208.append_exact piece0005 piece0006 rfl rfl rfl
#print axioms join01_00

theorem join01_01 : ChunkFacts (toRow data01.row) 1025 1024 (toTotals ⟨3820267105314, 387597210030, 1302948567383, 2904915747961, 613195965⟩) :=
  CleanupSegments208.append_exact piece0007 piece0008 rfl rfl rfl
#print axioms join01_01

theorem join01_02 : ChunkFacts (toRow data01.row) 1 2048 (toTotals ⟨992820276740649, 2992737298507, 20472590870214, 975340423168942, 2934203046⟩) :=
  CleanupSegments208.append_exact join01_00 join01_01 rfl rfl rfl
#print axioms join01_02

theorem join01_03 : ChunkFacts (toRow data01.row) 1 2534 (toTotals ⟨993035101491761, 3083738382601, 20751892653822, 975366947220540, 3108046325⟩) :=
  CleanupSegments208.append_exact join01_02 piece0009 rfl rfl rfl
#print axioms join01_03

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) := join01_03
#print axioms fact01

theorem piece0010 : ChunkFacts (toRow data02.row) 1 512 (toTotals ⟨1002776764326671, 2641047305720, 17135451781366, 988282359851025, 1715080060⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0010
#print axioms piece0010

theorem piece0011 : ChunkFacts (toRow data02.row) 513 512 (toTotals ⟨30975788513473, 982048384060, 3035998894328, 28921838003205, 864639427⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0011
#print axioms piece0011

theorem piece0012 : ChunkFacts (toRow data02.row) 1025 512 (toTotals ⟨4717774103783, 426149765510, 1159619627396, 3984304241897, 517976117⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0012
#print axioms piece0012

theorem piece0013 : ChunkFacts (toRow data02.row) 1537 512 (toTotals ⟨776580390857, 185456241030, 468376447807, 493660184080, 265340222⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0013
#print axioms piece0013

theorem piece0014 : ChunkFacts (toRow data02.row) 2049 512 (toTotals ⟨225134506348, 120346762240, 294243854336, 51237414252, 202666023⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0014
#print axioms piece0014

theorem piece0015 : ChunkFacts (toRow data02.row) 2561 308 (toTotals ⟨114813744601, 72396099160, 177006068624, 10203775137, 122480051⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G01.checked0015
#print axioms piece0015

theorem join02_00 : ChunkFacts (toRow data02.row) 1 1024 (toTotals ⟨1033752552840144, 3623095689780, 20171450675694, 1017204197854230, 2579719487⟩) :=
  CleanupSegments208.append_exact piece0010 piece0011 rfl rfl rfl
#print axioms join02_00

theorem join02_01 : ChunkFacts (toRow data02.row) 1025 1024 (toTotals ⟨5494354494640, 611606006540, 1627996075203, 4477964425977, 783316339⟩) :=
  CleanupSegments208.append_exact piece0012 piece0013 rfl rfl rfl
#print axioms join02_01

theorem join02_02 : ChunkFacts (toRow data02.row) 2049 820 (toTotals ⟨339948250949, 192742861400, 471249922960, 61441189389, 325146074⟩) :=
  CleanupSegments208.append_exact piece0014 piece0015 rfl rfl rfl
#print axioms join02_02

theorem join02_03 : ChunkFacts (toRow data02.row) 1 2048 (toTotals ⟨1039246907334784, 4234701696320, 21799446750897, 1021682162280207, 3363035826⟩) :=
  CleanupSegments208.append_exact join02_00 join02_01 rfl rfl rfl
#print axioms join02_03

theorem join02_04 : ChunkFacts (toRow data02.row) 1 2868 (toTotals ⟨1039586855585733, 4427444557720, 22270696673857, 1021743603469596, 3688181900⟩) :=
  CleanupSegments208.append_exact join02_03 join02_02 rfl rfl rfl
#print axioms join02_04

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) := join02_04
#print axioms fact02

theorem piece0016 : ChunkFacts (toRow data03.row) 1 512 (toTotals ⟨1043880131392841, 3368573916499, 17657504744941, 1029591200564399, 1843636656⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0016
#print axioms piece0016

theorem piece0017 : ChunkFacts (toRow data03.row) 513 512 (toTotals ⟨37241032225713, 1376677240037, 3497019245804, 35120690219946, 993019282⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0017
#print axioms piece0017

theorem piece0018 : ChunkFacts (toRow data03.row) 1025 512 (toTotals ⟨5810947660493, 594570692122, 1325706490488, 5079811862127, 604135975⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0018
#print axioms piece0018

theorem piece0019 : ChunkFacts (toRow data03.row) 1537 512 (toTotals ⟨1466363495954, 315388354765, 674577023837, 1107174826882, 380543577⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0019
#print axioms piece0019

theorem piece0020 : ChunkFacts (toRow data03.row) 2049 512 (toTotals ⟨309784974217, 165189954424, 335621896352, 139353032289, 238830853⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0020
#print axioms piece0020

theorem piece0021 : ChunkFacts (toRow data03.row) 2561 512 (toTotals ⟨184328784610, 144824069632, 294243854336, 34908999906, 235307246⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0021
#print axioms piece0021

theorem piece0022 : ChunkFacts (toRow data03.row) 3073 231 (toTotals ⟨73411238999, 65340547041, 132754551468, 5997234572, 102180520⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0022
#print axioms piece0022

theorem join03_00 : ChunkFacts (toRow data03.row) 1 1024 (toTotals ⟨1081121163618554, 4745251156536, 21154523990745, 1064711890784345, 2836655938⟩) :=
  CleanupSegments208.append_exact piece0016 piece0017 rfl rfl rfl
#print axioms join03_00

theorem join03_01 : ChunkFacts (toRow data03.row) 1025 1024 (toTotals ⟨7277311156447, 909959046887, 2000283514325, 6186986689009, 984679552⟩) :=
  CleanupSegments208.append_exact piece0018 piece0019 rfl rfl rfl
#print axioms join03_01

theorem join03_02 : ChunkFacts (toRow data03.row) 2049 1024 (toTotals ⟨494113758827, 310014024056, 629865750688, 174262032195, 474138099⟩) :=
  CleanupSegments208.append_exact piece0020 piece0021 rfl rfl rfl
#print axioms join03_02

theorem join03_03 : ChunkFacts (toRow data03.row) 1 2048 (toTotals ⟨1088398474775001, 5655210203423, 23154807505070, 1070898877473354, 3821335490⟩) :=
  CleanupSegments208.append_exact join03_00 join03_01 rfl rfl rfl
#print axioms join03_03

theorem join03_04 : ChunkFacts (toRow data03.row) 2049 1255 (toTotals ⟨567524997826, 375354571097, 762620302156, 180259266767, 576318619⟩) :=
  CleanupSegments208.append_exact join03_02 piece0022 rfl rfl rfl
#print axioms join03_04

theorem join03_05 : ChunkFacts (toRow data03.row) 1 3303 (toTotals ⟨1088965999772827, 6030564774520, 23917427807226, 1071079136740121, 4397654109⟩) :=
  CleanupSegments208.append_exact join03_03 join03_04 rfl rfl rfl
#print axioms join03_05

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) := join03_05
#print axioms fact03

theorem piece0023 : ChunkFacts (toRow data04.row) 1 512 (toTotals ⟨1074685280291752, 3931619714460, 18092089125080, 1060524810881132, 1949664569⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G02.checked0023
#print axioms piece0023

theorem piece0024 : ChunkFacts (toRow data04.row) 513 512 (toTotals ⟨41374208121849, 1686328724790, 3817699071427, 39242837775212, 1090527681⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0024
#print axioms piece0024

theorem piece0025 : ChunkFacts (toRow data04.row) 1025 512 (toTotals ⟨6925952846789, 748745060895, 1499494266959, 6175203640725, 682377894⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0025
#print axioms piece0025

theorem piece0026 : ChunkFacts (toRow data04.row) 1537 512 (toTotals ⟨2084522148694, 426145780770, 827560840277, 1683107089187, 472336690⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0026
#print axioms piece0026

theorem piece0027 : ChunkFacts (toRow data04.row) 2049 512 (toTotals ⟨473066120712, 230383095660, 420676760496, 282772455876, 301257652⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0027
#print axioms piece0027

theorem piece0028 : ChunkFacts (toRow data04.row) 2561 512 (toTotals ⟨184328784610, 161142274560, 294243854336, 51227204834, 246843630⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0028
#print axioms piece0028

theorem piece0029 : ChunkFacts (toRow data04.row) 3073 512 (toTotals ⟨156167206682, 161142274560, 294243854336, 23065626906, 267414221⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0029
#print axioms piece0029

theorem piece0030 : ChunkFacts (toRow data04.row) 3585 92 (toTotals ⟨25708740434, 28955252460, 52871942576, 1792050318, 35989105⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0030
#print axioms piece0030

theorem join04_00 : ChunkFacts (toRow data04.row) 1 1024 (toTotals ⟨1116059488413601, 5617948439250, 21909788196507, 1099767648656344, 3040192250⟩) :=
  CleanupSegments208.append_exact piece0023 piece0024 rfl rfl rfl
#print axioms join04_00

theorem join04_01 : ChunkFacts (toRow data04.row) 1025 1024 (toTotals ⟨9010474995483, 1174890841665, 2327055107236, 7858310729912, 1154714584⟩) :=
  CleanupSegments208.append_exact piece0025 piece0026 rfl rfl rfl
#print axioms join04_01

theorem join04_02 : ChunkFacts (toRow data04.row) 2049 1024 (toTotals ⟨657394905322, 391525370220, 714920614832, 333999660710, 548101282⟩) :=
  CleanupSegments208.append_exact piece0027 piece0028 rfl rfl rfl
#print axioms join04_02

theorem join04_03 : ChunkFacts (toRow data04.row) 3073 604 (toTotals ⟨181875947116, 190097527020, 347115796912, 24857677224, 303403326⟩) :=
  CleanupSegments208.append_exact piece0029 piece0030 rfl rfl rfl
#print axioms join04_03

theorem join04_04 : ChunkFacts (toRow data04.row) 1 2048 (toTotals ⟨1125069963409084, 6792839280915, 24236843303743, 1107625959386256, 4194906834⟩) :=
  CleanupSegments208.append_exact join04_00 join04_01 rfl rfl rfl
#print axioms join04_04

theorem join04_05 : ChunkFacts (toRow data04.row) 2049 1628 (toTotals ⟨839270852438, 581622897240, 1062036411744, 358857337934, 851504608⟩) :=
  CleanupSegments208.append_exact join04_02 join04_03 rfl rfl rfl
#print axioms join04_05

theorem join04_06 : ChunkFacts (toRow data04.row) 1 3676 (toTotals ⟨1125909234261522, 7374462178155, 25298879715487, 1107984816724190, 5046411442⟩) :=
  CleanupSegments208.append_exact join04_04 join04_05 rfl rfl rfl
#print axioms join04_06

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) := join04_06
#print axioms fact04

theorem piece0031 : ChunkFacts (toRow data05.row) 1 512 (toTotals ⟨1120018212015039, 4429340908080, 18569890571416, 1105877662351703, 2040367767⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G03.checked0031
#print axioms piece0031

theorem piece0032 : ChunkFacts (toRow data05.row) 513 512 (toTotals ⟨45819618623075, 1969160350190, 4116425546978, 43672353426287, 1173625607⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0032
#print axioms piece0032

theorem piece0033 : ChunkFacts (toRow data05.row) 1025 512 (toTotals ⟨8070803262066, 897381758900, 1669374117243, 7298810903723, 757425529⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0033
#print axioms piece0033

theorem piece0034 : ChunkFacts (toRow data05.row) 1537 512 (toTotals ⟨2646071499630, 531994997446, 963533683892, 2214532813184, 555466548⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0034
#print axioms piece0034

theorem piece0035 : ChunkFacts (toRow data05.row) 2049 512 (toTotals ⟨601375802327, 288516701352, 489640163856, 400252339823, 357417520⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0035
#print axioms piece0035

theorem piece0036 : ChunkFacts (toRow data05.row) 2561 512 (toTotals ⟨232842691827, 190651294438, 323553300764, 99940685501, 273055106⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0036
#print axioms piece0036

theorem piece0037 : ChunkFacts (toRow data05.row) 3073 512 (toTotals ⟨156167206682, 173380928512, 294243854336, 35304280858, 277639373⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0037
#print axioms piece0037

theorem piece0038 : ChunkFacts (toRow data05.row) 3585 431 (toTotals ⟨115259954740, 145951523806, 247693557068, 13517921478, 232589956⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0038
#print axioms piece0038

theorem join05_00 : ChunkFacts (toRow data05.row) 1 1024 (toTotals ⟨1165837830638114, 6398501258270, 22686316118394, 1149550015777990, 3213993374⟩) :=
  CleanupSegments208.append_exact piece0031 piece0032 rfl rfl rfl
#print axioms join05_00

theorem join05_01 : ChunkFacts (toRow data05.row) 1025 1024 (toTotals ⟨10716874761696, 1429376756346, 2632907801135, 9513343716907, 1312892077⟩) :=
  CleanupSegments208.append_exact piece0033 piece0034 rfl rfl rfl
#print axioms join05_01

theorem join05_02 : ChunkFacts (toRow data05.row) 2049 1024 (toTotals ⟨834218494154, 479167995790, 813193464620, 500193025324, 630472626⟩) :=
  CleanupSegments208.append_exact piece0035 piece0036 rfl rfl rfl
#print axioms join05_02

theorem join05_03 : ChunkFacts (toRow data05.row) 3073 943 (toTotals ⟨271427161422, 319332452318, 541937411404, 48822202336, 510229329⟩) :=
  CleanupSegments208.append_exact piece0037 piece0038 rfl rfl rfl
#print axioms join05_03

theorem join05_04 : ChunkFacts (toRow data05.row) 1 2048 (toTotals ⟨1176554705399810, 7827878014616, 25319223919529, 1159063359494897, 4526885451⟩) :=
  CleanupSegments208.append_exact join05_00 join05_01 rfl rfl rfl
#print axioms join05_04

theorem join05_05 : ChunkFacts (toRow data05.row) 2049 1967 (toTotals ⟨1105645655576, 798500448108, 1355130876024, 549015227660, 1140701955⟩) :=
  CleanupSegments208.append_exact join05_02 join05_03 rfl rfl rfl
#print axioms join05_05

theorem join05_06 : ChunkFacts (toRow data05.row) 1 4015 (toTotals ⟨1177660351055386, 8626378462724, 26674354795553, 1159612374722557, 5667587406⟩) :=
  CleanupSegments208.append_exact join05_04 join05_05 rfl rfl rfl
#print axioms join05_06

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) := join05_06
#print axioms fact05

theorem piece0039 : ChunkFacts (toRow data06.row) 1 512 (toTotals ⟨1156138661152583, 4953360055098, 19022980131515, 1142069041076166, 2151342581⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G04.checked0039
#print axioms piece0039

theorem piece0040 : ChunkFacts (toRow data06.row) 513 512 (toTotals ⟨49897340654431, 2276740184880, 4418715131701, 47755365707610, 1272500436⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0040
#print axioms piece0040

theorem piece0041 : ChunkFacts (toRow data06.row) 1025 512 (toTotals ⟨9317290405163, 1077463667112, 1872471340148, 8522282732127, 846016979⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0041
#print axioms piece0041

theorem piece0042 : ChunkFacts (toRow data06.row) 1537 512 (toTotals ⟨3310655658958, 644593001388, 1094219333249, 2861029327097, 639319100⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0042
#print axioms piece0042

theorem piece0043 : ChunkFacts (toRow data06.row) 2049 512 (toTotals ⟨826415410049, 371239163904, 588487708672, 609166865281, 430019697⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0043
#print axioms piece0043

theorem piece0044 : ChunkFacts (toRow data06.row) 2561 512 (toTotals ⟨365728112210, 257402154660, 408033469880, 215096796990, 343955688⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0044
#print axioms piece0044

theorem piece0045 : ChunkFacts (toRow data06.row) 3073 512 (toTotals ⟨156167206682, 185619581952, 294243854336, 47542934298, 287864525⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0045
#print axioms piece0045

theorem piece0046 : ChunkFacts (toRow data06.row) 3585 512 (toTotals ⟨135553731532, 185619581952, 294243854336, 26929459148, 311584561⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0046
#print axioms piece0046

theorem piece0047 : ChunkFacts (toRow data06.row) 4097 327 (toTotals ⟨78101034559, 118550006442, 187925274156, 8725766845, 187225280⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G05.checked0047
#print axioms piece0047

theorem join06_00 : ChunkFacts (toRow data06.row) 1 1024 (toTotals ⟨1206036001807014, 7230100239978, 23441695263216, 1189824406783776, 3423843017⟩) :=
  CleanupSegments208.append_exact piece0039 piece0040 rfl rfl rfl
#print axioms join06_00

theorem join06_01 : ChunkFacts (toRow data06.row) 1025 1024 (toTotals ⟨12627946064121, 1722056668500, 2966690673397, 11383312059224, 1485336079⟩) :=
  CleanupSegments208.append_exact piece0041 piece0042 rfl rfl rfl
#print axioms join06_01

theorem join06_02 : ChunkFacts (toRow data06.row) 2049 1024 (toTotals ⟨1192143522259, 628641318564, 996521178552, 824263662271, 773975385⟩) :=
  CleanupSegments208.append_exact piece0043 piece0044 rfl rfl rfl
#print axioms join06_02

theorem join06_03 : ChunkFacts (toRow data06.row) 3073 1024 (toTotals ⟨291720938214, 371239163904, 588487708672, 74472393446, 599449086⟩) :=
  CleanupSegments208.append_exact piece0045 piece0046 rfl rfl rfl
#print axioms join06_03

theorem join06_04 : ChunkFacts (toRow data06.row) 1 2048 (toTotals ⟨1218663947871135, 8952156908478, 26408385936613, 1201207718843000, 4909179096⟩) :=
  CleanupSegments208.append_exact join06_00 join06_01 rfl rfl rfl
#print axioms join06_04

theorem join06_05 : ChunkFacts (toRow data06.row) 2049 2048 (toTotals ⟨1483864460473, 999880482468, 1585008887224, 898736055717, 1373424471⟩) :=
  CleanupSegments208.append_exact join06_02 join06_03 rfl rfl rfl
#print axioms join06_05

theorem join06_06 : ChunkFacts (toRow data06.row) 1 4096 (toTotals ⟨1220147812331608, 9952037390946, 27993394823837, 1202106454898717, 6282603567⟩) :=
  CleanupSegments208.append_exact join06_04 join06_05 rfl rfl rfl
#print axioms join06_06

theorem join06_07 : ChunkFacts (toRow data06.row) 1 4423 (toTotals ⟨1220225913366167, 10070587397388, 28181320097993, 1202115180665562, 6469828847⟩) :=
  CleanupSegments208.append_exact join06_06 piece0047 rfl rfl rfl
#print axioms join06_07

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) := join06_07
#print axioms fact06

theorem piece0048 : ChunkFacts (toRow data07.row) 1 512 (toTotals ⟨915960063117087, 1263818495016, 15878454216317, 901345427395786, 1500575806⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0048
#print axioms piece0048

theorem piece0049 : ChunkFacts (toRow data07.row) 513 512 (toTotals ⟨19779566179502, 375289742748, 2168230573844, 17986625348406, 653355771⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0049
#print axioms piece0049

theorem piece0050 : ChunkFacts (toRow data07.row) 1025 512 (toTotals ⟨2268967606375, 152538802068, 758557833224, 1662948575219, 336493089⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0050
#print axioms piece0050

theorem piece0051 : ChunkFacts (toRow data07.row) 1537 512 (toTotals ⟨289562326390, 66695018496, 289053130752, 67204214134, 169500973⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0051
#print axioms piece0051

theorem piece0052 : ChunkFacts (toRow data07.row) 2049 229 (toTotals ⟨106847894863, 29830389132, 129283529184, 7394754811, 75312051⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0052
#print axioms piece0052

theorem join07_00 : ChunkFacts (toRow data07.row) 1 1024 (toTotals ⟨935739629296589, 1639108237764, 18046684790161, 919332052744192, 2153931577⟩) :=
  CleanupSegments208.append_exact piece0048 piece0049 rfl rfl rfl
#print axioms join07_00

theorem join07_01 : ChunkFacts (toRow data07.row) 1025 1024 (toTotals ⟨2558529932765, 219233820564, 1047610963976, 1730152789353, 505994062⟩) :=
  CleanupSegments208.append_exact piece0050 piece0051 rfl rfl rfl
#print axioms join07_01

theorem join07_02 : ChunkFacts (toRow data07.row) 1 2048 (toTotals ⟨938298159229354, 1858342058328, 19094295754137, 921062205533545, 2659925639⟩) :=
  CleanupSegments208.append_exact join07_00 join07_01 rfl rfl rfl
#print axioms join07_02

theorem join07_03 : ChunkFacts (toRow data07.row) 1 2277 (toTotals ⟨938405007124217, 1888172447460, 19223579283321, 921069600288356, 2735237690⟩) :=
  CleanupSegments208.append_exact join07_02 piece0052 rfl rfl rfl
#print axioms join07_03

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) := join07_03
#print axioms fact07

theorem piece0053 : ChunkFacts (toRow data08.row) 1 512 (toTotals ⟨955860212385565, 1887138001600, 16457287391177, 941290062995988, 1638527294⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0053
#print axioms piece0053

theorem piece0054 : ChunkFacts (toRow data08.row) 513 512 (toTotals ⟨25217340682160, 636188793860, 2587508162029, 23266021313991, 772493155⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0054
#print axioms piece0054

theorem piece0055 : ChunkFacts (toRow data08.row) 1025 512 (toTotals ⟨3508037579906, 275867883440, 980144569984, 2803760893362, 446476241⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G06.checked0055
#print axioms piece0055

theorem piece0056 : ChunkFacts (toRow data08.row) 1537 512 (toTotals ⟨370216905773, 101379646460, 318520786776, 153075765457, 192956508⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0056
#print axioms piece0056

theorem piece0057 : ChunkFacts (toRow data08.row) 2049 508 (toTotals ⟨223477607528, 91475773360, 286794903168, 28158477720, 187468161⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0057
#print axioms piece0057

theorem join08_00 : ChunkFacts (toRow data08.row) 1 1024 (toTotals ⟨981077553067725, 2523326795460, 19044795553206, 964556084309979, 2411020449⟩) :=
  CleanupSegments208.append_exact piece0053 piece0054 rfl rfl rfl
#print axioms join08_00

theorem join08_01 : ChunkFacts (toRow data08.row) 1025 1024 (toTotals ⟨3878254485679, 377247529900, 1298665356760, 2956836658819, 639432749⟩) :=
  CleanupSegments208.append_exact piece0055 piece0056 rfl rfl rfl
#print axioms join08_01

theorem join08_02 : ChunkFacts (toRow data08.row) 1 2048 (toTotals ⟨984955807553404, 2900574325360, 20343460909966, 967512920968798, 3050453198⟩) :=
  CleanupSegments208.append_exact join08_00 join08_01 rfl rfl rfl
#print axioms join08_02

theorem join08_03 : ChunkFacts (toRow data08.row) 1 2556 (toTotals ⟨985179285160932, 2992050098720, 20630255813134, 967541079446518, 3237921359⟩) :=
  CleanupSegments208.append_exact join08_02 piece0057 rfl rfl rfl
#print axioms join08_03

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) := join08_03
#print axioms fact08

theorem piece0058 : ChunkFacts (toRow data09.row) 1 512 (toTotals ⟨995091425993834, 2508357953280, 17006826335913, 980592957611201, 1771501511⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0058
#print axioms piece0058

theorem piece0059 : ChunkFacts (toRow data09.row) 513 512 (toTotals ⟨31275916474592, 932190079200, 3017501261507, 29190605292285, 895413736⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0059
#print axioms piece0059

theorem piece0060 : ChunkFacts (toRow data09.row) 1025 512 (toTotals ⟨4634419443209, 399541778880, 1130316704320, 3903644517769, 527741762⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0060
#print axioms piece0060

theorem piece0061 : ChunkFacts (toRow data09.row) 1537 512 (toTotals ⟨816118902285, 177771648000, 471002807536, 522887742749, 275704493⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0061
#print axioms piece0061

theorem piece0062 : ChunkFacts (toRow data09.row) 2049 512 (toTotals ⟨225056349036, 113773854720, 289053130752, 49777073004, 206601853⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0062
#print axioms piece0062

theorem piece0063 : ChunkFacts (toRow data09.row) 2561 292 (toTotals ⟨109111985261, 64886651520, 164850613632, 9148023149, 118200065⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G07.checked0063
#print axioms piece0063

theorem join09_00 : ChunkFacts (toRow data09.row) 1 1024 (toTotals ⟨1026367342468426, 3440548032480, 20024327597420, 1009783562903486, 2666915247⟩) :=
  CleanupSegments208.append_exact piece0058 piece0059 rfl rfl rfl
#print axioms join09_00

theorem join09_01 : ChunkFacts (toRow data09.row) 1025 1024 (toTotals ⟨5450538345494, 577313426880, 1601319511856, 4426532260518, 803446255⟩) :=
  CleanupSegments208.append_exact piece0060 piece0061 rfl rfl rfl
#print axioms join09_01

theorem join09_02 : ChunkFacts (toRow data09.row) 2049 804 (toTotals ⟨334168334297, 178660506240, 453903744384, 58925096153, 324801918⟩) :=
  CleanupSegments208.append_exact piece0062 piece0063 rfl rfl rfl
#print axioms join09_02

theorem join09_03 : ChunkFacts (toRow data09.row) 1 2048 (toTotals ⟨1031817880813920, 4017861459360, 21625647109276, 1014210095164004, 3470361502⟩) :=
  CleanupSegments208.append_exact join09_00 join09_01 rfl rfl rfl
#print axioms join09_03

theorem join09_04 : ChunkFacts (toRow data09.row) 1 2852 (toTotals ⟨1032152049148217, 4196521965600, 22079550853660, 1014269020260157, 3795163420⟩) :=
  CleanupSegments208.append_exact join09_03 join09_02 rfl rfl rfl
#print axioms join09_04

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) := join09_04
#print axioms fact09

theorem piece0064 : ChunkFacts (toRow data10.row) 1 512 (toTotals ⟨1019751124924110, 3031497000940, 17330144011553, 1005452477913497, 1873435501⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0064
#print axioms piece0064

theorem piece0065 : ChunkFacts (toRow data10.row) 513 512 (toTotals ⟨35806956228931, 1225781487575, 3351298293786, 33681439422720, 997711831⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0065
#print axioms piece0065

theorem piece0066 : ChunkFacts (toRow data10.row) 1025 512 (toTotals ⟨5544869740373, 529912762110, 1266939473158, 4807843029325, 599368742⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0066
#print axioms piece0066

theorem piece0067 : ChunkFacts (toRow data10.row) 1537 512 (toTotals ⟨1316536285231, 273293258335, 625307645976, 964521897590, 366517178⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0067
#print axioms piece0067

theorem piece0068 : ChunkFacts (toRow data10.row) 2049 512 (toTotals ⟨265473627235, 142247968590, 308248065216, 99473530609, 228064859⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0068
#print axioms piece0068

theorem piece0069 : ChunkFacts (toRow data10.row) 2561 512 (toTotals ⟨184250627298, 133390036480, 289053130752, 28587533026, 236100878⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0069
#print axioms piece0069

theorem piece0070 : ChunkFacts (toRow data10.row) 3073 116 (toTotals ⟨37503453232, 30221180140, 65488599936, 2236033436, 46840665⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0070
#print axioms piece0070

theorem join10_00 : ChunkFacts (toRow data10.row) 1 1024 (toTotals ⟨1055558081153041, 4257278488515, 20681442305339, 1039133917336217, 2871147332⟩) :=
  CleanupSegments208.append_exact piece0064 piece0065 rfl rfl rfl
#print axioms join10_00

theorem join10_01 : ChunkFacts (toRow data10.row) 1025 1024 (toTotals ⟨6861406025604, 803206020445, 1892247119134, 5772364926915, 965885920⟩) :=
  CleanupSegments208.append_exact piece0066 piece0067 rfl rfl rfl
#print axioms join10_01

theorem join10_02 : ChunkFacts (toRow data10.row) 2049 1024 (toTotals ⟨449724254533, 275638005070, 597301195968, 128061063635, 464165737⟩) :=
  CleanupSegments208.append_exact piece0068 piece0069 rfl rfl rfl
#print axioms join10_02

theorem join10_03 : ChunkFacts (toRow data10.row) 1 2048 (toTotals ⟨1062419487178645, 5060484508960, 22573689424473, 1044906282263132, 3837033252⟩) :=
  CleanupSegments208.append_exact join10_00 join10_01 rfl rfl rfl
#print axioms join10_03

theorem join10_04 : ChunkFacts (toRow data10.row) 2049 1140 (toTotals ⟨487227707765, 305859185210, 662789795904, 130297097071, 511006402⟩) :=
  CleanupSegments208.append_exact join10_02 piece0070 rfl rfl rfl
#print axioms join10_04

theorem join10_05 : ChunkFacts (toRow data10.row) 1 3188 (toTotals ⟨1062906714886410, 5366343694170, 23236479220377, 1045036579360203, 4348039654⟩) :=
  CleanupSegments208.append_exact join10_03 join10_04 rfl rfl rfl
#print axioms join10_05

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) := join10_05
#print axioms fact10

theorem piece0071 : ChunkFacts (toRow data11.row) 1 512 (toTotals ⟨1071390461583569, 3741779020670, 17953732157595, 1057178508446644, 1992487706⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G08.checked0071
#print axioms piece0071

theorem piece0072 : ChunkFacts (toRow data11.row) 513 512 (toTotals ⟨40988866361569, 1582658069920, 3724282216481, 38847242215008, 1106621807⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0072
#print axioms piece0072

theorem piece0073 : ChunkFacts (toRow data11.row) 1025 512 (toTotals ⟨6796188358351, 699585072070, 1457176697570, 6038596732851, 689468338⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0073
#print axioms piece0073

theorem piece0074 : ChunkFacts (toRow data11.row) 1537 512 (toTotals ⟨2012664705872, 395066836940, 794062189024, 1613669353788, 470831110⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0074
#print axioms piece0074

theorem piece0075 : ChunkFacts (toRow data11.row) 2049 512 (toTotals ⟨445788352807, 211280070890, 399141725472, 257926698225, 297167889⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0075
#print axioms piece0075

theorem piece0076 : ChunkFacts (toRow data11.row) 2561 512 (toTotals ⟨184250627298, 153006218240, 289053130752, 48203714786, 250521358⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0076
#print axioms piece0076

theorem piece0077 : ChunkFacts (toRow data11.row) 3073 512 (toTotals ⟨156089049370, 153006218240, 289053130752, 20042136858, 268815641⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0077
#print axioms piece0077

theorem piece0078 : ChunkFacts (toRow data11.row) 3585 29 (toTotals ⟨8168944688, 8666367830, 16372149984, 463162534, 4809708⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0078
#print axioms piece0078

theorem join11_00 : ChunkFacts (toRow data11.row) 1 1024 (toTotals ⟨1112379327945138, 5324437090590, 21678014374076, 1096025750661652, 3099109513⟩) :=
  CleanupSegments208.append_exact piece0071 piece0072 rfl rfl rfl
#print axioms join11_00

theorem join11_01 : ChunkFacts (toRow data11.row) 1025 1024 (toTotals ⟨8808853064223, 1094651909010, 2251238886594, 7652266086639, 1160299448⟩) :=
  CleanupSegments208.append_exact piece0073 piece0074 rfl rfl rfl
#print axioms join11_01

theorem join11_02 : ChunkFacts (toRow data11.row) 2049 1024 (toTotals ⟨630038980105, 364286289130, 688194856224, 306130413011, 547689247⟩) :=
  CleanupSegments208.append_exact piece0075 piece0076 rfl rfl rfl
#print axioms join11_02

theorem join11_03 : ChunkFacts (toRow data11.row) 3073 541 (toTotals ⟨164257994058, 161672586070, 305425280736, 20505299392, 273625349⟩) :=
  CleanupSegments208.append_exact piece0077 piece0078 rfl rfl rfl
#print axioms join11_03

theorem join11_04 : ChunkFacts (toRow data11.row) 1 2048 (toTotals ⟨1121188181009361, 6419088999600, 23929253260670, 1103678016748291, 4259408961⟩) :=
  CleanupSegments208.append_exact join11_00 join11_01 rfl rfl rfl
#print axioms join11_04

theorem join11_05 : ChunkFacts (toRow data11.row) 2049 1565 (toTotals ⟨794296974163, 525958875200, 993620136960, 326635712403, 821314596⟩) :=
  CleanupSegments208.append_exact join11_02 join11_03 rfl rfl rfl
#print axioms join11_05

theorem join11_06 : ChunkFacts (toRow data11.row) 1 3613 (toTotals ⟨1121982477983524, 6945047874800, 24922873397630, 1104004652460694, 5080723557⟩) :=
  CleanupSegments208.append_exact join11_04 join11_05 rfl rfl rfl
#print axioms join11_06

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) := join11_06
#print axioms fact11

theorem piece0079 : ChunkFacts (toRow data12.row) 1 512 (toTotals ⟨1116387108039729, 4330494351222, 18470582151159, 1102247020239792, 2121715083⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G09.checked0079
#print axioms piece0079

theorem piece0080 : ChunkFacts (toRow data12.row) 513 512 (toTotals ⟨46627299176680, 1941358344168, 4109306329731, 44459351191117, 1223178208⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0080
#print axioms piece0080

theorem piece0081 : ChunkFacts (toRow data12.row) 1025 512 (toTotals ⟨8353661460145, 890612967462, 1681608358298, 7562666069309, 792361452⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0081
#print axioms piece0081

theorem piece0082 : ChunkFacts (toRow data12.row) 1537 512 (toTotals ⟨2794430459811, 533445206926, 980417623544, 2347458043193, 588293377⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0082
#print axioms piece0082

theorem piece0083 : ChunkFacts (toRow data12.row) 2049 512 (toTotals ⟨611430535407, 284020857548, 486648044352, 408803348603, 370959513⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0083
#print axioms piece0083

theorem piece0084 : ChunkFacts (toRow data12.row) 2561 512 (toTotals ⟨241971290679, 188798087442, 323491101408, 107278276713, 284180137⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0084
#print axioms piece0084

theorem piece0085 : ChunkFacts (toRow data12.row) 3073 512 (toTotals ⟨156089049370, 168699163648, 289053130752, 35735082266, 284457914⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0085
#print axioms piece0085

theorem piece0086 : ChunkFacts (toRow data12.row) 3585 460 (toTotals ⟨122501330262, 151565654840, 259696172160, 14370812942, 256564997⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0086
#print axioms piece0086

theorem join12_00 : ChunkFacts (toRow data12.row) 1 1024 (toTotals ⟨1163014407216409, 6271852695390, 22579888480890, 1146706371430909, 3344893291⟩) :=
  CleanupSegments208.append_exact piece0079 piece0080 rfl rfl rfl
#print axioms join12_00

theorem join12_01 : ChunkFacts (toRow data12.row) 1025 1024 (toTotals ⟨11148091919956, 1424058174388, 2662025981842, 9910124112502, 1380654829⟩) :=
  CleanupSegments208.append_exact piece0081 piece0082 rfl rfl rfl
#print axioms join12_01

theorem join12_02 : ChunkFacts (toRow data12.row) 2049 1024 (toTotals ⟨853401826086, 472818944990, 810139145760, 516081625316, 655139650⟩) :=
  CleanupSegments208.append_exact piece0083 piece0084 rfl rfl rfl
#print axioms join12_02

theorem join12_03 : ChunkFacts (toRow data12.row) 3073 972 (toTotals ⟨278590379632, 320264818488, 548749302912, 50105895208, 541022911⟩) :=
  CleanupSegments208.append_exact piece0085 piece0086 rfl rfl rfl
#print axioms join12_03

theorem join12_04 : ChunkFacts (toRow data12.row) 1 2048 (toTotals ⟨1174162499136365, 7695910869778, 25241914462732, 1156616495543411, 4725548120⟩) :=
  CleanupSegments208.append_exact join12_00 join12_01 rfl rfl rfl
#print axioms join12_04

theorem join12_05 : ChunkFacts (toRow data12.row) 2049 1996 (toTotals ⟨1131992205718, 793083763478, 1358888448672, 566187520524, 1196162561⟩) :=
  CleanupSegments208.append_exact join12_02 join12_03 rfl rfl rfl
#print axioms join12_05

theorem join12_06 : ChunkFacts (toRow data12.row) 1 4044 (toTotals ⟨1175294491342083, 8488994633256, 26600802911404, 1157182683063935, 5921710681⟩) :=
  CleanupSegments208.append_exact join12_04 join12_05 rfl rfl rfl
#print axioms join12_06

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) := join12_06
#print axioms fact12

theorem piece0087 : ChunkFacts (toRow data13.row) 1 512 (toTotals ⟨1150489243460136, 4832124576012, 18904073289547, 1136417294746601, 2230335066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G10.checked0087
#print axioms piece0087

theorem piece0088 : ChunkFacts (toRow data13.row) 513 512 (toTotals ⟨50590067714649, 2236474610460, 4399746868344, 48426795456765, 1320974932⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0088
#print axioms piece0088

theorem piece0089 : ChunkFacts (toRow data13.row) 1025 512 (toTotals ⟨9529972948481, 1061664543216, 1872173985087, 8719463506610, 879878894⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0089
#print axioms piece0089

theorem piece0090 : ChunkFacts (toRow data13.row) 1537 512 (toTotals ⟨3437654843710, 640453012956, 1103679212528, 2974428644138, 671416856⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0090
#print axioms piece0090

theorem piece0091 : ChunkFacts (toRow data13.row) 2049 512 (toTotals ⟨835746874230, 363405094308, 582058159776, 617093808762, 444000721⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0091
#print axioms piece0091

theorem piece0092 : ChunkFacts (toRow data13.row) 2561 512 (toTotals ⟨374032782070, 253784352960, 406480965120, 221336169910, 356836047⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0092
#print axioms piece0092

theorem piece0093 : ChunkFacts (toRow data13.row) 3073 512 (toTotals ⟨156089049370, 180468873216, 289053130752, 47504791834, 294683066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0093
#print axioms piece0093

theorem piece0094 : ChunkFacts (toRow data13.row) 3585 512 (toTotals ⟨135475574220, 180468873216, 289053130752, 26891316684, 318689542⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0094
#print axioms piece0094

theorem piece0095 : ChunkFacts (toRow data13.row) 4097 346 (toTotals ⟨82409955214, 121957480728, 195336686016, 9030749926, 204791324⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G11.checked0095
#print axioms piece0095

theorem join13_00 : ChunkFacts (toRow data13.row) 1 1024 (toTotals ⟨1201079311174785, 7068599186472, 23303820157891, 1184844090203366, 3551309998⟩) :=
  CleanupSegments208.append_exact piece0087 piece0088 rfl rfl rfl
#print axioms join13_00

theorem join13_01 : ChunkFacts (toRow data13.row) 1025 1024 (toTotals ⟨12967627792191, 1702117556172, 2975853197615, 11693892150748, 1551295750⟩) :=
  CleanupSegments208.append_exact piece0089 piece0090 rfl rfl rfl
#print axioms join13_01

theorem join13_02 : ChunkFacts (toRow data13.row) 2049 1024 (toTotals ⟨1209779656300, 617189447268, 988539124896, 838429978672, 800836768⟩) :=
  CleanupSegments208.append_exact piece0091 piece0092 rfl rfl rfl
#print axioms join13_02

theorem join13_03 : ChunkFacts (toRow data13.row) 3073 1024 (toTotals ⟨291564623590, 360937746432, 578106261504, 74396108518, 613372608⟩) :=
  CleanupSegments208.append_exact piece0093 piece0094 rfl rfl rfl
#print axioms join13_03

theorem join13_04 : ChunkFacts (toRow data13.row) 1 2048 (toTotals ⟨1214046938966976, 8770716742644, 26279673355506, 1196537982354114, 5102605748⟩) :=
  CleanupSegments208.append_exact join13_00 join13_01 rfl rfl rfl
#print axioms join13_04

theorem join13_05 : ChunkFacts (toRow data13.row) 2049 2048 (toTotals ⟨1501344279890, 978127193700, 1566645386400, 912826087190, 1414209376⟩) :=
  CleanupSegments208.append_exact join13_02 join13_03 rfl rfl rfl
#print axioms join13_05

theorem join13_06 : ChunkFacts (toRow data13.row) 1 4096 (toTotals ⟨1215548283246866, 9748843936344, 27846318741906, 1197450808441304, 6516815124⟩) :=
  CleanupSegments208.append_exact join13_04 join13_05 rfl rfl rfl
#print axioms join13_06

theorem join13_07 : ChunkFacts (toRow data13.row) 1 4442 (toTotals ⟨1215630693202080, 9870801417072, 28041655427922, 1197459839191230, 6721606448⟩) :=
  CleanupSegments208.append_exact join13_06 piece0095 rfl rfl rfl
#print axioms join13_07

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) := join13_07
#print axioms fact13

theorem piece0096 : ChunkFacts (toRow data14.row) 1 512 (toTotals ⟨917056534122334, 1140740196664, 15783936510180, 902413337808818, 1545994798⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0096
#print axioms piece0096

theorem piece0097 : ChunkFacts (toRow data14.row) 513 512 (toTotals ⟨19724290703996, 339116638528, 2145169209764, 17918238132760, 672814419⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0097
#print axioms piece0097

theorem piece0098 : ChunkFacts (toRow data14.row) 1025 512 (toTotals ⟨2222206597586, 137677576784, 745916515022, 1613967659348, 345017720⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0098
#print axioms piece0098

theorem piece0099 : ChunkFacts (toRow data14.row) 1537 512 (toTotals ⟨289489937270, 60455333888, 284231877632, 65713393526, 172781727⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0099
#print axioms piece0099

theorem piece0100 : ChunkFacts (toRow data14.row) 2049 218 (toTotals ⟨101933370105, 25740747632, 121020604148, 6653513589, 72775433⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0100
#print axioms piece0100

theorem join14_00 : ChunkFacts (toRow data14.row) 1 1024 (toTotals ⟨936780824826330, 1479856835192, 17929105719944, 920331575941578, 2218809217⟩) :=
  CleanupSegments208.append_exact piece0096 piece0097 rfl rfl rfl
#print axioms join14_00

theorem join14_01 : ChunkFacts (toRow data14.row) 1025 1024 (toTotals ⟨2511696534856, 198132910672, 1030148392654, 1679681052874, 517799447⟩) :=
  CleanupSegments208.append_exact piece0098 piece0099 rfl rfl rfl
#print axioms join14_01

theorem join14_02 : ChunkFacts (toRow data14.row) 1 2048 (toTotals ⟨939292521361186, 1677989745864, 18959254112598, 922011256994452, 2736608664⟩) :=
  CleanupSegments208.append_exact join14_00 join14_01 rfl rfl rfl
#print axioms join14_02

theorem join14_03 : ChunkFacts (toRow data14.row) 1 2266 (toTotals ⟨939394454731291, 1703730493496, 19080274716746, 922017910508041, 2809384097⟩) :=
  CleanupSegments208.append_exact join14_02 piece0100 rfl rfl rfl
#print axioms join14_03

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) := join14_03
#print axioms fact14

theorem piece0101 : ChunkFacts (toRow data15.row) 1 512 (toTotals ⟨960043689624208, 1826342202885, 16376257067815, 945493774759278, 1697177863⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0101
#print axioms piece0101

theorem piece0102 : ChunkFacts (toRow data15.row) 513 512 (toTotals ⟨25789218632827, 620862699300, 2596007257920, 23814074074207, 805284857⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0102
#print axioms piece0102

theorem piece0103 : ChunkFacts (toRow data15.row) 1025 512 (toTotals ⟨3514954400361, 266207889225, 965104444126, 2816057845460, 460645356⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G12.checked0103
#print axioms piece0103

theorem piece0104 : ChunkFacts (toRow data15.row) 1537 512 (toTotals ⟨424729910056, 101453820975, 330272943760, 195910787271, 205173971⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0104
#print axioms piece0104

theorem piece0105 : ChunkFacts (toRow data15.row) 2049 512 (toTotals ⟨224983959916, 88793771520, 284231877632, 29545853804, 198450262⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0105
#print axioms piece0105

theorem piece0106 : ChunkFacts (toRow data15.row) 2561 18 (toTotals ⟨7071700727, 3121656030, 9992526948, 200829809, 2624076⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0106
#print axioms piece0106

theorem join15_00 : ChunkFacts (toRow data15.row) 1 1024 (toTotals ⟨985832908257035, 2447204902185, 18972264325735, 969307848833485, 2502462720⟩) :=
  CleanupSegments208.append_exact piece0101 piece0102 rfl rfl rfl
#print axioms join15_00

theorem join15_01 : ChunkFacts (toRow data15.row) 1025 1024 (toTotals ⟨3939684310417, 367661710200, 1295377387886, 3011968632731, 665819327⟩) :=
  CleanupSegments208.append_exact piece0103 piece0104 rfl rfl rfl
#print axioms join15_01

theorem join15_02 : ChunkFacts (toRow data15.row) 2049 530 (toTotals ⟨232055660643, 91915427550, 294224404580, 29746683613, 201074338⟩) :=
  CleanupSegments208.append_exact piece0105 piece0106 rfl rfl rfl
#print axioms join15_02

theorem join15_03 : ChunkFacts (toRow data15.row) 1 2048 (toTotals ⟨989772592567452, 2814866612385, 20267641713621, 972319817466216, 3168282047⟩) :=
  CleanupSegments208.append_exact join15_00 join15_01 rfl rfl rfl
#print axioms join15_03

theorem join15_04 : ChunkFacts (toRow data15.row) 1 2578 (toTotals ⟨990004648228095, 2906782039935, 20561866118201, 972349564149829, 3369356385⟩) :=
  CleanupSegments208.append_exact join15_03 join15_02 rfl rfl rfl
#print axioms join15_04

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) := join15_04
#print axioms fact15

theorem piece0107 : ChunkFacts (toRow data16.row) 1 512 (toTotals ⟨1001993145429801, 2469200401248, 16936735342263, 987525610488786, 1842705485⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0107
#print axioms piece0107

theorem piece0108 : ChunkFacts (toRow data16.row) 513 512 (toTotals ⟨32199430712553, 933950777760, 3046062415789, 30087319074524, 940823797⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0108
#print axioms piece0108

theorem piece0109 : ChunkFacts (toRow data16.row) 1025 512 (toTotals ⟨4729246582825, 397963175232, 1128315717610, 3998894040447, 550317648⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0109
#print axioms piece0109

theorem piece0110 : ChunkFacts (toRow data16.row) 1537 512 (toTotals ⟨899202135561, 183306889248, 491035905838, 591473118971, 297797918⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0110
#print axioms piece0110

theorem piece0111 : ChunkFacts (toRow data16.row) 2049 512 (toTotals ⟨224983959916, 111464521728, 284231877632, 52216604012, 212903950⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G13.checked0111
#print axioms piece0111

theorem piece0112 : ChunkFacts (toRow data16.row) 2561 337 (toTotals ⟨124889239730, 73366296528, 187082310082, 11173226176, 141614489⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0112
#print axioms piece0112

theorem join16_00 : ChunkFacts (toRow data16.row) 1 1024 (toTotals ⟨1034192576142354, 3403151179008, 19982797758052, 1017612929563310, 2783529282⟩) :=
  CleanupSegments208.append_exact piece0107 piece0108 rfl rfl rfl
#print axioms join16_00

theorem join16_01 : ChunkFacts (toRow data16.row) 1025 1024 (toTotals ⟨5628448718386, 581270064480, 1619351623448, 4590367159418, 848115566⟩) :=
  CleanupSegments208.append_exact piece0109 piece0110 rfl rfl rfl
#print axioms join16_01

theorem join16_02 : ChunkFacts (toRow data16.row) 2049 849 (toTotals ⟨349873199646, 184830818256, 471314187714, 63389830188, 354518439⟩) :=
  CleanupSegments208.append_exact piece0111 piece0112 rfl rfl rfl
#print axioms join16_02

theorem join16_03 : ChunkFacts (toRow data16.row) 1 2048 (toTotals ⟨1039821024860740, 3984421243488, 21602149381500, 1022203296722728, 3631644848⟩) :=
  CleanupSegments208.append_exact join16_00 join16_01 rfl rfl rfl
#print axioms join16_03

theorem join16_04 : ChunkFacts (toRow data16.row) 1 2897 (toTotals ⟨1040170898060386, 4169252061744, 22073463569214, 1022266686552916, 3986163287⟩) :=
  CleanupSegments208.append_exact join16_03 join16_02 rfl rfl rfl
#print axioms join16_04

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) := join16_04
#print axioms fact16

theorem piece0113 : ChunkFacts (toRow data17.row) 1 512 (toTotals ⟨1026960783206180, 2981402909920, 17275798008868, 1012666388107232, 1951429975⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0113
#print axioms piece0113

theorem piece0114 : ChunkFacts (toRow data17.row) 513 512 (toTotals ⟨36743487353761, 1220312907536, 3368862315946, 34594937945351, 1044469203⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0114
#print axioms piece0114

theorem piece0115 : ChunkFacts (toRow data17.row) 1025 512 (toTotals ⟨5800917513170, 529574556160, 1280979323760, 5049512745570, 628962336⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0115
#print axioms piece0115

theorem piece0116 : ChunkFacts (toRow data17.row) 1537 512 (toTotals ⟨1445741629013, 280318070352, 650261556072, 1075798143293, 395261411⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0116
#print axioms piece0116

theorem piece0117 : ChunkFacts (toRow data17.row) 2049 512 (toTotals ⟨281644380101, 142577765120, 310878616160, 113343529061, 239318490⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0117
#print axioms piece0117

theorem piece0118 : ChunkFacts (toRow data17.row) 2561 512 (toTotals ⟨184178238178, 130356813824, 284231877632, 30303174370, 242665214⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0118
#print axioms piece0118

theorem piece0119 : ChunkFacts (toRow data17.row) 3073 158 (toTotals ⟨50728365574, 40227298016, 87712180988, 3243482602, 69025491⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G14.checked0119
#print axioms piece0119

theorem join17_00 : ChunkFacts (toRow data17.row) 1 1024 (toTotals ⟨1063704270559941, 4201715817456, 20644660324814, 1047261326052583, 2995899178⟩) :=
  CleanupSegments208.append_exact piece0113 piece0114 rfl rfl rfl
#print axioms join17_00

theorem join17_01 : ChunkFacts (toRow data17.row) 1025 1024 (toTotals ⟨7246659142183, 809892626512, 1931240879832, 6125310888863, 1024223747⟩) :=
  CleanupSegments208.append_exact piece0115 piece0116 rfl rfl rfl
#print axioms join17_01

theorem join17_02 : ChunkFacts (toRow data17.row) 2049 1024 (toTotals ⟨465822618279, 272934578944, 595110493792, 143646703431, 481983704⟩) :=
  CleanupSegments208.append_exact piece0117 piece0118 rfl rfl rfl
#print axioms join17_02

theorem join17_03 : ChunkFacts (toRow data17.row) 1 2048 (toTotals ⟨1070950929702124, 5011608443968, 22575901204646, 1053386636941446, 4020122925⟩) :=
  CleanupSegments208.append_exact join17_00 join17_01 rfl rfl rfl
#print axioms join17_03

theorem join17_04 : ChunkFacts (toRow data17.row) 2049 1182 (toTotals ⟨516550983853, 313161876960, 682822674780, 146890186033, 551009195⟩) :=
  CleanupSegments208.append_exact join17_02 piece0119 rfl rfl rfl
#print axioms join17_04

theorem join17_05 : ChunkFacts (toRow data17.row) 1 3230 (toTotals ⟨1071467480685977, 5324770320928, 23258723879426, 1053533527127479, 4571132120⟩) :=
  CleanupSegments208.append_exact join17_03 join17_04 rfl rfl rfl
#print axioms join17_05

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) := join17_05
#print axioms fact17

theorem piece0120 : ChunkFacts (toRow data18.row) 1 512 (toTotals ⟨1072131272181880, 3537607479458, 17789616022210, 1057879263639128, 2045247568⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0120
#print axioms piece0120

theorem piece0121 : ChunkFacts (toRow data18.row) 513 512 (toTotals ⟨40747438656722, 1492494746574, 3651983912849, 38587949490447, 1129547794⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0121
#print axioms piece0121

theorem piece0122 : ChunkFacts (toRow data18.row) 1025 512 (toTotals ⟨6799205061440, 659447992918, 1427607557522, 6031045496836, 700435487⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0122
#print axioms piece0122

theorem piece0123 : ChunkFacts (toRow data18.row) 1537 512 (toTotals ⟨2014372749388, 373905023128, 781530905834, 1606746866682, 480016425⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0123
#print axioms piece0123

theorem piece0124 : ChunkFacts (toRow data18.row) 2049 512 (toTotals ⟨418287003138, 193771448156, 378605743252, 233452708042, 292922956⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0124
#print axioms piece0124

theorem piece0125 : ChunkFacts (toRow data18.row) 2561 512 (toTotals ⟨184178238178, 145470647296, 284231877632, 45417007842, 254201598⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0125
#print axioms piece0125

theorem piece0126 : ChunkFacts (toRow data18.row) 3073 485 (toTotals ⟨148356089629, 137799343630, 269243087210, 16912346049, 246741905⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0126
#print axioms piece0126

theorem join18_00 : ChunkFacts (toRow data18.row) 1 1024 (toTotals ⟨1112878710838602, 5030102226032, 21441599935059, 1096467213129575, 3174795362⟩) :=
  CleanupSegments208.append_exact piece0120 piece0121 rfl rfl rfl
#print axioms join18_00

theorem join18_01 : ChunkFacts (toRow data18.row) 1025 1024 (toTotals ⟨8813577810828, 1033353016046, 2209138463356, 7637792363518, 1180451912⟩) :=
  CleanupSegments208.append_exact piece0122 piece0123 rfl rfl rfl
#print axioms join18_01

theorem join18_02 : ChunkFacts (toRow data18.row) 2049 1024 (toTotals ⟨602465241316, 339242095452, 662837620884, 278869715884, 547124554⟩) :=
  CleanupSegments208.append_exact piece0124 piece0125 rfl rfl rfl
#print axioms join18_02

theorem join18_03 : ChunkFacts (toRow data18.row) 1 2048 (toTotals ⟨1121692288649430, 6063455242078, 23650738398415, 1104105005493093, 4355247274⟩) :=
  CleanupSegments208.append_exact join18_00 join18_01 rfl rfl rfl
#print axioms join18_03

theorem join18_04 : ChunkFacts (toRow data18.row) 2049 1509 (toTotals ⟨750821330945, 477041439082, 932080708094, 295782061933, 793866459⟩) :=
  CleanupSegments208.append_exact join18_02 piece0126 rfl rfl rfl
#print axioms join18_04

theorem join18_05 : ChunkFacts (toRow data18.row) 1 3557 (toTotals ⟨1122443109980375, 6540496681160, 24582819106509, 1104400787555026, 5149113733⟩) :=
  CleanupSegments208.append_exact join18_03 join18_04 rfl rfl rfl
#print axioms join18_05

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) := join18_05
#print axioms fact18

theorem piece0127 : ChunkFacts (toRow data19.row) 1 512 (toTotals ⟨1106503933641123, 4047230741856, 18183466774698, 1092367697608281, 2161522684⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G15.checked0127
#print axioms piece0127

theorem piece0128 : ChunkFacts (toRow data19.row) 513 512 (toTotals ⟨45165844142543, 1800302577360, 3963232622668, 43002914097235, 1236430492⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0128
#print axioms piece0128

theorem piece0129 : ChunkFacts (toRow data19.row) 1025 512 (toTotals ⟨8169209081053, 830522861472, 1626846018640, 7372885923885, 796581066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0129
#print axioms piece0129

theorem piece0130 : ChunkFacts (toRow data19.row) 1537 512 (toTotals ⟨2667204672294, 494926387992, 942201344508, 2219929715778, 586834247⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0130
#print axioms piece0130

theorem piece0131 : ChunkFacts (toRow data19.row) 2049 512 (toTotals ⟨584236087560, 262831630632, 465207643468, 381860074724, 367157453⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0131
#print axioms piece0131

theorem piece0132 : ChunkFacts (toRow data19.row) 2561 512 (toTotals ⟨215598169633, 170934652380, 302551510370, 83981311643, 276526188⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0132
#print axioms piece0132

theorem piece0133 : ChunkFacts (toRow data19.row) 3073 512 (toTotals ⟨156016660250, 160584480768, 284231877632, 32369263386, 287885876⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0133
#print axioms piece0133

theorem piece0134 : ChunkFacts (toRow data19.row) 3585 373 (toTotals ⟨100369851140, 116988303372, 207067363978, 10290790534, 206962601⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0134
#print axioms piece0134

theorem join19_00 : ChunkFacts (toRow data19.row) 1 1024 (toTotals ⟨1151669777783666, 5847533319216, 22146699397366, 1135370611705516, 3397953176⟩) :=
  CleanupSegments208.append_exact piece0127 piece0128 rfl rfl rfl
#print axioms join19_00

theorem join19_01 : ChunkFacts (toRow data19.row) 1025 1024 (toTotals ⟨10836413753347, 1325449249464, 2569047363148, 9592815639663, 1383415313⟩) :=
  CleanupSegments208.append_exact piece0129 piece0130 rfl rfl rfl
#print axioms join19_01

theorem join19_02 : ChunkFacts (toRow data19.row) 2049 1024 (toTotals ⟨799834257193, 433766283012, 767759153838, 465841386367, 643683641⟩) :=
  CleanupSegments208.append_exact piece0131 piece0132 rfl rfl rfl
#print axioms join19_02

theorem join19_03 : ChunkFacts (toRow data19.row) 3073 885 (toTotals ⟨256386511390, 277572784140, 491299241610, 42660053920, 494848477⟩) :=
  CleanupSegments208.append_exact piece0133 piece0134 rfl rfl rfl
#print axioms join19_03

theorem join19_04 : ChunkFacts (toRow data19.row) 1 2048 (toTotals ⟨1162506191537013, 7172982568680, 24715746760514, 1144963427345179, 4781368489⟩) :=
  CleanupSegments208.append_exact join19_00 join19_01 rfl rfl rfl
#print axioms join19_04

theorem join19_05 : ChunkFacts (toRow data19.row) 2049 1909 (toTotals ⟨1056220768583, 711339067152, 1259058395448, 508501440287, 1138532118⟩) :=
  CleanupSegments208.append_exact join19_02 join19_03 rfl rfl rfl
#print axioms join19_05

theorem join19_06 : ChunkFacts (toRow data19.row) 1 3957 (toTotals ⟨1163562412305596, 7884321635832, 25974805155962, 1145471928785466, 5919900607⟩) :=
  CleanupSegments208.append_exact join19_04 join19_05 rfl rfl rfl
#print axioms join19_06

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) := join19_06
#print axioms fact19

theorem piece0135 : ChunkFacts (toRow data20.row) 1 512 (toTotals ⟨1143388259753129, 4657721117637, 18650873628234, 1129395107242532, 2302208719⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G16.checked0135
#print axioms piece0135

theorem piece0136 : ChunkFacts (toRow data20.row) 513 512 (toTotals ⟨50858296914250, 2188336223913, 4357759507568, 48688873630595, 1362743150⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0136
#print axioms piece0136

theorem piece0137 : ChunkFacts (toRow data20.row) 1025 512 (toTotals ⟨9709279769089, 1045267702374, 1869598945402, 8884948526061, 911149785⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0137
#print axioms piece0137

theorem piece0138 : ChunkFacts (toRow data20.row) 1537 512 (toTotals ⟨3521184543841, 632102136498, 1102437634928, 3050849045411, 697735076⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0138
#print axioms piece0138

theorem piece0139 : ChunkFacts (toRow data20.row) 2049 512 (toTotals ⟨846783415566, 356887199760, 577346001440, 626324613886, 457399678⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0139
#print axioms piece0139

theorem piece0140 : ChunkFacts (toRow data20.row) 2561 512 (toTotals ⟨382360669196, 250507361370, 405252481780, 227615548786, 369645572⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0140
#print axioms piece0140

theorem piece0141 : ChunkFacts (toRow data20.row) 3073 512 (toTotals ⟨156016660250, 175698313728, 284231877632, 47483096346, 301519412⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0141
#print axioms piece0141

theorem piece0142 : ChunkFacts (toRow data20.row) 3585 512 (toTotals ⟨135403185100, 175698313728, 284231877632, 26869621196, 325755425⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0142
#print axioms piece0142

theorem piece0143 : ChunkFacts (toRow data20.row) 4097 364 (toTotals ⟨86471040540, 124910519916, 202071100504, 9310459952, 222116241⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G17.checked0143
#print axioms piece0143

theorem join20_00 : ChunkFacts (toRow data20.row) 1 1024 (toTotals ⟨1194246556667379, 6846057341550, 23008633135802, 1178083980873127, 3664951869⟩) :=
  CleanupSegments208.append_exact piece0135 piece0136 rfl rfl rfl
#print axioms join20_00

theorem join20_01 : ChunkFacts (toRow data20.row) 1025 1024 (toTotals ⟨13230464312930, 1677369838872, 2972036580330, 11935797571472, 1608884861⟩) :=
  CleanupSegments208.append_exact piece0137 piece0138 rfl rfl rfl
#print axioms join20_01

theorem join20_02 : ChunkFacts (toRow data20.row) 2049 1024 (toTotals ⟨1229144084762, 607394561130, 982598483220, 853940162672, 827045250⟩) :=
  CleanupSegments208.append_exact piece0139 piece0140 rfl rfl rfl
#print axioms join20_02

theorem join20_03 : ChunkFacts (toRow data20.row) 3073 1024 (toTotals ⟨291419845350, 351396627456, 568463755264, 74352717542, 627274837⟩) :=
  CleanupSegments208.append_exact piece0141 piece0142 rfl rfl rfl
#print axioms join20_03

theorem join20_04 : ChunkFacts (toRow data20.row) 1 2048 (toTotals ⟨1207477020980309, 8523427180422, 25980669716132, 1190019778444599, 5273836730⟩) :=
  CleanupSegments208.append_exact join20_00 join20_01 rfl rfl rfl
#print axioms join20_04

theorem join20_05 : ChunkFacts (toRow data20.row) 2049 2048 (toTotals ⟨1520563930112, 958791188586, 1551062238484, 928292880214, 1454320087⟩) :=
  CleanupSegments208.append_exact join20_02 join20_03 rfl rfl rfl
#print axioms join20_05

theorem join20_06 : ChunkFacts (toRow data20.row) 1 4096 (toTotals ⟨1208997584910421, 9482218369008, 27531731954616, 1190948071324813, 6728156817⟩) :=
  CleanupSegments208.append_exact join20_04 join20_05 rfl rfl rfl
#print axioms join20_06

theorem join20_07 : ChunkFacts (toRow data20.row) 1 4460 (toTotals ⟨1209084055950961, 9607128888924, 27733803055120, 1190957381784765, 6950273058⟩) :=
  CleanupSegments208.append_exact join20_06 piece0143 rfl rfl rfl
#print axioms join20_07

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) := join20_07
#print axioms fact20

theorem piece0144 : ChunkFacts (toRow data21.row) 1 512 (toTotals ⟨914682936167564, 1147673940398, 15660944084938, 900169666023024, 1621543690⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0144
#print axioms piece0144

theorem piece0145 : ChunkFacts (toRow data21.row) 513 512 (toTotals ⟨20833056355560, 351829645496, 2200933984734, 18983952016322, 719152067⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0145
#print axioms piece0145

theorem piece0146 : ChunkFacts (toRow data21.row) 1025 512 (toTotals ⟨2448792213341, 145617076240, 777802213466, 1816607076115, 377810712⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0146
#print axioms piece0146

theorem piece0147 : ChunkFacts (toRow data21.row) 1537 512 (toTotals ⟨289422700918, 60125760512, 277982619136, 71565842294, 178825486⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0147
#print axioms piece0147

theorem piece0148 : ChunkFacts (toRow data21.row) 2049 280 (toTotals ⟨129112865731, 32881275280, 152021744840, 9972396171, 97846807⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0148
#print axioms piece0148

theorem join21_00 : ChunkFacts (toRow data21.row) 1 1024 (toTotals ⟨935515992523124, 1499503585894, 17861878069672, 919153618039346, 2340695757⟩) :=
  CleanupSegments208.append_exact piece0144 piece0145 rfl rfl rfl
#print axioms join21_00

theorem join21_01 : ChunkFacts (toRow data21.row) 1025 1024 (toTotals ⟨2738214914259, 205742836752, 1055784832602, 1888172918409, 556636198⟩) :=
  CleanupSegments208.append_exact piece0146 piece0147 rfl rfl rfl
#print axioms join21_01

theorem join21_02 : ChunkFacts (toRow data21.row) 1 2048 (toTotals ⟨938254207437383, 1705246422646, 18917662902274, 921041790957755, 2897331955⟩) :=
  CleanupSegments208.append_exact join21_00 join21_01 rfl rfl rfl
#print axioms join21_02

theorem join21_03 : ChunkFacts (toRow data21.row) 1 2328 (toTotals ⟨938383320303114, 1738127697926, 19069684647114, 921051763353926, 2995178762⟩) :=
  CleanupSegments208.append_exact join21_02 piece0148 rfl rfl rfl
#print axioms join21_03

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) := join21_03
#print axioms fact21

theorem piece0149 : ChunkFacts (toRow data22.row) 1 512 (toTotals ⟨963808701847350, 1777901941200, 16258766847496, 949327836941054, 1763922467⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0149
#print axioms piece0149

theorem piece0150 : ChunkFacts (toRow data22.row) 513 512 (toTotals ⟨26779682870151, 614990163480, 2628258037662, 24766414995969, 848126841⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0150
#print axioms piece0150

theorem piece0151 : ChunkFacts (toRow data22.row) 1025 512 (toTotals ⟨3584482694725, 259744281720, 954018920003, 2890208056442, 477552158⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G18.checked0151
#print axioms piece0151

theorem piece0152 : ChunkFacts (toRow data22.row) 1537 512 (toTotals ⟨510927879288, 104366021760, 350481596820, 264812304228, 223562132⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0152
#print axioms piece0152

theorem piece0153 : ChunkFacts (toRow data22.row) 2049 512 (toTotals ⟨224916723564, 85633658880, 277982619136, 32567763308, 203858791⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0153
#print axioms piece0153

theorem piece0154 : ChunkFacts (toRow data22.row) 2561 61 (toTotals ⟨23761194233, 10202447640, 33119022983, 844618890, 20351693⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0154
#print axioms piece0154

theorem join22_00 : ChunkFacts (toRow data22.row) 1 1024 (toTotals ⟨990588384717501, 2392892104680, 18887024885158, 974094251937023, 2612049308⟩) :=
  CleanupSegments208.append_exact piece0149 piece0150 rfl rfl rfl
#print axioms join22_00

theorem join22_01 : ChunkFacts (toRow data22.row) 1025 1024 (toTotals ⟨4095410574013, 364110303480, 1304500516823, 3155020360670, 701114290⟩) :=
  CleanupSegments208.append_exact piece0151 piece0152 rfl rfl rfl
#print axioms join22_01

theorem join22_02 : ChunkFacts (toRow data22.row) 2049 573 (toTotals ⟨248677917797, 95836106520, 311101642119, 33412382198, 224210484⟩) :=
  CleanupSegments208.append_exact piece0153 piece0154 rfl rfl rfl
#print axioms join22_02

theorem join22_03 : ChunkFacts (toRow data22.row) 1 2048 (toTotals ⟨994683795291514, 2757002408160, 20191525401981, 977249272297693, 3313163598⟩) :=
  CleanupSegments208.append_exact join22_00 join22_01 rfl rfl rfl
#print axioms join22_03

theorem join22_04 : ChunkFacts (toRow data22.row) 1 2621 (toTotals ⟨994932473209311, 2852838514680, 20502627044100, 977282684679891, 3537374082⟩) :=
  CleanupSegments208.append_exact join22_03 join22_02 rfl rfl rfl
#print axioms join22_04

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) := join22_04
#print axioms fact22

theorem piece0155 : ChunkFacts (toRow data23.row) 1 512 (toTotals ⟨1003008898565340, 2399799297420, 16785310517528, 988623387345232, 1913575521⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0155
#print axioms piece0155

theorem piece0156 : ChunkFacts (toRow data23.row) 513 512 (toTotals ⟨33145298515972, 919188217332, 3053296953603, 31011189779701, 982796369⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0156
#print axioms piece0156

theorem piece0157 : ChunkFacts (toRow data23.row) 1025 512 (toTotals ⟨4969380186853, 394717644720, 1143503166250, 4220594665323, 578117768⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0157
#print axioms piece0157

theorem piece0158 : ChunkFacts (toRow data23.row) 1537 512 (toTotals ⟨997775898762, 186651056466, 512111225899, 672315729329, 321984464⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0158
#print axioms piece0158

theorem piece0159 : ChunkFacts (toRow data23.row) 2049 512 (toTotals ⟨224916723564, 107497571328, 277982619136, 54431675756, 218017639⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G19.checked0159
#print axioms piece0159

theorem piece0160 : ChunkFacts (toRow data23.row) 2561 379 (toTotals ⟨139385647425, 79573397526, 205772290337, 13186754614, 164454343⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0160
#print axioms piece0160

theorem join23_00 : ChunkFacts (toRow data23.row) 1 1024 (toTotals ⟨1036154197081312, 3318987514752, 19838607471131, 1019634577124933, 2896371890⟩) :=
  CleanupSegments208.append_exact piece0155 piece0156 rfl rfl rfl
#print axioms join23_00

theorem join23_01 : ChunkFacts (toRow data23.row) 1025 1024 (toTotals ⟨5967156085615, 581368701186, 1655614392149, 4892910394652, 900102232⟩) :=
  CleanupSegments208.append_exact piece0157 piece0158 rfl rfl rfl
#print axioms join23_01

theorem join23_02 : ChunkFacts (toRow data23.row) 2049 891 (toTotals ⟨364302370989, 187070968854, 483754909473, 67618430370, 382471982⟩) :=
  CleanupSegments208.append_exact piece0159 piece0160 rfl rfl rfl
#print axioms join23_02

theorem join23_03 : ChunkFacts (toRow data23.row) 1 2048 (toTotals ⟨1042121353166927, 3900356215938, 21494221863280, 1024527487519585, 3796474122⟩) :=
  CleanupSegments208.append_exact join23_00 join23_01 rfl rfl rfl
#print axioms join23_03

theorem join23_04 : ChunkFacts (toRow data23.row) 1 2939 (toTotals ⟨1042485655537916, 4087427184792, 21977976772753, 1024595105949955, 4178946104⟩) :=
  CleanupSegments208.append_exact join23_03 join23_02 rfl rfl rfl
#print axioms join23_04

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) := join23_04
#print axioms fact23

theorem piece0161 : ChunkFacts (toRow data24.row) 1 512 (toTotals ⟨1019386879283581, 2879225374740, 17062471861871, 1005203632796450, 2023056456⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0161
#print axioms piece0161

theorem piece0162 : ChunkFacts (toRow data24.row) 513 512 (toTotals ⟨37498608159010, 1194316239360, 3360295658039, 35332628740331, 1086350854⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0162
#print axioms piece0162

theorem piece0163 : ChunkFacts (toRow data24.row) 1025 512 (toTotals ⟨6072366308850, 522022270740, 1290635061567, 5303753518023, 657001944⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0163
#print axioms piece0163

theorem piece0164 : ChunkFacts (toRow data24.row) 1537 512 (toTotals ⟨1563932017509, 282127746510, 668428341019, 1177631423000, 421177539⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0164
#print axioms piece0164

theorem piece0165 : ChunkFacts (toRow data24.row) 2049 512 (toTotals ⟨296453857229, 140695560270, 311101642119, 126047775380, 249334669⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0165
#print axioms piece0165

theorem piece0166 : ChunkFacts (toRow data24.row) 2561 512 (toTotals ⟨184111001826, 125717498880, 277982619136, 31845881570, 247783172⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0166
#print axioms piece0166

theorem piece0167 : ChunkFacts (toRow data24.row) 3073 197 (toTotals ⟨62846545405, 48371772030, 106958156191, 4260161244, 90894169⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G20.checked0167
#print axioms piece0167

theorem join24_00 : ChunkFacts (toRow data24.row) 1 1024 (toTotals ⟨1056885487442591, 4073541614100, 20422767519910, 1040536261536781, 3109407310⟩) :=
  CleanupSegments208.append_exact piece0161 piece0162 rfl rfl rfl
#print axioms join24_00

theorem join24_01 : ChunkFacts (toRow data24.row) 1025 1024 (toTotals ⟨7636298326359, 804150017250, 1959063402586, 6481384941023, 1078179483⟩) :=
  CleanupSegments208.append_exact piece0163 piece0164 rfl rfl rfl
#print axioms join24_01

theorem join24_02 : ChunkFacts (toRow data24.row) 2049 1024 (toTotals ⟨480564859055, 266413059150, 589084261255, 157893656950, 497117841⟩) :=
  CleanupSegments208.append_exact piece0165 piece0166 rfl rfl rfl
#print axioms join24_02

theorem join24_03 : ChunkFacts (toRow data24.row) 1 2048 (toTotals ⟨1064521785768950, 4877691631350, 22381830922496, 1047017646477804, 4187586793⟩) :=
  CleanupSegments208.append_exact join24_00 join24_01 rfl rfl rfl
#print axioms join24_03

theorem join24_04 : ChunkFacts (toRow data24.row) 2049 1221 (toTotals ⟨543411404460, 314784831180, 696042417446, 162153818194, 588012010⟩) :=
  CleanupSegments208.append_exact join24_02 piece0167 rfl rfl rfl
#print axioms join24_04

theorem join24_05 : ChunkFacts (toRow data24.row) 1 3269 (toTotals ⟨1065065197173410, 5192476462530, 23077873339942, 1047179800295998, 4775598803⟩) :=
  CleanupSegments208.append_exact join24_03 join24_04 rfl rfl rfl
#print axioms join24_05

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) := join24_05
#print axioms fact24

theorem piece0168 : ChunkFacts (toRow data25.row) 1 512 (toTotals ⟨1076118990636515, 3567792732126, 17702348017592, 1061984435351049, 2150769347⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0168
#print axioms piece0168

theorem piece0169 : ChunkFacts (toRow data25.row) 513 512 (toTotals ⟨42980574152889, 1537206733848, 3727566998200, 40790213888537, 1201853075⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0169
#print axioms piece0169

theorem piece0170 : ChunkFacts (toRow data25.row) 1025 512 (toTotals ⟨7436116729936, 689606459058, 1488125878012, 6637597310982, 755588450⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0170
#print axioms piece0170

theorem piece0171 : ChunkFacts (toRow data25.row) 1537 512 (toTotals ⟨2300316348872, 401450478408, 836360137368, 1865406689912, 534908857⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0171
#print axioms piece0171

theorem piece0172 : ChunkFacts (toRow data25.row) 2049 512 (toTotals ⟨475612288586, 206910050496, 399600015008, 282922324074, 323123072⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0172
#print axioms piece0172

theorem piece0173 : ChunkFacts (toRow data25.row) 2561 512 (toTotals ⟨184111001826, 143937426432, 277982619136, 50065809122, 262203652⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0173
#print axioms piece0173

theorem piece0174 : ChunkFacts (toRow data25.row) 3073 512 (toTotals ⟨155949423898, 143937426432, 277982619136, 21904231194, 282774046⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0174
#print axioms piece0174

theorem piece0175 : ChunkFacts (toRow data25.row) 3585 99 (toTotals ⟨27596692129, 27831650814, 53750545497, 1677797446, 43769947⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G21.checked0175
#print axioms piece0175

theorem join25_00 : ChunkFacts (toRow data25.row) 1 1024 (toTotals ⟨1119099564789404, 5104999465974, 21429915015792, 1102774649239586, 3352622422⟩) :=
  CleanupSegments208.append_exact piece0168 piece0169 rfl rfl rfl
#print axioms join25_00

theorem join25_01 : ChunkFacts (toRow data25.row) 1025 1024 (toTotals ⟨9736433078808, 1091056937466, 2324486015380, 8503004000894, 1290497307⟩) :=
  CleanupSegments208.append_exact piece0170 piece0171 rfl rfl rfl
#print axioms join25_01

theorem join25_02 : ChunkFacts (toRow data25.row) 2049 1024 (toTotals ⟨659723290412, 350847476928, 677582634144, 332988133196, 585326724⟩) :=
  CleanupSegments208.append_exact piece0172 piece0173 rfl rfl rfl
#print axioms join25_02

theorem join25_03 : ChunkFacts (toRow data25.row) 3073 611 (toTotals ⟨183546116027, 171769077246, 331733164633, 23582028640, 326543993⟩) :=
  CleanupSegments208.append_exact piece0174 piece0175 rfl rfl rfl
#print axioms join25_03

theorem join25_04 : ChunkFacts (toRow data25.row) 1 2048 (toTotals ⟨1128835997868212, 6196056403440, 23754401031172, 1111277653240480, 4643119729⟩) :=
  CleanupSegments208.append_exact join25_00 join25_01 rfl rfl rfl
#print axioms join25_04

theorem join25_05 : ChunkFacts (toRow data25.row) 2049 1635 (toTotals ⟨843269406439, 522616554174, 1009315798777, 356570161836, 911870717⟩) :=
  CleanupSegments208.append_exact join25_02 join25_03 rfl rfl rfl
#print axioms join25_05

theorem join25_06 : ChunkFacts (toRow data25.row) 1 3683 (toTotals ⟨1129679267274651, 6718672957614, 24763716829949, 1111634223402316, 5554990446⟩) :=
  CleanupSegments208.append_exact join25_04 join25_05 rfl rfl rfl
#print axioms join25_06

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) := join25_06
#print axioms fact25

theorem piece0176 : ChunkFacts (toRow data26.row) 1 512 (toTotals ⟨1118902864448433, 4107106134252, 18158286109162, 1104851684473523, 2266455520⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0176
#print axioms piece0176

theorem piece0177 : ChunkFacts (toRow data26.row) 513 512 (toTotals ⟨47719612756750, 1857268935578, 4051839963741, 45525041728587, 1308361088⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0177
#print axioms piece0177

theorem piece0178 : ChunkFacts (toRow data26.row) 1025 512 (toTotals ⟨8830853780638, 861297246004, 1683991326344, 8008159700298, 853482458⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0178
#print axioms piece0178

theorem piece0179 : ChunkFacts (toRow data26.row) 1537 512 (toTotals ⟨2995909314454, 524456338868, 993553508024, 2526812145298, 645042348⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0179
#print axioms piece0179

theorem piece0180 : ChunkFacts (toRow data26.row) 2049 512 (toTotals ⟨624868560272, 271206465672, 475610887428, 420464138516, 393318065⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0180
#print axioms piece0180

theorem piece0181 : ChunkFacts (toRow data26.row) 2561 512 (toTotals ⟨258220014553, 182971485402, 320874468573, 120317031382, 304713734⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0181
#print axioms piece0181

theorem piece0182 : ChunkFacts (toRow data26.row) 3073 512 (toTotals ⟨155949423898, 158513368064, 277982619136, 36480172826, 296407582⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0182
#print axioms piece0182

theorem piece0183 : ChunkFacts (toRow data26.row) 3585 512 (toTotals ⟨135335948748, 158513368064, 277982619136, 15866697676, 302091905⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G22.checked0183
#print axioms piece0183

theorem piece0184 : ChunkFacts (toRow data26.row) 4097 2 (toTotals ⟨495219669, 619192844, 1085869606, 28542907, 27966⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0184
#print axioms piece0184

theorem join26_00 : ChunkFacts (toRow data26.row) 1 1024 (toTotals ⟨1166622477205183, 5964375069830, 22210126072903, 1150376726202110, 3574816608⟩) :=
  CleanupSegments208.append_exact piece0176 piece0177 rfl rfl rfl
#print axioms join26_00

theorem join26_01 : ChunkFacts (toRow data26.row) 1025 1024 (toTotals ⟨11826763095092, 1385753584872, 2677544834368, 10534971845596, 1498524806⟩) :=
  CleanupSegments208.append_exact piece0178 piece0179 rfl rfl rfl
#print axioms join26_01

theorem join26_02 : ChunkFacts (toRow data26.row) 2049 1024 (toTotals ⟨883088574825, 454177951074, 796485356001, 540781169898, 698031799⟩) :=
  CleanupSegments208.append_exact piece0180 piece0181 rfl rfl rfl
#print axioms join26_02

theorem join26_03 : ChunkFacts (toRow data26.row) 3073 1024 (toTotals ⟨291285372646, 317026736128, 555965238272, 52346870502, 598499487⟩) :=
  CleanupSegments208.append_exact piece0182 piece0183 rfl rfl rfl
#print axioms join26_03

theorem join26_04 : ChunkFacts (toRow data26.row) 1 2048 (toTotals ⟨1178449240300275, 7350128654702, 24887670907271, 1160911698047706, 5073341414⟩) :=
  CleanupSegments208.append_exact join26_00 join26_01 rfl rfl rfl
#print axioms join26_04

theorem join26_05 : ChunkFacts (toRow data26.row) 2049 2048 (toTotals ⟨1174373947471, 771204687202, 1352450594273, 593128040400, 1296531286⟩) :=
  CleanupSegments208.append_exact join26_02 join26_03 rfl rfl rfl
#print axioms join26_05

theorem join26_06 : ChunkFacts (toRow data26.row) 1 4096 (toTotals ⟨1179623614247746, 8121333341904, 26240121501544, 1161504826088106, 6369872700⟩) :=
  CleanupSegments208.append_exact join26_04 join26_05 rfl rfl rfl
#print axioms join26_06

theorem join26_07 : ChunkFacts (toRow data26.row) 1 4098 (toTotals ⟨1179624109467415, 8121952534748, 26241207371150, 1161504854631013, 6369900666⟩) :=
  CleanupSegments208.append_exact join26_06 piece0184 rfl rfl rfl
#print axioms join26_07

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) := join26_07
#print axioms fact26

theorem piece0185 : ChunkFacts (toRow data27.row) 1 512 (toTotals ⟨1126906376934723, 4465149053308, 18359539669973, 1113011986318058, 2380742647⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0185
#print axioms piece0185

theorem piece0186 : ChunkFacts (toRow data27.row) 513 512 (toTotals ⟨51346855560002, 2124685511580, 4318001723881, 49153539347701, 1411336713⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0186
#print axioms piece0186

theorem piece0187 : ChunkFacts (toRow data27.row) 1025 512 (toTotals ⟨10024537882040, 1023290903708, 1869967114151, 9177861671597, 945138623⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0187
#print axioms piece0187

theorem piece0188 : ChunkFacts (toRow data27.row) 1537 512 (toTotals ⟨3655916610663, 625491529110, 1113607389118, 3167800750655, 731526498⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0188
#print axioms piece0188

theorem piece0189 : ChunkFacts (toRow data27.row) 2049 512 (toTotals ⟨854840821013, 346502450253, 568452738741, 632890532525, 468824693⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0189
#print axioms piece0189

theorem piece0190 : ChunkFacts (toRow data27.row) 2561 512 (toTotals ⟨385247626370, 242915757866, 398514145402, 229649238834, 378577974⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0190
#print axioms piece0190

theorem piece0191 : ChunkFacts (toRow data27.row) 3073 512 (toTotals ⟨155949423898, 169445324288, 277982619136, 47412129050, 306632734⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G23.checked0191
#print axioms piece0191

theorem piece0192 : ChunkFacts (toRow data27.row) 3585 512 (toTotals ⟨135335948748, 169445324288, 277982619136, 26798653900, 330896251⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G24.checked0192
#print axioms piece0192

theorem piece0193 : ChunkFacts (toRow data27.row) 4097 381 (toTotals ⟨90287723128, 126091149519, 206858159943, 9520712704, 237690258⟩) :=
  CleanupFastSound208.check_sound CleanupChecks250262G24.checked0193
#print axioms piece0193

theorem join27_00 : ChunkFacts (toRow data27.row) 1 1024 (toTotals ⟨1178253232494725, 6589834564888, 22677541393854, 1162165525665759, 3792079360⟩) :=
  CleanupSegments208.append_exact piece0185 piece0186 rfl rfl rfl
#print axioms join27_00

theorem join27_01 : ChunkFacts (toRow data27.row) 1025 1024 (toTotals ⟨13680454492703, 1648782432818, 2983574503269, 12345662422252, 1676665121⟩) :=
  CleanupSegments208.append_exact piece0187 piece0188 rfl rfl rfl
#print axioms join27_01

theorem join27_02 : ChunkFacts (toRow data27.row) 2049 1024 (toTotals ⟨1240088447383, 589418208119, 966966884143, 862539771359, 847402667⟩) :=
  CleanupSegments208.append_exact piece0189 piece0190 rfl rfl rfl
#print axioms join27_02

theorem join27_03 : ChunkFacts (toRow data27.row) 3073 1024 (toTotals ⟨291285372646, 338890648576, 555965238272, 74210782950, 637528985⟩) :=
  CleanupSegments208.append_exact piece0191 piece0192 rfl rfl rfl
#print axioms join27_03

theorem join27_04 : ChunkFacts (toRow data27.row) 1 2048 (toTotals ⟨1191933686987428, 8238616997706, 25661115897123, 1174511188088011, 5468744481⟩) :=
  CleanupSegments208.append_exact join27_00 join27_01 rfl rfl rfl
#print axioms join27_04

theorem join27_05 : ChunkFacts (toRow data27.row) 2049 2048 (toTotals ⟨1531373820029, 928308856695, 1522932122415, 936750554309, 1484931652⟩) :=
  CleanupSegments208.append_exact join27_02 join27_03 rfl rfl rfl
#print axioms join27_05

theorem join27_06 : ChunkFacts (toRow data27.row) 1 4096 (toTotals ⟨1193465060807457, 9166925854401, 27184048019538, 1175447938642320, 6953676133⟩) :=
  CleanupSegments208.append_exact join27_04 join27_05 rfl rfl rfl
#print axioms join27_06

theorem join27_07 : ChunkFacts (toRow data27.row) 1 4477 (toTotals ⟨1193555348530585, 9293017003920, 27390906179481, 1175457459355024, 7191366391⟩) :=
  CleanupSegments208.append_exact join27_06 piece0193 rfl rfl rfl
#print axioms join27_07

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) := join27_07
#print axioms fact27

theorem all_facts {k : ℕ} (hk : k < 28) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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

#print axioms all_facts
end JSP233.CleanupFacts250262
