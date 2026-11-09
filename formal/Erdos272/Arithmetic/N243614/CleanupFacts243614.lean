module

public import Erdos272.Arithmetic.N243614.CleanupChecks243614G00
public import Erdos272.Arithmetic.N243614.CleanupChecks243614G01
public import Erdos272.Arithmetic.N243614.CleanupChecks243614G02
public import Erdos272.Arithmetic.N243614.CleanupChecks243614G03
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts243614
open CleanupRows243614 CleanupEval208 CleanupMachineSound208
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem piece0000 : ChunkFacts (toRow data00.row) 1 512 (toTotals ⟨869426826482171, 1166499332475, 15827263777841, 854766062036805, 1350654284⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0000
#print axioms piece0000

theorem piece0001 : ChunkFacts (toRow data00.row) 513 512 (toTotals ⟨16858650932653, 331539347925, 2046010668015, 15144179612563, 565108227⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0001
#print axioms piece0001

theorem piece0002 : ChunkFacts (toRow data00.row) 1025 512 (toTotals ⟨1826401962175, 128406915825, 685917125382, 1268891752618, 275331018⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0002
#print axioms piece0002

theorem piece0003 : ChunkFacts (toRow data00.row) 1537 512 (toTotals ⟨289681949558, 64518489600, 301887994880, 52312444278, 156507564⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0003
#print axioms piece0003

theorem piece0004 : ChunkFacts (toRow data00.row) 2049 97 (toTotals ⟨46659104344, 12223229475, 57193624030, 1688709789, 27626989⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0004
#print axioms piece0004

theorem join00_00 : ChunkFacts (toRow data00.row) 1 1024 (toTotals ⟨886285477414824, 1498038680400, 17873274445856, 869910241649368, 1915762511⟩) :=
  CleanupSegments208.append_exact piece0000 piece0001 rfl rfl rfl
#print axioms join00_00

theorem join00_01 : ChunkFacts (toRow data00.row) 1025 1024 (toTotals ⟨2116083911733, 192925405425, 987805120262, 1321204196896, 431838582⟩) :=
  CleanupSegments208.append_exact piece0002 piece0003 rfl rfl rfl
#print axioms join00_01

theorem join00_02 : ChunkFacts (toRow data00.row) 1 2048 (toTotals ⟨888401561326557, 1690964085825, 18861079566118, 871231445846264, 2347601093⟩) :=
  CleanupSegments208.append_exact join00_00 join00_01 rfl rfl rfl
#print axioms join00_02

theorem join00_03 : ChunkFacts (toRow data00.row) 1 2145 (toTotals ⟨888448220430901, 1703187315300, 18918273190148, 871233134556053, 2375228082⟩) :=
  CleanupSegments208.append_exact join00_02 piece0004 rfl rfl rfl
#print axioms join00_03

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) := join00_03
#print axioms fact00

theorem piece0005 : ChunkFacts (toRow data01.row) 1 512 (toTotals ⟨917561295484712, 1861227534375, 16525778161511, 902896744857576, 1486068068⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0005
#print axioms piece0005

theorem piece0006 : ChunkFacts (toRow data01.row) 513 512 (toTotals ⟨22150522035801, 597787870500, 2472592396510, 20275717509791, 677621217⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0006
#print axioms piece0006

theorem piece0007 : ChunkFacts (toRow data01.row) 1025 512 (toTotals ⟨3026925920809, 255907353375, 929013931268, 2353819342916, 381251443⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G00.checked0007
#print axioms piece0007

theorem piece0008 : ChunkFacts (toRow data01.row) 1537 512 (toTotals ⟨298809291462, 94753401750, 305425744820, 88136948392, 170235826⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0008
#print axioms piece0008

theorem piece0009 : ChunkFacts (toRow data01.row) 2049 388 (toTotals ⟨175031953484, 70973590500, 228774496120, 17231047864, 132052502⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0009
#print axioms piece0009

theorem join01_00 : ChunkFacts (toRow data01.row) 1 1024 (toTotals ⟨939711817520513, 2459015404875, 18998370558021, 923172462367367, 2163689285⟩) :=
  CleanupSegments208.append_exact piece0005 piece0006 rfl rfl rfl
#print axioms join01_00

theorem join01_01 : ChunkFacts (toRow data01.row) 1025 1024 (toTotals ⟨3325735212271, 350660755125, 1234439676088, 2441956291308, 551487269⟩) :=
  CleanupSegments208.append_exact piece0007 piece0008 rfl rfl rfl
#print axioms join01_01

theorem join01_02 : ChunkFacts (toRow data01.row) 1 2048 (toTotals ⟨943037552732784, 2809676160000, 20232810234109, 925614418658675, 2715176554⟩) :=
  CleanupSegments208.append_exact join01_00 join01_01 rfl rfl rfl
#print axioms join01_02

theorem join01_03 : ChunkFacts (toRow data01.row) 1 2436 (toTotals ⟨943212584686268, 2880649750500, 20461584730229, 925631649706539, 2847229056⟩) :=
  CleanupSegments208.append_exact join01_02 piece0009 rfl rfl rfl
#print axioms join01_03

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) := join01_03
#print axioms fact01

theorem piece0010 : ChunkFacts (toRow data02.row) 1 512 (toTotals ⟨957112762657938, 2547086058932, 17116562481903, 942543286234967, 1621357153⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0010
#print axioms piece0010

theorem piece0011 : ChunkFacts (toRow data02.row) 513 512 (toTotals ⟨27985808096776, 916144662696, 2928874491907, 25973078267565, 797640975⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0011
#print axioms piece0011

theorem piece0012 : ChunkFacts (toRow data02.row) 1025 512 (toTotals ⟨4322085864654, 401537354692, 1142167349142, 3581455870204, 482113614⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0012
#print axioms piece0012

theorem piece0013 : ChunkFacts (toRow data02.row) 1537 512 (toTotals ⟨563681205708, 159641798836, 409307309788, 314015694756, 225279020⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0013
#print axioms piece0013

theorem piece0014 : ChunkFacts (toRow data02.row) 2049 512 (toTotals ⟨225175972204, 118630770688, 301887994880, 41918748012, 195184230⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0014
#print axioms piece0014

theorem piece0015 : ChunkFacts (toRow data02.row) 2561 198 (toTotals ⟨75289356181, 45876743352, 116745748020, 4420351513, 73262846⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G01.checked0015
#print axioms piece0015

theorem join02_00 : ChunkFacts (toRow data02.row) 1 1024 (toTotals ⟨985098570754714, 3463230721628, 20045436973810, 968516364502532, 2418998128⟩) :=
  CleanupSegments208.append_exact piece0010 piece0011 rfl rfl rfl
#print axioms join02_00

theorem join02_01 : ChunkFacts (toRow data02.row) 1025 1024 (toTotals ⟨4885767070362, 561179153528, 1551474658930, 3895471564960, 707392634⟩) :=
  CleanupSegments208.append_exact piece0012 piece0013 rfl rfl rfl
#print axioms join02_01

theorem join02_02 : ChunkFacts (toRow data02.row) 2049 710 (toTotals ⟨300465328385, 164507514040, 418633742900, 46339099525, 268447076⟩) :=
  CleanupSegments208.append_exact piece0014 piece0015 rfl rfl rfl
#print axioms join02_02

theorem join02_03 : ChunkFacts (toRow data02.row) 1 2048 (toTotals ⟨989984337825076, 4024409875156, 21596911632740, 972411836067492, 3126390762⟩) :=
  CleanupSegments208.append_exact join02_00 join02_01 rfl rfl rfl
#print axioms join02_03

theorem join02_04 : ChunkFacts (toRow data02.row) 1 2758 (toTotals ⟨990284803153461, 4188917389196, 22015545375640, 972458175167017, 3394837838⟩) :=
  CleanupSegments208.append_exact join02_03 join02_02 rfl rfl rfl
#print axioms join02_04

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) := join02_04
#print axioms fact02

theorem piece0016 : ChunkFacts (toRow data03.row) 1 512 (toTotals ⟨1029519519907333, 3848638458304, 18145569640579, 1015222588725058, 1845847155⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0016
#print axioms piece0016

theorem piece0017 : ChunkFacts (toRow data03.row) 513 512 (toTotals ⟨37942956272078, 1601617029208, 3725493709177, 35819079592109, 1014886570⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0017
#print axioms piece0017

theorem piece0018 : ChunkFacts (toRow data03.row) 1025 512 (toTotals ⟨6253865164154, 706439248568, 1454656641992, 5505647770730, 633850851⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0018
#print axioms piece0018

theorem piece0019 : ChunkFacts (toRow data03.row) 1537 512 (toTotals ⟨1695838432615, 386241042416, 764970697414, 1317108777617, 418173848⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0019
#print axioms piece0019

theorem piece0020 : ChunkFacts (toRow data03.row) 2049 512 (toTotals ⟨402414715921, 210022479304, 395638368290, 216798826935, 270177725⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0020
#print axioms piece0020

theorem piece0021 : ChunkFacts (toRow data03.row) 2561 512 (toTotals ⟨184370250466, 160255602688, 301887994880, 42737858274, 238833171⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0021
#print axioms piece0021

theorem piece0022 : ChunkFacts (toRow data03.row) 3073 463 (toTotals ⟨142245229031, 144918640712, 272996370370, 14167499373, 220312696⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0022
#print axioms piece0022

theorem join03_00 : ChunkFacts (toRow data03.row) 1 1024 (toTotals ⟨1067462476179411, 5450255487512, 21871063349756, 1051041668317167, 2860733725⟩) :=
  CleanupSegments208.append_exact piece0016 piece0017 rfl rfl rfl
#print axioms join03_00

theorem join03_01 : ChunkFacts (toRow data03.row) 1025 1024 (toTotals ⟨7949703596769, 1092680290984, 2219627339406, 6822756548347, 1052024699⟩) :=
  CleanupSegments208.append_exact piece0018 piece0019 rfl rfl rfl
#print axioms join03_01

theorem join03_02 : ChunkFacts (toRow data03.row) 2049 1024 (toTotals ⟨586784966387, 370278081992, 697526363170, 259536685209, 509010896⟩) :=
  CleanupSegments208.append_exact piece0020 piece0021 rfl rfl rfl
#print axioms join03_02

theorem join03_03 : ChunkFacts (toRow data03.row) 1 2048 (toTotals ⟨1075412179776180, 6542935778496, 24090690689162, 1057864424865514, 3912758424⟩) :=
  CleanupSegments208.append_exact join03_00 join03_01 rfl rfl rfl
#print axioms join03_03

theorem join03_04 : ChunkFacts (toRow data03.row) 2049 1487 (toTotals ⟨729030195418, 515196722704, 970522733540, 273704184582, 729323592⟩) :=
  CleanupSegments208.append_exact join03_02 piece0022 rfl rfl rfl
#print axioms join03_04

theorem join03_05 : ChunkFacts (toRow data03.row) 1 3535 (toTotals ⟨1076141209971598, 7058132501200, 25061213422702, 1058138129050096, 4642082016⟩) :=
  CleanupSegments208.append_exact join03_03 join03_04 rfl rfl rfl
#print axioms join03_05

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) := join03_05
#print axioms fact03

theorem piece0023 : ChunkFacts (toRow data04.row) 1 512 (toTotals ⟨1104824695906723, 4850361989868, 19055472551227, 1090619585345364, 2042532176⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G02.checked0023
#print axioms piece0023

theorem piece0024 : ChunkFacts (toRow data04.row) 513 512 (toTotals ⟨46282991828196, 2191653086792, 4359754904657, 44114890010331, 1196558793⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0024
#print axioms piece0024

theorem piece0025 : ChunkFacts (toRow data04.row) 1025 512 (toTotals ⟨8327489985781, 1015873533792, 1800005576212, 7543357943361, 783190376⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0025
#print axioms piece0025

theorem piece0026 : ChunkFacts (toRow data04.row) 1537 512 (toTotals ⟨2887546497342, 605616914376, 1050261545674, 2442901866044, 585665062⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0026
#print axioms piece0026

theorem piece0027 : ChunkFacts (toRow data04.row) 2049 512 (toTotals ⟨709858604659, 343327629476, 559554115510, 493632118625, 389981550⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0027
#print axioms piece0027

theorem piece0028 : ChunkFacts (toRow data04.row) 2561 512 (toTotals ⟨302189443833, 232261684008, 378539243580, 155911884261, 305821403⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0028
#print axioms piece0028

theorem piece0029 : ChunkFacts (toRow data04.row) 3073 512 (toTotals ⟨156208672538, 185230501888, 301887994880, 39551179546, 279350500⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0029
#print axioms piece0029

theorem piece0030 : ChunkFacts (toRow data04.row) 3585 512 (toTotals ⟨135595197388, 185230501888, 301887994880, 18937704396, 302518119⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0030
#print axioms piece0030

theorem piece0031 : ChunkFacts (toRow data04.row) 4097 158 (toTotals ⟨38486553760, 57160975192, 93160748420, 2486780532, 75660407⟩) :=
  CleanupFastSound208.check_sound CleanupChecks243614G03.checked0031
#print axioms piece0031

theorem join04_00 : ChunkFacts (toRow data04.row) 1 1024 (toTotals ⟨1151107687734919, 7042015076660, 23415227455884, 1134734475355695, 3239090969⟩) :=
  CleanupSegments208.append_exact piece0023 piece0024 rfl rfl rfl
#print axioms join04_00

theorem join04_01 : ChunkFacts (toRow data04.row) 1025 1024 (toTotals ⟨11215036483123, 1621490448168, 2850267121886, 9986259809405, 1368855438⟩) :=
  CleanupSegments208.append_exact piece0025 piece0026 rfl rfl rfl
#print axioms join04_01

theorem join04_02 : ChunkFacts (toRow data04.row) 2049 1024 (toTotals ⟨1012048048492, 575589313484, 938093359090, 649544002886, 695802953⟩) :=
  CleanupSegments208.append_exact piece0027 piece0028 rfl rfl rfl
#print axioms join04_02

theorem join04_03 : ChunkFacts (toRow data04.row) 3073 1024 (toTotals ⟨291803869926, 370461003776, 603775989760, 58488883942, 581868619⟩) :=
  CleanupSegments208.append_exact piece0029 piece0030 rfl rfl rfl
#print axioms join04_03

theorem join04_04 : ChunkFacts (toRow data04.row) 1 2048 (toTotals ⟨1162322724218042, 8663505524828, 26265494577770, 1144720735165100, 4607946407⟩) :=
  CleanupSegments208.append_exact join04_00 join04_01 rfl rfl rfl
#print axioms join04_04

theorem join04_05 : ChunkFacts (toRow data04.row) 2049 2048 (toTotals ⟨1303851918418, 946050317260, 1541869348850, 708032886828, 1277671572⟩) :=
  CleanupSegments208.append_exact join04_02 join04_03 rfl rfl rfl
#print axioms join04_05

theorem join04_06 : ChunkFacts (toRow data04.row) 1 4096 (toTotals ⟨1163626576136460, 9609555842088, 27807363926620, 1145428768051928, 5885617979⟩) :=
  CleanupSegments208.append_exact join04_04 join04_05 rfl rfl rfl
#print axioms join04_06

theorem join04_07 : ChunkFacts (toRow data04.row) 1 4254 (toTotals ⟨1163665062690220, 9666716817280, 27900524675040, 1145431254832460, 5961278386⟩) :=
  CleanupSegments208.append_exact join04_06 piece0031 rfl rfl rfl
#print axioms join04_07

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) := join04_07
#print axioms fact04

theorem all_facts {k : ℕ} (hk : k < 5) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
  interval_cases k
  · exact fact00
  · exact fact01
  · exact fact02
  · exact fact03
  · exact fact04

#print axioms all_facts
end JSP233.CleanupFacts243614
