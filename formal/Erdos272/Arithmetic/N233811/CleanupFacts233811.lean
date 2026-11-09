module

public import Erdos272.Arithmetic.N233811.CleanupChecks233811G00
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G01
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G02
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G03
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G04
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G05
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G06
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G07
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G08
public import Erdos272.Arithmetic.N233811.CleanupChecks233811G09
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts233811
open CleanupRows233811 CleanupEval208 CleanupMachineSound208
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem piece0000 : ChunkFacts (toRow data00.row) 1 512 (toTotals ⟨868550944318947, 1165780386621, 15937154826665, 853779569878903, 1283711815⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0000
#print axioms piece0000

theorem piece0001 : ChunkFacts (toRow data00.row) 513 512 (toTotals ⟨16035979567993, 323128747442, 2006974957671, 14352133357764, 529633823⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0001
#print axioms piece0001

theorem piece0002 : ChunkFacts (toRow data00.row) 1025 512 (toTotals ⟨1653024239805, 121522849156, 654351568940, 1120195520021, 250355003⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0002
#print axioms piece0002

theorem piece0003 : ChunkFacts (toRow data00.row) 1537 512 (toTotals ⟨289770153846, 65083366912, 308043401216, 46810119542, 150468147⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0003
#print axioms piece0003

theorem piece0004 : ChunkFacts (toRow data00.row) 2049 47 (toTotals ⟨22883518315, 5974449697, 28277421596, 580546416, 11517411⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0004
#print axioms piece0004

theorem join00_00 : ChunkFacts (toRow data00.row) 1 1024 (toTotals ⟨884586923886940, 1488909134063, 17944129784336, 868131703236667, 1813345638⟩) :=
  CleanupSegments208.append_exact piece0000 piece0001 rfl rfl rfl
#print axioms join00_00

theorem join00_01 : ChunkFacts (toRow data00.row) 1025 1024 (toTotals ⟨1942794393651, 186606216068, 962394970156, 1167005639563, 400823150⟩) :=
  CleanupSegments208.append_exact piece0002 piece0003 rfl rfl rfl
#print axioms join00_01

theorem join00_02 : ChunkFacts (toRow data00.row) 1 2048 (toTotals ⟨886529718280591, 1675515350131, 18906524754492, 869298708876230, 2214168788⟩) :=
  CleanupSegments208.append_exact join00_00 join00_01 rfl rfl rfl
#print axioms join00_02

theorem join00_03 : ChunkFacts (toRow data00.row) 1 2095 (toTotals ⟨886552601798906, 1681489799828, 18934802176088, 869299289422646, 2225686199⟩) :=
  CleanupSegments208.append_exact join00_02 piece0004 rfl rfl rfl
#print axioms join00_03

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) := join00_03
#print axioms fact00

theorem piece0005 : ChunkFacts (toRow data01.row) 1 512 (toTotals ⟨915021373176615, 1879841538507, 16637231588051, 900263983127071, 1416341510⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0005
#print axioms piece0005

theorem piece0006 : ChunkFacts (toRow data01.row) 513 512 (toTotals ⟨21262785163048, 590445120743, 2433542870803, 19419687412988, 637129099⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0006
#print axioms piece0006

theorem piece0007 : ChunkFacts (toRow data01.row) 1025 512 (toTotals ⟨2842014183275, 249452343402, 905840127036, 2185626399641, 352259375⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G00.checked0007
#print axioms piece0007

theorem piece0008 : ChunkFacts (toRow data01.row) 1537 512 (toTotals ⟨289770153846, 95455605248, 308043401216, 77182357878, 163316787⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0008
#print axioms piece0008

theorem piece0009 : ChunkFacts (toRow data01.row) 2049 338 (toTotals ⟨154152210278, 63015614402, 203356776584, 13811048096, 109912569⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0009
#print axioms piece0009

theorem join01_00 : ChunkFacts (toRow data01.row) 1 1024 (toTotals ⟨936284158339663, 2470286659250, 19070774458854, 919683670540059, 2053470609⟩) :=
  CleanupSegments208.append_exact piece0005 piece0006 rfl rfl rfl
#print axioms join01_00

theorem join01_01 : ChunkFacts (toRow data01.row) 1025 1024 (toTotals ⟨3131784337121, 344907948650, 1213883528252, 2262808757519, 515576162⟩) :=
  CleanupSegments208.append_exact piece0007 piece0008 rfl rfl rfl
#print axioms join01_01

theorem join01_02 : ChunkFacts (toRow data01.row) 1 2048 (toTotals ⟨939415942676784, 2815194607900, 20284657987106, 921946479297578, 2569046771⟩) :=
  CleanupSegments208.append_exact join01_00 join01_01 rfl rfl rfl
#print axioms join01_02

theorem join01_03 : ChunkFacts (toRow data01.row) 1 2386 (toTotals ⟨939570094887062, 2878210222302, 20488014763690, 921960290345674, 2678959340⟩) :=
  CleanupSegments208.append_exact join01_02 piece0009 rfl rfl rfl
#print axioms join01_03

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) := join01_03
#print axioms fact01

theorem piece0010 : ChunkFacts (toRow data02.row) 1 512 (toTotals ⟨958425108320245, 2581877509029, 17246339282429, 943760646546845, 1545223912⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0010
#print axioms piece0010

theorem piece0011 : ChunkFacts (toRow data02.row) 513 512 (toTotals ⟨26778314823096, 909031590579, 2878882178690, 24808464234985, 750038150⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0011
#print axioms piece0011

theorem piece0012 : ChunkFacts (toRow data02.row) 1025 512 (toTotals ⟨4129589048232, 397923773793, 1127125992264, 3400386829761, 450633859⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0012
#print axioms piece0012

theorem piece0013 : ChunkFacts (toRow data02.row) 1537 512 (toTotals ⟨497631631900, 154945870177, 392875666004, 259701836073, 209380476⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0013
#print axioms piece0013

theorem piece0014 : ChunkFacts (toRow data02.row) 2049 512 (toTotals ⟨225264176492, 121488951808, 308043401216, 38709727084, 188881884⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0014
#print axioms piece0014

theorem piece0015 : ChunkFacts (toRow data02.row) 2561 147 (toTotals ⟨56446015631, 34880617023, 88442148396, 2884484258, 51177681⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G01.checked0015
#print axioms piece0015

theorem join02_00 : ChunkFacts (toRow data02.row) 1 1024 (toTotals ⟨985203423143341, 3490909099608, 20125221461119, 968569110781830, 2295262062⟩) :=
  CleanupSegments208.append_exact piece0010 piece0011 rfl rfl rfl
#print axioms join02_00

theorem join02_01 : ChunkFacts (toRow data02.row) 1025 1024 (toTotals ⟨4627220680132, 552869643970, 1520001658268, 3660088665834, 660014335⟩) :=
  CleanupSegments208.append_exact piece0012 piece0013 rfl rfl rfl
#print axioms join02_01

theorem join02_02 : ChunkFacts (toRow data02.row) 2049 659 (toTotals ⟨281710192123, 156369568831, 396485549612, 41594211342, 240059565⟩) :=
  CleanupSegments208.append_exact piece0014 piece0015 rfl rfl rfl
#print axioms join02_02

theorem join02_03 : ChunkFacts (toRow data02.row) 1 2048 (toTotals ⟨989830643823473, 4043778743578, 21645223119387, 972229199447664, 2955276397⟩) :=
  CleanupSegments208.append_exact join02_00 join02_01 rfl rfl rfl
#print axioms join02_03

theorem join02_04 : ChunkFacts (toRow data02.row) 1 2707 (toTotals ⟨990112354015596, 4200148312409, 22041708668999, 972270793659006, 3195335962⟩) :=
  CleanupSegments208.append_exact join02_03 join02_02 rfl rfl rfl
#print axioms join02_04

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) := join02_04
#print axioms fact02

theorem piece0016 : ChunkFacts (toRow data03.row) 1 512 (toTotals ⟨982338896427826, 3162060136551, 17647036363205, 967853920201172, 1651701168⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0016
#print axioms piece0016

theorem piece0017 : ChunkFacts (toRow data03.row) 513 512 (toTotals ⟨31360691054791, 1223491031875, 3260567205652, 29323614881014, 850840453⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0017
#print axioms piece0017

theorem piece0018 : ChunkFacts (toRow data03.row) 1025 512 (toTotals ⟨5067158796787, 543369845699, 1292218002620, 4318310639866, 530653627⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0018
#print axioms piece0018

theorem piece0019 : ChunkFacts (toRow data03.row) 1537 512 (toTotals ⟨915797738335, 248893032770, 549905603000, 614785168105, 287560758⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0019
#print axioms piece0019

theorem piece0020 : ChunkFacts (toRow data03.row) 2049 512 (toTotals ⟨225264176492, 143183407616, 308043401216, 60404182892, 200680924⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0020
#print axioms piece0020

theorem piece0021 : ChunkFacts (toRow data03.row) 2561 490 (toTotals ⟨177179185579, 137030995570, 294807161320, 19403019829, 199795012⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0021
#print axioms piece0021

theorem join03_00 : ChunkFacts (toRow data03.row) 1 1024 (toTotals ⟨1013699587482617, 4385551168426, 20907603568857, 997177535082186, 2502541621⟩) :=
  CleanupSegments208.append_exact piece0016 piece0017 rfl rfl rfl
#print axioms join03_00

theorem join03_01 : ChunkFacts (toRow data03.row) 1025 1024 (toTotals ⟨5982956535122, 792262878469, 1842123605620, 4933095807971, 818214385⟩) :=
  CleanupSegments208.append_exact piece0018 piece0019 rfl rfl rfl
#print axioms join03_01

theorem join03_02 : ChunkFacts (toRow data03.row) 2049 1002 (toTotals ⟨402443362071, 280214403186, 602850562536, 79807202721, 400475936⟩) :=
  CleanupSegments208.append_exact piece0020 piece0021 rfl rfl rfl
#print axioms join03_02

theorem join03_03 : ChunkFacts (toRow data03.row) 1 2048 (toTotals ⟨1019682544017739, 5177814046895, 22749727174477, 1002110630890157, 3320756006⟩) :=
  CleanupSegments208.append_exact join03_00 join03_01 rfl rfl rfl
#print axioms join03_03

theorem join03_04 : ChunkFacts (toRow data03.row) 1 3050 (toTotals ⟨1020084987379810, 5458028450081, 23352577737013, 1002190438092878, 3721231942⟩) :=
  CleanupSegments208.append_exact join03_03 join03_02 rfl rfl rfl
#print axioms join03_04

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) := join03_04
#print axioms fact03

theorem piece0022 : ChunkFacts (toRow data04.row) 1 512 (toTotals ⟨1031933793458879, 3816876761467, 18280811595623, 1017469858624723, 1742918097⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0022
#print axioms piece0022

theorem piece0023 : ChunkFacts (toRow data04.row) 513 512 (toTotals ⟨35774103564415, 1531391284236, 3613493493182, 33692001355469, 939090371⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G02.checked0023
#print axioms piece0023

theorem piece0024 : ChunkFacts (toRow data04.row) 1025 512 (toTotals ⟨5891687497314, 675392470566, 1419165576168, 5147914391712, 589666308⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0024
#print axioms piece0024

theorem piece0025 : ChunkFacts (toRow data04.row) 1537 512 (toTotals ⟨1434577016318, 353060316554, 704889939280, 1082747393592, 368518599⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0025
#print axioms piece0025

theorem piece0026 : ChunkFacts (toRow data04.row) 2049 512 (toTotals ⟨340966344029, 192521344906, 369411422552, 164076266383, 241126437⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0026
#print axioms piece0026

theorem piece0027 : ChunkFacts (toRow data04.row) 2561 512 (toTotals ⟨184458454754, 160538971648, 308043401216, 36954025186, 229377878⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0027
#print axioms piece0027

theorem piece0028 : ChunkFacts (toRow data04.row) 3073 322 (toTotals ⟨101029289747, 100963962638, 193730420296, 8262832089, 142515126⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0028
#print axioms piece0028

theorem join04_00 : ChunkFacts (toRow data04.row) 1 1024 (toTotals ⟨1067707897023294, 5348268045703, 21894305088805, 1051161859980192, 2682008468⟩) :=
  CleanupSegments208.append_exact piece0022 piece0023 rfl rfl rfl
#print axioms join04_00

theorem join04_01 : ChunkFacts (toRow data04.row) 1025 1024 (toTotals ⟨7326264513632, 1028452787120, 2124055515448, 6230661785304, 958184907⟩) :=
  CleanupSegments208.append_exact piece0024 piece0025 rfl rfl rfl
#print axioms join04_01

theorem join04_02 : ChunkFacts (toRow data04.row) 2049 1024 (toTotals ⟨525424798783, 353060316554, 677454823768, 201030291569, 470504315⟩) :=
  CleanupSegments208.append_exact piece0026 piece0027 rfl rfl rfl
#print axioms join04_02

theorem join04_03 : ChunkFacts (toRow data04.row) 1 2048 (toTotals ⟨1075034161536926, 6376720832823, 24018360604253, 1057392521765496, 3640193375⟩) :=
  CleanupSegments208.append_exact join04_00 join04_01 rfl rfl rfl
#print axioms join04_03

theorem join04_04 : ChunkFacts (toRow data04.row) 2049 1346 (toTotals ⟨626454088530, 454024279192, 871185244064, 209293123658, 613019441⟩) :=
  CleanupSegments208.append_exact join04_02 piece0028 rfl rfl rfl
#print axioms join04_04

theorem join04_05 : ChunkFacts (toRow data04.row) 1 3394 (toTotals ⟨1075660615625456, 6830745112015, 24889545848317, 1057601814889154, 4253212816⟩) :=
  CleanupSegments208.append_exact join04_03 join04_04 rfl rfl rfl
#print axioms join04_05

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) := join04_05
#print axioms fact04

theorem piece0029 : ChunkFacts (toRow data05.row) 1 512 (toTotals ⟨1078559982020851, 4438329697884, 18808937567812, 1064189374150923, 1855506735⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0029
#print axioms piece0029

theorem piece0030 : ChunkFacts (toRow data05.row) 513 512 (toTotals ⟨40991718868738, 1901595305818, 4014792221054, 38878521953502, 1045137051⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0030
#print axioms piece0030

theorem piece0031 : ChunkFacts (toRow data05.row) 1025 512 (toTotals ⟨7060277744176, 859244507818, 1619032798624, 6300489453370, 674377948⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G03.checked0031
#print axioms piece0031

theorem piece0032 : ChunkFacts (toRow data05.row) 1537 512 (toTotals ⟨2037443580652, 479828817346, 872508868192, 1644763529806, 462175158⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0032
#print axioms piece0032

theorem piece0033 : ChunkFacts (toRow data05.row) 2049 512 (toTotals ⟨539848435194, 279002563598, 483122756204, 335728242588, 317792954⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0033
#print axioms piece0033

theorem piece0034 : ChunkFacts (toRow data05.row) 2561 512 (toTotals ⟨184458454754, 177894536192, 308043401216, 54309589730, 240914262⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0034
#print axioms piece0034

theorem piece0035 : ChunkFacts (toRow data05.row) 3073 512 (toTotals ⟨156296876826, 177894536192, 308043401216, 26148011802, 262287548⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0035
#print axioms piece0035

theorem piece0036 : ChunkFacts (toRow data05.row) 3585 241 (toTotals ⟨66091348063, 83735514106, 144996991588, 4829870581, 114283047⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0036
#print axioms piece0036

theorem join05_00 : ChunkFacts (toRow data05.row) 1 1024 (toTotals ⟨1119551700889589, 6339925003702, 22823729788866, 1103067896104425, 2900643786⟩) :=
  CleanupSegments208.append_exact piece0029 piece0030 rfl rfl rfl
#print axioms join05_00

theorem join05_01 : ChunkFacts (toRow data05.row) 1025 1024 (toTotals ⟨9097721324828, 1339073325164, 2491541666816, 7945252983176, 1136553106⟩) :=
  CleanupSegments208.append_exact piece0031 piece0032 rfl rfl rfl
#print axioms join05_01

theorem join05_02 : ChunkFacts (toRow data05.row) 2049 1024 (toTotals ⟨724306889948, 456897099790, 791166157420, 390037832318, 558707216⟩) :=
  CleanupSegments208.append_exact piece0033 piece0034 rfl rfl rfl
#print axioms join05_02

theorem join05_03 : ChunkFacts (toRow data05.row) 3073 753 (toTotals ⟨222388224889, 261630050298, 453040392804, 30977882383, 376570595⟩) :=
  CleanupSegments208.append_exact piece0035 piece0036 rfl rfl rfl
#print axioms join05_03

theorem join05_04 : ChunkFacts (toRow data05.row) 1 2048 (toTotals ⟨1128649422214417, 7678998328866, 25315271455682, 1111013149087601, 4037196892⟩) :=
  CleanupSegments208.append_exact join05_00 join05_01 rfl rfl rfl
#print axioms join05_04

theorem join05_05 : ChunkFacts (toRow data05.row) 2049 1777 (toTotals ⟨946695114837, 718527150088, 1244206550224, 421015714701, 935277811⟩) :=
  CleanupSegments208.append_exact join05_02 join05_03 rfl rfl rfl
#print axioms join05_05

theorem join05_06 : ChunkFacts (toRow data05.row) 1 3825 (toTotals ⟨1129596117329254, 8397525478954, 26559478005906, 1111434164802302, 4972474703⟩) :=
  CleanupSegments208.append_exact join05_04 join05_05 rfl rfl rfl
#print axioms join05_06

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) := join05_06
#print axioms fact05

theorem piece0037 : ChunkFacts (toRow data06.row) 1 512 (toTotals ⟨1113628948345089, 4985318120090, 19297475149759, 1099316791315420, 1967104263⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0037
#print axioms piece0037

theorem piece0038 : ChunkFacts (toRow data06.row) 513 512 (toTotals ⟨45508630195346, 2235376374715, 4380473430685, 43363533139376, 1148512236⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0038
#print axioms piece0038

theorem piece0039 : ChunkFacts (toRow data06.row) 1025 512 (toTotals ⟨8191549823627, 1034723843175, 1810115970972, 7416157695830, 755143145⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G04.checked0039
#print axioms piece0039

theorem piece0040 : ChunkFacts (toRow data06.row) 1537 512 (toTotals ⟨2767777832922, 610020975652, 1041090432736, 2336708375838, 556088226⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0040
#print axioms piece0040

theorem piece0041 : ChunkFacts (toRow data06.row) 2049 512 (toTotals ⟨696349758013, 350128176123, 564946784652, 481531149484, 376607255⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0041
#print axioms piece0041

theorem piece0042 : ChunkFacts (toRow data06.row) 2561 512 (toTotals ⟨294499614443, 236028898281, 380842720644, 149685792080, 294316656⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0042
#print axioms piece0042

theorem piece0043 : ChunkFacts (toRow data06.row) 3073 512 (toTotals ⟨156296876826, 190911209984, 308043401216, 39164685594, 272512700⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0043
#print axioms piece0043

theorem piece0044 : ChunkFacts (toRow data06.row) 3585 512 (toTotals ⟨135683401676, 190911209984, 308043401216, 18551210444, 295450662⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0044
#print axioms piece0044

theorem piece0045 : ChunkFacts (toRow data06.row) 4097 132 (toTotals ⟨32273679827, 49219296324, 79417439376, 2075536775, 57357049⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0045
#print axioms piece0045

theorem join06_00 : ChunkFacts (toRow data06.row) 1 1024 (toTotals ⟨1159137578540435, 7220694494805, 23677948580444, 1142680324454796, 3115616499⟩) :=
  CleanupSegments208.append_exact piece0037 piece0038 rfl rfl rfl
#print axioms join06_00

theorem join06_01 : ChunkFacts (toRow data06.row) 1025 1024 (toTotals ⟨10959327656549, 1644744818827, 2851206403708, 9752866071668, 1311231371⟩) :=
  CleanupSegments208.append_exact piece0039 piece0040 rfl rfl rfl
#print axioms join06_01

theorem join06_02 : ChunkFacts (toRow data06.row) 2049 1024 (toTotals ⟨990849372456, 586157074404, 945789505296, 631216941564, 670923911⟩) :=
  CleanupSegments208.append_exact piece0041 piece0042 rfl rfl rfl
#print axioms join06_02

theorem join06_03 : ChunkFacts (toRow data06.row) 3073 1024 (toTotals ⟨291980278502, 381822419968, 616086802432, 57715896038, 567963362⟩) :=
  CleanupSegments208.append_exact piece0043 piece0044 rfl rfl rfl
#print axioms join06_03

theorem join06_04 : ChunkFacts (toRow data06.row) 1 2048 (toTotals ⟨1170096906196984, 8865439313632, 26529154984152, 1152433190526464, 4426847870⟩) :=
  CleanupSegments208.append_exact join06_00 join06_01 rfl rfl rfl
#print axioms join06_04

theorem join06_05 : ChunkFacts (toRow data06.row) 2049 2048 (toTotals ⟨1282829650958, 967979494372, 1561876307728, 688932837602, 1238887273⟩) :=
  CleanupSegments208.append_exact join06_02 join06_03 rfl rfl rfl
#print axioms join06_05

theorem join06_06 : ChunkFacts (toRow data06.row) 1 4096 (toTotals ⟨1171379735847942, 9833418808004, 28091031291880, 1153122123364066, 5665735143⟩) :=
  CleanupSegments208.append_exact join06_04 join06_05 rfl rfl rfl
#print axioms join06_06

theorem join06_07 : ChunkFacts (toRow data06.row) 1 4228 (toTotals ⟨1171412009527769, 9882638104328, 28170448731256, 1153124198900841, 5723092192⟩) :=
  CleanupSegments208.append_exact join06_06 piece0045 rfl rfl rfl
#print axioms join06_07

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) := join06_07
#print axioms fact06

theorem piece0046 : ChunkFacts (toRow data07.row) 1 512 (toTotals ⟨871569283048395, 1144452837426, 15893140812754, 856820595073067, 1311357001⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0046
#print axioms piece0046

theorem piece0047 : ChunkFacts (toRow data07.row) 513 512 (toTotals ⟨16187827797526, 318415309782, 2010337145074, 14495905962234, 542239330⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G05.checked0047
#print axioms piece0047

theorem piece0048 : ChunkFacts (toRow data07.row) 1025 512 (toTotals ⟨1684584761842, 120743882130, 660252188564, 1145076455408, 258596354⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0048
#print axioms piece0048

theorem piece0049 : ChunkFacts (toRow data07.row) 1537 512 (toTotals ⟨289725136758, 63732853248, 305943757312, 47514232694, 153031977⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0049
#print axioms piece0049

theorem piece0050 : ChunkFacts (toRow data07.row) 2049 54 (toTotals ⟨26243355234, 6721824366, 32267505654, 697673946, 13875472⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0050
#print axioms piece0050

theorem join07_00 : ChunkFacts (toRow data07.row) 1 1024 (toTotals ⟨887757110845921, 1462868147208, 17903477957828, 871316501035301, 1853596331⟩) :=
  CleanupSegments208.append_exact piece0046 piece0047 rfl rfl rfl
#print axioms join07_00

theorem join07_01 : ChunkFacts (toRow data07.row) 1025 1024 (toTotals ⟨1974309898600, 184476735378, 966195945876, 1192590688102, 411628331⟩) :=
  CleanupSegments208.append_exact piece0048 piece0049 rfl rfl rfl
#print axioms join07_01

theorem join07_02 : ChunkFacts (toRow data07.row) 1 2048 (toTotals ⟨889731420744521, 1647344882586, 18869673903704, 872509091723403, 2265224662⟩) :=
  CleanupSegments208.append_exact join07_00 join07_01 rfl rfl rfl
#print axioms join07_02

theorem join07_03 : ChunkFacts (toRow data07.row) 1 2102 (toTotals ⟨889757664099755, 1654066706952, 18901941409358, 872509789397349, 2279100134⟩) :=
  CleanupSegments208.append_exact join07_02 piece0050 rfl rfl rfl
#print axioms join07_03

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) := join07_03
#print axioms fact07

theorem piece0051 : ChunkFacts (toRow data08.row) 1 512 (toTotals ⟨919236323091384, 1846310881797, 16581737838446, 904500896134735, 1442021453⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0051
#print axioms piece0051

theorem piece0052 : ChunkFacts (toRow data08.row) 513 512 (toTotals ⟨21338932934559, 578923346799, 2425448971383, 19492407309975, 649360281⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0052
#print axioms piece0052

theorem piece0053 : ChunkFacts (toRow data08.row) 1025 512 (toTotals ⟨2851164295986, 245188916667, 904120224160, 2192232988493, 360220891⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0053
#print axioms piece0053

theorem piece0054 : ChunkFacts (toRow data08.row) 1537 512 (toTotals ⟨289725136758, 93474851328, 305943757312, 77256230774, 165880617⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0054
#print axioms piece0054

theorem piece0055 : ChunkFacts (toRow data08.row) 2049 340 (toTotals ⟨154968486889, 62073143460, 203165776340, 13875854009, 112391963⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G06.checked0055
#print axioms piece0055

theorem join08_00 : ChunkFacts (toRow data08.row) 1 1024 (toTotals ⟨940575256025943, 2425234228596, 19007186809829, 923993303444710, 2091381734⟩) :=
  CleanupSegments208.append_exact piece0051 piece0052 rfl rfl rfl
#print axioms join08_00

theorem join08_01 : ChunkFacts (toRow data08.row) 1025 1024 (toTotals ⟨3140889432744, 338663767995, 1210063981472, 2269489219267, 526101508⟩) :=
  CleanupSegments208.append_exact piece0053 piece0054 rfl rfl rfl
#print axioms join08_01

theorem join08_02 : ChunkFacts (toRow data08.row) 1 2048 (toTotals ⟨943716145458687, 2763897996591, 20217250791301, 926262792663977, 2617483242⟩) :=
  CleanupSegments208.append_exact join08_00 join08_01 rfl rfl rfl
#print axioms join08_02

theorem join08_03 : ChunkFacts (toRow data08.row) 1 2388 (toTotals ⟨943871113945576, 2825971140051, 20420416567641, 926276668517986, 2729875205⟩) :=
  CleanupSegments208.append_exact join08_02 piece0055 rfl rfl rfl
#print axioms join08_03

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) := join08_03
#print axioms fact08

theorem piece0056 : ChunkFacts (toRow data09.row) 1 512 (toTotals ⟨961346547593611, 2537364222120, 17188922215738, 946694989599993, 1577280796⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0056
#print axioms piece0056

theorem piece0057 : ChunkFacts (toRow data09.row) 513 512 (toTotals ⟨27092857932423, 895977696016, 2884494685458, 25104340942981, 767402296⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0057
#print axioms piece0057

theorem piece0058 : ChunkFacts (toRow data09.row) 1025 512 (toTotals ⟨4160293269180, 393616757534, 1132956106078, 3420953920636, 464039559⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0058
#print axioms piece0058

theorem piece0059 : ChunkFacts (toRow data09.row) 1537 512 (toTotals ⟨495216972348, 151265944011, 389238473658, 257244442701, 211689694⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0059
#print axioms piece0059

theorem piece0060 : ChunkFacts (toRow data09.row) 2049 512 (toTotals ⟨225219159404, 118967992832, 305943757312, 38243394924, 191441054⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0060
#print axioms piece0060

theorem piece0061 : ChunkFacts (toRow data09.row) 2561 143 (toTotals ⟨54938023664, 33227388623, 85449135343, 2716276944, 50179859⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0061
#print axioms piece0061

theorem join09_00 : ChunkFacts (toRow data09.row) 1 1024 (toTotals ⟨988439405526034, 3433341918136, 20073416901196, 971799330542974, 2344683092⟩) :=
  CleanupSegments208.append_exact piece0056 piece0057 rfl rfl rfl
#print axioms join09_00

theorem join09_01 : ChunkFacts (toRow data09.row) 1025 1024 (toTotals ⟨4655510241528, 544882701545, 1522194579736, 3678198363337, 675729253⟩) :=
  CleanupSegments208.append_exact piece0058 piece0059 rfl rfl rfl
#print axioms join09_01

theorem join09_02 : ChunkFacts (toRow data09.row) 2049 655 (toTotals ⟨280157183068, 152195381455, 391392892655, 40959671868, 241620913⟩) :=
  CleanupSegments208.append_exact piece0060 piece0061 rfl rfl rfl
#print axioms join09_02

theorem join09_03 : ChunkFacts (toRow data09.row) 1 2048 (toTotals ⟨993094915767562, 3978224619681, 21595611480932, 975477528906311, 3020412345⟩) :=
  CleanupSegments208.append_exact join09_00 join09_01 rfl rfl rfl
#print axioms join09_03

theorem join09_04 : ChunkFacts (toRow data09.row) 1 2703 (toTotals ⟨993375072950630, 4130420001136, 21987004373587, 975518488578179, 3262033258⟩) :=
  CleanupSegments208.append_exact join09_03 join09_02 rfl rfl rfl
#print axioms join09_04

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) := join09_04
#print axioms fact09

theorem piece0062 : ChunkFacts (toRow data10.row) 1 512 (toTotals ⟨1035821821353837, 3857613513351, 18245164745792, 1021434270121396, 1794089207⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0062
#print axioms piece0062

theorem piece0063 : ChunkFacts (toRow data10.row) 513 512 (toTotals ⟨36767989627122, 1577039579847, 3675463197967, 34669566009002, 977607652⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G07.checked0063
#print axioms piece0063

theorem piece0064 : ChunkFacts (toRow data10.row) 1025 512 (toTotals ⟨6078984522450, 695650732482, 1440550229639, 5334085025293, 612048864⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0064
#print axioms piece0064

theorem piece0065 : ChunkFacts (toRow data10.row) 1537 512 (toTotals ⟨1568129989959, 372737609154, 738599871141, 1202267727972, 394506312⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0065
#print axioms piece0065

theorem piece0066 : ChunkFacts (toRow data10.row) 2049 512 (toTotals ⟨370302587457, 202136046927, 383027243041, 189411391343, 255383721⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0066
#print axioms piece0066

theorem piece0067 : ChunkFacts (toRow data10.row) 2561 512 (toTotals ⟨184413437666, 161456561664, 305943757312, 39926242018, 234835660⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0067
#print axioms piece0067

theorem piece0068 : ChunkFacts (toRow data10.row) 3073 392 (toTotals ⟨121703274683, 123615180024, 234238189192, 11080265515, 181108690⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0068
#print axioms piece0068

theorem join10_00 : ChunkFacts (toRow data10.row) 1 1024 (toTotals ⟨1072589810980959, 5434653093198, 21920627943759, 1056103836130398, 2771696859⟩) :=
  CleanupSegments208.append_exact piece0062 piece0063 rfl rfl rfl
#print axioms join10_00

theorem join10_01 : ChunkFacts (toRow data10.row) 1025 1024 (toTotals ⟨7647114512409, 1068388341636, 2179150100780, 6536352753265, 1006555176⟩) :=
  CleanupSegments208.append_exact piece0064 piece0065 rfl rfl rfl
#print axioms join10_01

theorem join10_02 : ChunkFacts (toRow data10.row) 2049 1024 (toTotals ⟨554716025123, 363592608591, 688971000353, 229337633361, 490219381⟩) :=
  CleanupSegments208.append_exact piece0066 piece0067 rfl rfl rfl
#print axioms join10_02

theorem join10_03 : ChunkFacts (toRow data10.row) 1 2048 (toTotals ⟨1080236925493368, 6503041434834, 24099778044539, 1062640188883663, 3778252035⟩) :=
  CleanupSegments208.append_exact join10_00 join10_01 rfl rfl rfl
#print axioms join10_03

theorem join10_04 : ChunkFacts (toRow data10.row) 2049 1416 (toTotals ⟨676419299806, 487207788615, 923209189545, 240417898876, 671328071⟩) :=
  CleanupSegments208.append_exact join10_02 piece0068 rfl rfl rfl
#print axioms join10_04

theorem join10_05 : ChunkFacts (toRow data10.row) 1 3464 (toTotals ⟨1080913344793174, 6990249223449, 25022987234084, 1062880606782539, 4449580106⟩) :=
  CleanupSegments208.append_exact join10_03 join10_04 rfl rfl rfl
#print axioms join10_05

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) := join10_05
#print axioms fact10

theorem piece0069 : ChunkFacts (toRow data11.row) 1 512 (toTotals ⟨1113033837984657, 4870185808644, 19181251669950, 1098722772123351, 1986889949⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0069
#print axioms piece0069

theorem piece0070 : ChunkFacts (toRow data11.row) 513 512 (toTotals ⟨45210773061095, 2171464612686, 4325020525461, 43057217148320, 1155839047⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0070
#print axioms piece0070

theorem piece0071 : ChunkFacts (toRow data11.row) 1025 512 (toTotals ⟨8017635339206, 996456520602, 1768627593424, 7245464266384, 754202471⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G08.checked0071
#print axioms piece0071

theorem piece0072 : ChunkFacts (toRow data11.row) 1537 512 (toTotals ⟨2728441046137, 593346224250, 1029011486947, 2292775783440, 559993897⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0072
#print axioms piece0072

theorem piece0073 : ChunkFacts (toRow data11.row) 2049 512 (toTotals ⟨651732113479, 330083068752, 540181946504, 441633235727, 368972316⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0073
#print axioms piece0073

theorem piece0074 : ChunkFacts (toRow data11.row) 2561 512 (toTotals ⟨277582527870, 224193588732, 366893490214, 134882626388, 289548546⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0074
#print axioms piece0074

theorem piece0075 : ChunkFacts (toRow data11.row) 3073 512 (toTotals ⟨156251859738, 186949702656, 305943757312, 37257805082, 275057604⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0075
#print axioms piece0075

theorem piece0076 : ChunkFacts (toRow data11.row) 3585 512 (toTotals ⟨135638384588, 186949702656, 305943757312, 16644329932, 298024487⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0076
#print axioms piece0076

theorem piece0077 : ChunkFacts (toRow data11.row) 4097 73 (toTotals ⟨17966070974, 26654938074, 43620887273, 1000121775, 23128175⟩) :=
  CleanupFastSound208.check_sound CleanupChecks233811G09.checked0077
#print axioms piece0077

theorem join11_00 : ChunkFacts (toRow data11.row) 1 1024 (toTotals ⟨1158244611045752, 7041650421330, 23506272195411, 1141779989271671, 3142728996⟩) :=
  CleanupSegments208.append_exact piece0069 piece0070 rfl rfl rfl
#print axioms join11_00

theorem join11_01 : ChunkFacts (toRow data11.row) 1025 1024 (toTotals ⟨10746076385343, 1589802744852, 2797639080371, 9538240049824, 1314196368⟩) :=
  CleanupSegments208.append_exact piece0071 piece0072 rfl rfl rfl
#print axioms join11_01

theorem join11_02 : ChunkFacts (toRow data11.row) 2049 1024 (toTotals ⟨929314641349, 554276657484, 907075436718, 576515862115, 658520862⟩) :=
  CleanupSegments208.append_exact piece0073 piece0074 rfl rfl rfl
#print axioms join11_02

theorem join11_03 : ChunkFacts (toRow data11.row) 3073 1024 (toTotals ⟨291890244326, 373899405312, 611887514624, 53902135014, 573082091⟩) :=
  CleanupSegments208.append_exact piece0075 piece0076 rfl rfl rfl
#print axioms join11_03

theorem join11_04 : ChunkFacts (toRow data11.row) 1 2048 (toTotals ⟨1168990687431095, 8631453166182, 26303911275782, 1151318229321495, 4456925364⟩) :=
  CleanupSegments208.append_exact join11_00 join11_01 rfl rfl rfl
#print axioms join11_04

theorem join11_05 : ChunkFacts (toRow data11.row) 2049 2048 (toTotals ⟨1221204885675, 928176062796, 1518962951342, 630417997129, 1231602953⟩) :=
  CleanupSegments208.append_exact join11_02 join11_03 rfl rfl rfl
#print axioms join11_05

theorem join11_06 : ChunkFacts (toRow data11.row) 1 4096 (toTotals ⟨1170211892316770, 9559629228978, 27822874227124, 1151948647318624, 5688528317⟩) :=
  CleanupSegments208.append_exact join11_04 join11_05 rfl rfl rfl
#print axioms join11_06

theorem join11_07 : ChunkFacts (toRow data11.row) 1 4169 (toTotals ⟨1170229858387744, 9586284167052, 27866495114397, 1151949647440399, 5711656492⟩) :=
  CleanupSegments208.append_exact join11_06 piece0077 rfl rfl rfl
#print axioms join11_07

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) := join11_07
#print axioms fact11

theorem all_facts {k : ℕ} (hk : k < 12) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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

#print axioms all_facts
end JSP233.CleanupFacts233811
