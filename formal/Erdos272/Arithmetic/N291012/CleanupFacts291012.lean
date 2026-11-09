module

public import Erdos272.Arithmetic.N291012.CleanupChecks291012G00
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G01
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G02
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G03
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G04
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G05
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G06
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G07
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G08
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G09
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G10
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G11
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G12
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G13
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G14
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G15
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G16
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G17
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G18
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G19
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G20
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G21
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G22
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G23
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G24
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G25
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G26
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G27
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G28
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G29
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G30
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G31
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G32
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G33
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G34
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G35
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G36
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G37
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G38
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G39
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G40
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G41
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G42
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G43
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G44
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G45
public import Erdos272.Arithmetic.N291012.CleanupChecks291012G46
public import Erdos272.Arithmetic.CleanupFastSound208
public import Erdos272.Arithmetic.CleanupSegments208

@[expose] public section

namespace JSP233.CleanupFacts291012
open CleanupRows291012 CleanupEval208 CleanupMachineSound208
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem piece0000 : ChunkFacts (toRow data00.row) 1 512 (toTotals ⟨914655925266703, 1149292821627, 15586986560573, 900218231527757, 1687455334⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0000
#print axioms piece0000

theorem piece0001 : ChunkFacts (toRow data00.row) 513 512 (toTotals ⟨21631729677555, 359497205667, 2234196641715, 19757030241507, 757372703⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0001
#print axioms piece0001

theorem piece0002 : ChunkFacts (toRow data00.row) 1025 512 (toTotals ⟨2581768461685, 150014433564, 793709220072, 1938073675177, 402351827⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0002
#print axioms piece0002

theorem piece0003 : ChunkFacts (toRow data00.row) 1537 512 (toTotals ⟨289360085878, 59818839552, 273849547264, 75329378166, 184866781⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0003
#print axioms piece0003

theorem piece0004 : ChunkFacts (toRow data00.row) 2049 322 (toTotals ⟨147099566772, 37620442062, 172225691834, 12494317000, 117102439⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0004
#print axioms piece0004

theorem join00_00 : ChunkFacts (toRow data00.row) 1 1024 (toTotals ⟨936287654944258, 1508790027294, 17821183202288, 919975261769264, 2444828037⟩) :=
  CleanupSegments208.append_exact piece0000 piece0001 rfl rfl rfl
#print axioms join00_00

theorem join00_01 : ChunkFacts (toRow data00.row) 1025 1024 (toTotals ⟨2871128547563, 209833273116, 1067558767336, 2013403053343, 587218608⟩) :=
  CleanupSegments208.append_exact piece0002 piece0003 rfl rfl rfl
#print axioms join00_01

theorem join00_02 : ChunkFacts (toRow data00.row) 1 2048 (toTotals ⟨939158783491821, 1718623300410, 18888741969624, 921988664822607, 3032046645⟩) :=
  CleanupSegments208.append_exact join00_00 join00_01 rfl rfl rfl
#print axioms join00_02

theorem join00_03 : ChunkFacts (toRow data00.row) 1 2370 (toTotals ⟨939305883058593, 1756243742472, 19060967661458, 922001159139607, 3149149084⟩) :=
  CleanupSegments208.append_exact join00_02 piece0004 rfl rfl rfl
#print axioms join00_03

theorem fact00 : ChunkFacts (toRow data00.row) 1 data00.steps (toTotals data00.total) := join00_03
#print axioms fact00

theorem piece0005 : ChunkFacts (toRow data01.row) 1 512 (toTotals ⟨961705794617403, 1801980681774, 16184404603203, 947323370695974, 1849026661⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0005
#print axioms piece0005

theorem piece0006 : ChunkFacts (toRow data01.row) 513 512 (toTotals ⟨28226135178969, 644550742836, 2693689950544, 26176995971261, 904409060⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0006
#print axioms piece0006

theorem piece0007 : ChunkFacts (toRow data01.row) 1025 512 (toTotals ⟨3857852387067, 271425234444, 978010842434, 3151266779077, 509680730⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0007
#print axioms piece0007

theorem piece0008 : ChunkFacts (toRow data01.row) 1537 512 (toTotals ⟨642272924825, 116180776530, 388403119758, 370050581597, 253188894⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0008
#print axioms piece0008

theorem piece0009 : ChunkFacts (toRow data01.row) 2049 512 (toTotals ⟨224854108524, 86209503744, 273849547264, 37214065004, 211338553⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0009
#print axioms piece0009

theorem piece0010 : ChunkFacts (toRow data01.row) 2561 127 (toTotals ⟨48845249208, 21383997999, 67927524419, 2301722788, 49297462⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0010
#print axioms piece0010

theorem join01_00 : ChunkFacts (toRow data01.row) 1 1024 (toTotals ⟨989931929796372, 2446531424610, 18878094553747, 973500366667235, 2753435721⟩) :=
  CleanupSegments208.append_exact piece0005 piece0006 rfl rfl rfl
#print axioms join01_00

theorem join01_01 : ChunkFacts (toRow data01.row) 1025 1024 (toTotals ⟨4500125311892, 387606010974, 1366413962192, 3521317360674, 762869624⟩) :=
  CleanupSegments208.append_exact piece0007 piece0008 rfl rfl rfl
#print axioms join01_01

theorem join01_02 : ChunkFacts (toRow data01.row) 2049 639 (toTotals ⟨273699357732, 107593501743, 341777071683, 39515787792, 260636015⟩) :=
  CleanupSegments208.append_exact piece0009 piece0010 rfl rfl rfl
#print axioms join01_02

theorem join01_03 : ChunkFacts (toRow data01.row) 1 2048 (toTotals ⟨994432055108264, 2834137435584, 20244508515939, 977021684027909, 3516305345⟩) :=
  CleanupSegments208.append_exact join01_00 join01_01 rfl rfl rfl
#print axioms join01_03

theorem join01_04 : ChunkFacts (toRow data01.row) 1 2687 (toTotals ⟨994705754465996, 2941730937327, 20586285587622, 977061199815701, 3776941360⟩) :=
  CleanupSegments208.append_exact join01_03 join01_02 rfl rfl rfl
#print axioms join01_04

theorem fact01 : ChunkFacts (toRow data01.row) 1 data01.steps (toTotals data01.total) := join01_04
#print axioms fact01

theorem piece0011 : ChunkFacts (toRow data02.row) 1 512 (toTotals ⟨999661329539100, 2366500352070, 16676401599574, 985351428291596, 1987072425⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0011
#print axioms piece0011

theorem piece0012 : ChunkFacts (toRow data02.row) 513 512 (toTotals ⟨34166663683289, 922023834680, 3080030029651, 32008657488318, 1028253034⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0012
#print axioms piece0012

theorem piece0013 : ChunkFacts (toRow data02.row) 1025 512 (toTotals ⟨5176424913588, 396478495995, 1158259470249, 4414643939334, 607374714⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0013
#print axioms piece0013

theorem piece0014 : ChunkFacts (toRow data02.row) 1537 512 (toTotals ⟨1095655214784, 193187909905, 536035107701, 752808016988, 348453766⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0014
#print axioms piece0014

theorem piece0015 : ChunkFacts (toRow data02.row) 2049 512 (toTotals ⟨224854108524, 105562657280, 273849547264, 56567218540, 224317497⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G00.checked0015
#print axioms piece0015

theorem piece0016 : ChunkFacts (toRow data02.row) 2561 420 (toTotals ⟨153331758011, 86594367300, 224642206740, 15283918571, 188571137⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0016
#print axioms piece0016

theorem join02_00 : ChunkFacts (toRow data02.row) 1 1024 (toTotals ⟨1033827993222389, 3288524186750, 19756431629225, 1017360085779914, 3015325459⟩) :=
  CleanupSegments208.append_exact piece0011 piece0012 rfl rfl rfl
#print axioms join02_00

theorem join02_01 : ChunkFacts (toRow data02.row) 1025 1024 (toTotals ⟨6272080128372, 589666405900, 1694294577950, 5167451956322, 955828480⟩) :=
  CleanupSegments208.append_exact piece0013 piece0014 rfl rfl rfl
#print axioms join02_01

theorem join02_02 : ChunkFacts (toRow data02.row) 2049 932 (toTotals ⟨378185866535, 192157024580, 498491754004, 71851137111, 412888634⟩) :=
  CleanupSegments208.append_exact piece0015 piece0016 rfl rfl rfl
#print axioms join02_02

theorem join02_03 : ChunkFacts (toRow data02.row) 1 2048 (toTotals ⟨1040100073350761, 3878190592650, 21450726207175, 1022527537736236, 3971153939⟩) :=
  CleanupSegments208.append_exact join02_00 join02_01 rfl rfl rfl
#print axioms join02_03

theorem join02_04 : ChunkFacts (toRow data02.row) 1 2980 (toTotals ⟨1040478259217296, 4070347617230, 21949217961179, 1022599388873347, 4384042573⟩) :=
  CleanupSegments208.append_exact join02_03 join02_02 rfl rfl rfl
#print axioms join02_04

theorem fact02 : ChunkFacts (toRow data02.row) 1 data02.steps (toTotals data02.total) := join02_04
#print axioms fact02

theorem piece0017 : ChunkFacts (toRow data03.row) 1 512 (toTotals ⟨1011434117997702, 2824660163130, 16921242336719, 997337535824113, 2099032437⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0017
#print axioms piece0017

theorem piece0018 : ChunkFacts (toRow data03.row) 513 512 (toTotals ⟨38075943138820, 1185140136570, 3360576984326, 35900506291064, 1130171137⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0018
#print axioms piece0018

theorem piece0019 : ChunkFacts (toRow data03.row) 1025 512 (toTotals ⟨6342727365190, 522933764340, 1305648942970, 5560012186560, 687068258⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0019
#print axioms piece0019

theorem piece0020 : ChunkFacts (toRow data03.row) 1537 512 (toTotals ⟨1682426252693, 287926272270, 689982458481, 1280370066482, 450428907⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0020
#print axioms piece0020

theorem piece0021 : ChunkFacts (toRow data03.row) 2049 512 (toTotals ⟨311112674627, 140956387260, 313429364642, 138639697245, 260704353⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0021
#print axioms piece0021

theorem piece0022 : ChunkFacts (toRow data03.row) 2561 512 (toTotals ⟨184048386786, 123156433920, 273849547264, 33355273442, 254349124⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0022
#print axioms piece0022

theorem piece0023 : ChunkFacts (toRow data03.row) 3073 235 (toTotals ⟨74508581039, 56526878850, 125692663295, 5342796594, 113439827⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0023
#print axioms piece0023

theorem join03_00 : ChunkFacts (toRow data03.row) 1 1024 (toTotals ⟨1049510061136522, 4009800299700, 20281819321045, 1033238042115177, 3229203574⟩) :=
  CleanupSegments208.append_exact piece0017 piece0018 rfl rfl rfl
#print axioms join03_00

theorem join03_01 : ChunkFacts (toRow data03.row) 1025 1024 (toTotals ⟨8025153617883, 810860036610, 1995631401451, 6840382253042, 1137497165⟩) :=
  CleanupSegments208.append_exact piece0019 piece0020 rfl rfl rfl
#print axioms join03_01

theorem join03_02 : ChunkFacts (toRow data03.row) 2049 1024 (toTotals ⟨495161061413, 264112821180, 587278911906, 171994970687, 515053477⟩) :=
  CleanupSegments208.append_exact piece0021 piece0022 rfl rfl rfl
#print axioms join03_02

theorem join03_03 : ChunkFacts (toRow data03.row) 1 2048 (toTotals ⟨1057535214754405, 4820660336310, 22277450722496, 1040078424368219, 4366700739⟩) :=
  CleanupSegments208.append_exact join03_00 join03_01 rfl rfl rfl
#print axioms join03_03

theorem join03_04 : ChunkFacts (toRow data03.row) 2049 1259 (toTotals ⟨569669642452, 320639700030, 712971575201, 177337767281, 628493304⟩) :=
  CleanupSegments208.append_exact join03_02 piece0023 rfl rfl rfl
#print axioms join03_04

theorem join03_05 : ChunkFacts (toRow data03.row) 1 3307 (toTotals ⟨1058104884396857, 5141300036340, 22990422297697, 1040255762135500, 4995194043⟩) :=
  CleanupSegments208.append_exact join03_03 join03_04 rfl rfl rfl
#print axioms join03_05

theorem fact03 : ChunkFacts (toRow data03.row) 1 data03.steps (toTotals data03.total) := join03_05
#print axioms fact03

theorem piece0024 : ChunkFacts (toRow data04.row) 1 512 (toTotals ⟨1062708050720207, 3470097463742, 17509770368273, 1048668377815676, 2227492478⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0024
#print axioms piece0024

theorem piece0025 : ChunkFacts (toRow data04.row) 513 512 (toTotals ⟨43442814689251, 1518562813096, 3719310190637, 41242067311710, 1248157084⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0025
#print axioms piece0025

theorem piece0026 : ChunkFacts (toRow data04.row) 1025 512 (toTotals ⟨7672360073857, 686707079492, 1498358867986, 6860708285363, 788285013⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0026
#print axioms piece0026

theorem piece0027 : ChunkFacts (toRow data04.row) 1537 512 (toTotals ⟨2411794021962, 404656853888, 853228441864, 1963222433986, 566848066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0027
#print axioms piece0027

theorem piece0028 : ChunkFacts (toRow data04.row) 2049 512 (toTotals ⟨492006146786, 206726871008, 402216522544, 296516495250, 337450843⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0028
#print axioms piece0028

theorem piece0029 : ChunkFacts (toRow data04.row) 2561 512 (toTotals ⟨184048386786, 140750210048, 273849547264, 50949049570, 268769604⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0029
#print axioms piece0029

theorem piece0030 : ChunkFacts (toRow data04.row) 3073 512 (toTotals ⟨155886808858, 140750210048, 273849547264, 22787471642, 289605409⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0030
#print axioms piece0030

theorem piece0031 : ChunkFacts (toRow data04.row) 3585 132 (toTotals ⟨36616960333, 36287163528, 70601836404, 2302287457, 64305692⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G01.checked0031
#print axioms piece0031

theorem join04_00 : ChunkFacts (toRow data04.row) 1 1024 (toTotals ⟨1106150865409458, 4988660276838, 21229080558910, 1089910445127386, 3475649562⟩) :=
  CleanupSegments208.append_exact piece0024 piece0025 rfl rfl rfl
#print axioms join04_00

theorem join04_01 : ChunkFacts (toRow data04.row) 1025 1024 (toTotals ⟨10084154095819, 1091363933380, 2351587309850, 8823930719349, 1355133079⟩) :=
  CleanupSegments208.append_exact piece0026 piece0027 rfl rfl rfl
#print axioms join04_01

theorem join04_02 : ChunkFacts (toRow data04.row) 2049 1024 (toTotals ⟨676054533572, 347477081056, 676066069808, 347465544820, 606220447⟩) :=
  CleanupSegments208.append_exact piece0028 piece0029 rfl rfl rfl
#print axioms join04_02

theorem join04_03 : ChunkFacts (toRow data04.row) 3073 644 (toTotals ⟨192503769191, 177037373576, 344451383668, 25089759099, 353911101⟩) :=
  CleanupSegments208.append_exact piece0030 piece0031 rfl rfl rfl
#print axioms join04_03

theorem join04_04 : ChunkFacts (toRow data04.row) 1 2048 (toTotals ⟨1116235019505277, 6080024210218, 23580667868760, 1098734375846735, 4830782641⟩) :=
  CleanupSegments208.append_exact join04_00 join04_01 rfl rfl rfl
#print axioms join04_04

theorem join04_05 : ChunkFacts (toRow data04.row) 2049 1668 (toTotals ⟨868558302763, 524514454632, 1020517453476, 372555303919, 960131548⟩) :=
  CleanupSegments208.append_exact join04_02 join04_03 rfl rfl rfl
#print axioms join04_05

theorem join04_06 : ChunkFacts (toRow data04.row) 1 3716 (toTotals ⟨1117103577808040, 6604538664850, 24601185322236, 1099106931150654, 5790914189⟩) :=
  CleanupSegments208.append_exact join04_04 join04_05 rfl rfl rfl
#print axioms join04_06

theorem fact04 : ChunkFacts (toRow data04.row) 1 data04.steps (toTotals data04.total) := join04_06
#print axioms fact04

theorem piece0032 : ChunkFacts (toRow data05.row) 1 512 (toTotals ⟨1099824181774506, 3950764923885, 17897944261398, 1085877002436993, 2344797127⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0032
#print axioms piece0032

theorem piece0033 : ChunkFacts (toRow data05.row) 513 512 (toTotals ⟨47344055374446, 1807705527362, 3997827325904, 45153933575904, 1355047455⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0033
#print axioms piece0033

theorem piece0034 : ChunkFacts (toRow data05.row) 1025 512 (toTotals ⟨9041668732216, 853957913896, 1690533930602, 8205092715510, 886230565⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0034
#print axioms piece0034

theorem piece0035 : ChunkFacts (toRow data05.row) 1537 512 (toTotals ⟨3115388479930, 524954298344, 1006976465044, 2633366313230, 678111231⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0035
#print axioms piece0035

theorem piece0036 : ChunkFacts (toRow data05.row) 2049 512 (toTotals ⟨631674457613, 267013044607, 472283496551, 426404005669, 405696113⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0036
#print axioms piece0036

theorem piece0037 : ChunkFacts (toRow data05.row) 2561 512 (toTotals ⟨266247742971, 181435817400, 320917438200, 126766122171, 315739268⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0037
#print axioms piece0037

theorem piece0038 : ChunkFacts (toRow data05.row) 3073 512 (toTotals ⟨155886808858, 154825230848, 273849547264, 36862492442, 303238945⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0038
#print axioms piece0038

theorem piece0039 : ChunkFacts (toRow data05.row) 3585 512 (toTotals ⟨135273333708, 154825230848, 273849547264, 16249017292, 321221926⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0039
#print axioms piece0039

theorem piece0040 : ChunkFacts (toRow data05.row) 4097 27 (toTotals ⟨6662146369, 8164611783, 14441284719, 385473433, 4268754⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0040
#print axioms piece0040

theorem join05_00 : ChunkFacts (toRow data05.row) 1 1024 (toTotals ⟨1147168237148952, 5758470451247, 21895771587302, 1131030936012897, 3699844582⟩) :=
  CleanupSegments208.append_exact piece0032 piece0033 rfl rfl rfl
#print axioms join05_00

theorem join05_01 : ChunkFacts (toRow data05.row) 1025 1024 (toTotals ⟨12157057212146, 1378912212240, 2697510395646, 10838459028740, 1564341796⟩) :=
  CleanupSegments208.append_exact piece0034 piece0035 rfl rfl rfl
#print axioms join05_01

theorem join05_02 : ChunkFacts (toRow data05.row) 2049 1024 (toTotals ⟨897922200584, 448448862007, 793200934751, 553170127840, 721435381⟩) :=
  CleanupSegments208.append_exact piece0036 piece0037 rfl rfl rfl
#print axioms join05_02

theorem join05_03 : ChunkFacts (toRow data05.row) 3073 1024 (toTotals ⟨291160142566, 309650461696, 547699094528, 53111509734, 624460871⟩) :=
  CleanupSegments208.append_exact piece0038 piece0039 rfl rfl rfl
#print axioms join05_03

theorem join05_04 : ChunkFacts (toRow data05.row) 1 2048 (toTotals ⟨1159325294361098, 7137382663487, 24593281982948, 1141869395041637, 5264186378⟩) :=
  CleanupSegments208.append_exact join05_00 join05_01 rfl rfl rfl
#print axioms join05_04

theorem join05_05 : ChunkFacts (toRow data05.row) 2049 2048 (toTotals ⟨1189082343150, 758099323703, 1340900029279, 606281637574, 1345896252⟩) :=
  CleanupSegments208.append_exact join05_02 join05_03 rfl rfl rfl
#print axioms join05_05

theorem join05_06 : ChunkFacts (toRow data05.row) 1 4096 (toTotals ⟨1160514376704248, 7895481987190, 25934182012227, 1142475676679211, 6610082630⟩) :=
  CleanupSegments208.append_exact join05_04 join05_05 rfl rfl rfl
#print axioms join05_06

theorem join05_07 : ChunkFacts (toRow data05.row) 1 4123 (toTotals ⟨1160521038850617, 7903646598973, 25948623296946, 1142476062152644, 6614351384⟩) :=
  CleanupSegments208.append_exact join05_06 piece0040 rfl rfl rfl
#print axioms join05_07

theorem fact05 : ChunkFacts (toRow data05.row) 1 data05.steps (toTotals data05.total) := join05_07
#print axioms fact05

theorem piece0041 : ChunkFacts (toRow data06.row) 1 512 (toTotals ⟨1123874730385027, 4376472448515, 18237140040725, 1110014062792817, 2463122061⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0041
#print axioms piece0041

theorem piece0042 : ChunkFacts (toRow data06.row) 513 512 (toTotals ⟨51972592208093, 2092140530595, 4305090823412, 49759641915276, 1461647815⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0042
#print axioms piece0042

theorem piece0043 : ChunkFacts (toRow data06.row) 1025 512 (toTotals ⟨10254074468977, 1012315643490, 1874892029116, 9391498083351, 981341240⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0043
#print axioms piece0043

theorem piece0044 : ChunkFacts (toRow data06.row) 1537 512 (toTotals ⟨3761839379954, 622441686345, 1122317381567, 3261963684732, 765223900⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0044
#print axioms piece0044

theorem piece0045 : ChunkFacts (toRow data06.row) 2049 512 (toTotals ⟨866550408451, 341422346895, 565349553629, 642623201717, 483977463⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0045
#print axioms piece0045

theorem piece0046 : ChunkFacts (toRow data06.row) 2561 512 (toTotals ⟨392623191517, 239996976105, 397402760971, 235217406651, 391235283⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0046
#print axioms piece0046

theorem piece0047 : ChunkFacts (toRow data06.row) 3073 512 (toTotals ⟨155886808858, 165381496320, 273849547264, 47418757914, 313464097⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G02.checked0047
#print axioms piece0047

theorem piece0048 : ChunkFacts (toRow data06.row) 3585 512 (toTotals ⟨135273333708, 165381496320, 273849547264, 26805282764, 337950406⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0048
#print axioms piece0048

theorem piece0049 : ChunkFacts (toRow data06.row) 4097 396 (toTotals ⟨93637157725, 127912251060, 211805509212, 9743899573, 254504122⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0049
#print axioms piece0049

theorem join06_00 : ChunkFacts (toRow data06.row) 1 1024 (toTotals ⟨1175847322593120, 6468612979110, 22542230864137, 1159773704708093, 3924769876⟩) :=
  CleanupSegments208.append_exact piece0041 piece0042 rfl rfl rfl
#print axioms join06_00

theorem join06_01 : ChunkFacts (toRow data06.row) 1025 1024 (toTotals ⟨14015913848931, 1634757329835, 2997209410683, 12653461768083, 1746565140⟩) :=
  CleanupSegments208.append_exact piece0043 piece0044 rfl rfl rfl
#print axioms join06_01

theorem join06_02 : ChunkFacts (toRow data06.row) 2049 1024 (toTotals ⟨1259173599968, 581419323000, 962752314600, 877840608368, 875212746⟩) :=
  CleanupSegments208.append_exact piece0045 piece0046 rfl rfl rfl
#print axioms join06_02

theorem join06_03 : ChunkFacts (toRow data06.row) 3073 1024 (toTotals ⟨291160142566, 330762992640, 547699094528, 74224040678, 651414503⟩) :=
  CleanupSegments208.append_exact piece0047 piece0048 rfl rfl rfl
#print axioms join06_03

theorem join06_04 : ChunkFacts (toRow data06.row) 1 2048 (toTotals ⟨1189863236442051, 8103370308945, 25539440274820, 1172427166476176, 5671335016⟩) :=
  CleanupSegments208.append_exact join06_00 join06_01 rfl rfl rfl
#print axioms join06_04

theorem join06_05 : ChunkFacts (toRow data06.row) 2049 2048 (toTotals ⟨1550333742534, 912182315640, 1510451409128, 952064649046, 1526627249⟩) :=
  CleanupSegments208.append_exact join06_02 join06_03 rfl rfl rfl
#print axioms join06_05

theorem join06_06 : ChunkFacts (toRow data06.row) 1 4096 (toTotals ⟨1191413570184585, 9015552624585, 27049891683948, 1173379231125222, 7197962265⟩) :=
  CleanupSegments208.append_exact join06_04 join06_05 rfl rfl rfl
#print axioms join06_06

theorem join06_07 : ChunkFacts (toRow data06.row) 1 4492 (toTotals ⟨1191507207342310, 9143464875645, 27261697193160, 1173388975024795, 7452466387⟩) :=
  CleanupSegments208.append_exact join06_06 piece0049 rfl rfl rfl
#print axioms join06_07

theorem fact06 : ChunkFacts (toRow data06.row) 1 data06.steps (toTotals data06.total) := join06_07
#print axioms fact06

theorem piece0050 : ChunkFacts (toRow data07.row) 1 512 (toTotals ⟨994653582298687, 1145106696754, 15654777215125, 980143911780316, 1824291453⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0050
#print axioms piece0050

theorem piece0051 : ChunkFacts (toRow data07.row) 513 512 (toTotals ⟨24801777056543, 370708244106, 2300277556649, 22872207744000, 840283472⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0051
#print axioms piece0051

theorem piece0052 : ChunkFacts (toRow data07.row) 1025 512 (toTotals ⟨3047802256398, 155195955942, 819929410044, 2383068802296, 451866025⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0052
#print axioms piece0052

theorem piece0053 : ChunkFacts (toRow data07.row) 1537 512 (toTotals ⟨406707988748, 64721457609, 305087332460, 166342113897, 215710619⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0053
#print axioms piece0053

theorem piece0054 : ChunkFacts (toRow data07.row) 2049 421 (toTotals ⟨188306490950, 47552763793, 215081631856, 20777622887, 163122243⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0054
#print axioms piece0054

theorem join07_00 : ChunkFacts (toRow data07.row) 1 1024 (toTotals ⟨1019455359355230, 1515814940860, 17955054771774, 1003016119524316, 2664574925⟩) :=
  CleanupSegments208.append_exact piece0050 piece0051 rfl rfl rfl
#print axioms join07_00

theorem join07_01 : ChunkFacts (toRow data07.row) 1025 1024 (toTotals ⟨3454510245146, 219917413551, 1125016742504, 2549410916193, 667576644⟩) :=
  CleanupSegments208.append_exact piece0052 piece0053 rfl rfl rfl
#print axioms join07_01

theorem join07_02 : ChunkFacts (toRow data07.row) 1 2048 (toTotals ⟨1022909869600376, 1735732354411, 19080071514278, 1005565530440509, 3332151569⟩) :=
  CleanupSegments208.append_exact join07_00 join07_01 rfl rfl rfl
#print axioms join07_02

theorem join07_03 : ChunkFacts (toRow data07.row) 1 2469 (toTotals ⟨1023098176091326, 1783285118204, 19295153146134, 1005586308063396, 3495273812⟩) :=
  CleanupSegments208.append_exact join07_02 piece0054 rfl rfl rfl
#print axioms join07_03

theorem fact07 : ChunkFacts (toRow data07.row) 1 data07.steps (toTotals data07.total) := join07_03
#print axioms fact07

theorem piece0055 : ChunkFacts (toRow data08.row) 1 512 (toTotals ⟨1041055561752155, 1787364674640, 16205128757952, 1026637797668843, 1992130829⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0055
#print axioms piece0055

theorem piece0056 : ChunkFacts (toRow data08.row) 513 512 (toTotals ⟨31585450892995, 655367047368, 2729686956958, 29511130983405, 989581963⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0056
#print axioms piece0056

theorem piece0057 : ChunkFacts (toRow data08.row) 1025 512 (toTotals ⟨4528886043868, 277708937608, 1007934256928, 3798660724548, 565171393⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0057
#print axioms piece0057

theorem piece0058 : ChunkFacts (toRow data08.row) 1537 512 (toTotals ⟨865124649013, 128761881388, 436910654120, 556975876281, 302522466⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0058
#print axioms piece0058

theorem piece0059 : ChunkFacts (toRow data08.row) 2049 512 (toTotals ⟨224795653996, 83345238016, 261571960832, 46568931180, 221578230⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0059
#print axioms piece0059

theorem piece0060 : ChunkFacts (toRow data08.row) 2561 231 (toTotals ⟨87143941753, 37603027308, 118013912016, 6733057045, 98598281⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0060
#print axioms piece0060

theorem join08_00 : ChunkFacts (toRow data08.row) 1 1024 (toTotals ⟨1072641012645150, 2442731722008, 18934815714910, 1056148928652248, 2981712792⟩) :=
  CleanupSegments208.append_exact piece0055 piece0056 rfl rfl rfl
#print axioms join08_00

theorem join08_01 : ChunkFacts (toRow data08.row) 1025 1024 (toTotals ⟨5394010692881, 406470818996, 1444844911048, 4355636600829, 867693859⟩) :=
  CleanupSegments208.append_exact piece0057 piece0058 rfl rfl rfl
#print axioms join08_01

theorem join08_02 : ChunkFacts (toRow data08.row) 2049 743 (toTotals ⟨311939595749, 120948265324, 379585872848, 53301988225, 320176511⟩) :=
  CleanupSegments208.append_exact piece0059 piece0060 rfl rfl rfl
#print axioms join08_02

theorem join08_03 : ChunkFacts (toRow data08.row) 1 2048 (toTotals ⟨1078035023338031, 2849202541004, 20379660625958, 1060504565253077, 3849406651⟩) :=
  CleanupSegments208.append_exact join08_00 join08_01 rfl rfl rfl
#print axioms join08_03

theorem join08_04 : ChunkFacts (toRow data08.row) 1 2791 (toTotals ⟨1078346962933780, 2970150806328, 20759246498806, 1060557867241302, 4169583162⟩) :=
  CleanupSegments208.append_exact join08_03 join08_02 rfl rfl rfl
#print axioms join08_04

theorem fact08 : ChunkFacts (toRow data08.row) 1 data08.steps (toTotals data08.total) := join08_04
#print axioms fact08

theorem piece0061 : ChunkFacts (toRow data09.row) 1 512 (toTotals ⟨1082120127502791, 2469242200026, 16716974072027, 1067872395630790, 2173997073⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0061
#print axioms piece0061

theorem piece0062 : ChunkFacts (toRow data09.row) 513 512 (toTotals ⟨39622781874477, 1014653855376, 3203505773652, 37433929956201, 1154026184⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0062
#print axioms piece0062

theorem piece0063 : ChunkFacts (toRow data09.row) 1025 512 (toTotals ⟨6391510091421, 442027422144, 1232096517938, 5601440995627, 694127033⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G03.checked0063
#print axioms piece0063

theorem piece0064 : ChunkFacts (toRow data09.row) 1537 512 (toTotals ⟨1580709688204, 239431520328, 636488241068, 1183652967464, 443637062⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0064
#print axioms piece0064

theorem piece0065 : ChunkFacts (toRow data09.row) 2049 512 (toTotals ⟨263081099110, 113646254841, 277409325648, 99318028303, 247756366⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0065
#print axioms piece0065

theorem piece0066 : ChunkFacts (toRow data09.row) 2561 512 (toTotals ⟨183989932258, 107158162944, 261571960832, 29576134370, 254491565⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0066
#print axioms piece0066

theorem piece0067 : ChunkFacts (toRow data09.row) 3073 106 (toTotals ⟨34269968994, 22185088422, 54153570016, 2301487400, 46545721⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0067
#print axioms piece0067

theorem join09_00 : ChunkFacts (toRow data09.row) 1 1024 (toTotals ⟨1121742909377268, 3483896055402, 19920479845679, 1105306325586991, 3328023257⟩) :=
  CleanupSegments208.append_exact piece0061 piece0062 rfl rfl rfl
#print axioms join09_00

theorem join09_01 : ChunkFacts (toRow data09.row) 1025 1024 (toTotals ⟨7972219779625, 681458942472, 1868584759006, 6785093963091, 1137764095⟩) :=
  CleanupSegments208.append_exact piece0063 piece0064 rfl rfl rfl
#print axioms join09_01

theorem join09_02 : ChunkFacts (toRow data09.row) 2049 1024 (toTotals ⟨447071031368, 220804417785, 538981286480, 128894162673, 502247931⟩) :=
  CleanupSegments208.append_exact piece0065 piece0066 rfl rfl rfl
#print axioms join09_02

theorem join09_03 : ChunkFacts (toRow data09.row) 1 2048 (toTotals ⟨1129715129156893, 4165354997874, 21789064604685, 1112091419550082, 4465787352⟩) :=
  CleanupSegments208.append_exact join09_00 join09_01 rfl rfl rfl
#print axioms join09_03

theorem join09_04 : ChunkFacts (toRow data09.row) 2049 1130 (toTotals ⟨481341000362, 242989506207, 593134856496, 131195650073, 548793652⟩) :=
  CleanupSegments208.append_exact join09_02 piece0067 rfl rfl rfl
#print axioms join09_04

theorem join09_05 : ChunkFacts (toRow data09.row) 1 3178 (toTotals ⟨1130196470157255, 4408344504081, 22382199461181, 1112222615200155, 5014581004⟩) :=
  CleanupSegments208.append_exact join09_03 join09_04 rfl rfl rfl
#print axioms join09_05

theorem fact09 : ChunkFacts (toRow data09.row) 1 data09.steps (toTotals data09.total) := join09_05
#print axioms fact09

theorem piece0068 : ChunkFacts (toRow data10.row) 1 512 (toTotals ⟨1106277015623962, 2948975626880, 17029976971991, 1092196014278851, 2294376801⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0068
#print axioms piece0068

theorem piece0069 : ChunkFacts (toRow data10.row) 513 512 (toTotals ⟨43574760542718, 1285569062343, 3468871973446, 41391457631615, 1260588574⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0069
#print axioms piece0069

theorem piece0070 : ChunkFacts (toRow data10.row) 1025 512 (toTotals ⟨7759662755777, 581064605428, 1395099262158, 6945628099047, 785309325⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0070
#print axioms piece0070

theorem piece0071 : ChunkFacts (toRow data10.row) 1537 512 (toTotals ⟨2318136744999, 340005249086, 783077319832, 1875064674253, 553029927⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0071
#print axioms piece0071

theorem piece0072 : ChunkFacts (toRow data10.row) 2049 512 (toTotals ⟨412160492575, 162484676810, 342291433120, 232353736265, 307443079⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0072
#print axioms piece0072

theorem piece0073 : ChunkFacts (toRow data10.row) 2561 512 (toTotals ⟨183989932258, 124167394816, 261571960832, 46585366242, 268912045⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0073
#print axioms piece0073

theorem piece0074 : ChunkFacts (toRow data10.row) 3073 455 (toTotals ⟨139609404230, 110344071565, 232451644880, 17501830915, 243913224⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0074
#print axioms piece0074

theorem join10_00 : ChunkFacts (toRow data10.row) 1 1024 (toTotals ⟨1149851776166680, 4234544689223, 20498848945437, 1133587471910466, 3554965375⟩) :=
  CleanupSegments208.append_exact piece0068 piece0069 rfl rfl rfl
#print axioms join10_00

theorem join10_01 : ChunkFacts (toRow data10.row) 1025 1024 (toTotals ⟨10077799500776, 921069854514, 2178176581990, 8820692773300, 1338339252⟩) :=
  CleanupSegments208.append_exact piece0070 piece0071 rfl rfl rfl
#print axioms join10_01

theorem join10_02 : ChunkFacts (toRow data10.row) 2049 1024 (toTotals ⟨596150424833, 286652071626, 603863393952, 278939102507, 576355124⟩) :=
  CleanupSegments208.append_exact piece0072 piece0073 rfl rfl rfl
#print axioms join10_02

theorem join10_03 : ChunkFacts (toRow data10.row) 1 2048 (toTotals ⟨1159929575667456, 5155614543737, 22677025527427, 1142408164683766, 4893304627⟩) :=
  CleanupSegments208.append_exact join10_00 join10_01 rfl rfl rfl
#print axioms join10_03

theorem join10_04 : ChunkFacts (toRow data10.row) 2049 1479 (toTotals ⟨735759829063, 396996143191, 836315038832, 296440933422, 820268348⟩) :=
  CleanupSegments208.append_exact join10_02 piece0074 rfl rfl rfl
#print axioms join10_04

theorem join10_05 : ChunkFacts (toRow data10.row) 1 3527 (toTotals ⟨1160665335496519, 5552610686928, 23513340566259, 1142704605617188, 5713572975⟩) :=
  CleanupSegments208.append_exact join10_03 join10_04 rfl rfl rfl
#print axioms join10_05

theorem fact10 : ChunkFacts (toRow data10.row) 1 data10.steps (toTotals data10.total) := join10_05
#print axioms fact10

theorem piece0075 : ChunkFacts (toRow data11.row) 1 512 (toTotals ⟨1161177280982380, 3596970902000, 17603255935202, 1147170995949178, 2432059453⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0075
#print axioms piece0075

theorem piece0076 : ChunkFacts (toRow data11.row) 513 512 (toTotals ⟨48905903422232, 1628494453600, 3818371837496, 46716026038336, 1386006816⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0076
#print axioms piece0076

theorem piece0077 : ChunkFacts (toRow data11.row) 1025 512 (toTotals ⟨9358572713831, 763236140800, 1605894463314, 8515914391317, 901840984⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0077
#print axioms piece0077

theorem piece0078 : ChunkFacts (toRow data11.row) 1537 512 (toTotals ⟨3129191627271, 467096106400, 948251315692, 2648036417979, 683237433⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0078
#print axioms piece0078

theorem piece0079 : ChunkFacts (toRow data11.row) 2049 512 (toTotals ⟨602889603631, 232169375200, 430163263712, 404895715119, 394603687⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G04.checked0079
#print axioms piece0079

theorem piece0080 : ChunkFacts (toRow data11.row) 2561 512 (toTotals ⟨218621036557, 150827373200, 279452856592, 89995553165, 296092327⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0080
#print axioms piece0080

theorem piece0081 : ChunkFacts (toRow data11.row) 3073 512 (toTotals ⟨155828354330, 141176627200, 261571960832, 35433020698, 304953989⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0081
#print axioms piece0081

theorem piece0082 : ChunkFacts (toRow data11.row) 3585 379 (toTotals ⟨101767560547, 104503792400, 193624556944, 12646796003, 223731596⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0082
#print axioms piece0082

theorem join11_00 : ChunkFacts (toRow data11.row) 1 1024 (toTotals ⟨1210083184404612, 5225465355600, 21421627772698, 1193887021987514, 3818066269⟩) :=
  CleanupSegments208.append_exact piece0075 piece0076 rfl rfl rfl
#print axioms join11_00

theorem join11_01 : ChunkFacts (toRow data11.row) 1025 1024 (toTotals ⟨12487764341102, 1230332247200, 2554145779006, 11163950809296, 1585078417⟩) :=
  CleanupSegments208.append_exact piece0077 piece0078 rfl rfl rfl
#print axioms join11_01

theorem join11_02 : ChunkFacts (toRow data11.row) 2049 1024 (toTotals ⟨821510640188, 382996748400, 709616120304, 494891268284, 690696014⟩) :=
  CleanupSegments208.append_exact piece0079 piece0080 rfl rfl rfl
#print axioms join11_02

theorem join11_03 : ChunkFacts (toRow data11.row) 3073 891 (toTotals ⟨257595914877, 245680419600, 455196517776, 48079816701, 528685585⟩) :=
  CleanupSegments208.append_exact piece0081 piece0082 rfl rfl rfl
#print axioms join11_03

theorem join11_04 : ChunkFacts (toRow data11.row) 1 2048 (toTotals ⟨1222570948745714, 6455797602800, 23975773551704, 1205050972796810, 5403144686⟩) :=
  CleanupSegments208.append_exact join11_00 join11_01 rfl rfl rfl
#print axioms join11_04

theorem join11_05 : ChunkFacts (toRow data11.row) 2049 1915 (toTotals ⟨1079106555065, 628677168000, 1164812638080, 542971084985, 1219381599⟩) :=
  CleanupSegments208.append_exact join11_02 join11_03 rfl rfl rfl
#print axioms join11_05

theorem join11_06 : ChunkFacts (toRow data11.row) 1 3963 (toTotals ⟨1223650055300779, 7084474770800, 25140586189784, 1205593943881795, 6622526285⟩) :=
  CleanupSegments208.append_exact join11_04 join11_05 rfl rfl rfl
#print axioms join11_06

theorem fact11 : ChunkFacts (toRow data11.row) 1 data11.steps (toTotals data11.total) := join11_06
#print axioms fact11

theorem piece0083 : ChunkFacts (toRow data12.row) 1 512 (toTotals ⟨1210303868821220, 4134426091900, 18073224440762, 1196365070472358, 2559243047⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0083
#print axioms piece0083

theorem piece0084 : ChunkFacts (toRow data12.row) 513 512 (toTotals ⟨53973507398428, 1944474160800, 4122440519688, 51795541039540, 1501971802⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0084
#print axioms piece0084

theorem piece0085 : ChunkFacts (toRow data12.row) 1025 512 (toTotals ⟨10726949715266, 941401202850, 1800659161051, 9867691757065, 1009174399⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0085
#print axioms piece0085

theorem piece0086 : ChunkFacts (toRow data12.row) 1537 512 (toTotals ⟨3895219168977, 582858548200, 1080149400648, 3397928316529, 790555455⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0086
#print axioms piece0086

theorem piece0087 : ChunkFacts (toRow data12.row) 2049 512 (toTotals ⟨832619510320, 306544900350, 518035094304, 621129316366, 477245981⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0087
#print axioms piece0087

theorem piece0088 : ChunkFacts (toRow data12.row) 2561 512 (toTotals ⟨365469760069, 212525705075, 359150563408, 218844901736, 379429672⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0088
#print axioms piece0088

theorem piece0089 : ChunkFacts (toRow data12.row) 3073 512 (toTotals ⟨155828354330, 154784012800, 261571960832, 49040406298, 318587525⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0089
#print axioms piece0089

theorem piece0090 : ChunkFacts (toRow data12.row) 3585 512 (toTotals ⟨135214879180, 154784012800, 261571960832, 28426931148, 342304896⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0090
#print axioms piece0090

theorem piece0091 : ChunkFacts (toRow data12.row) 4097 301 (toTotals ⟨71903203776, 90996070025, 153775703536, 9123570265, 190877226⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0091
#print axioms piece0091

theorem join12_00 : ChunkFacts (toRow data12.row) 1 1024 (toTotals ⟨1264277376219648, 6078900252700, 22195664960450, 1248160611511898, 4061214849⟩) :=
  CleanupSegments208.append_exact piece0083 piece0084 rfl rfl rfl
#print axioms join12_00

theorem join12_01 : ChunkFacts (toRow data12.row) 1025 1024 (toTotals ⟨14622168884243, 1524259751050, 2880808561699, 13265620073594, 1799729854⟩) :=
  CleanupSegments208.append_exact piece0085 piece0086 rfl rfl rfl
#print axioms join12_01

theorem join12_02 : ChunkFacts (toRow data12.row) 2049 1024 (toTotals ⟨1198089270389, 519070605425, 877185657712, 839974218102, 856675653⟩) :=
  CleanupSegments208.append_exact piece0087 piece0088 rfl rfl rfl
#print axioms join12_02

theorem join12_03 : ChunkFacts (toRow data12.row) 3073 1024 (toTotals ⟨291043233510, 309568025600, 523143921664, 77467337446, 660892421⟩) :=
  CleanupSegments208.append_exact piece0089 piece0090 rfl rfl rfl
#print axioms join12_03

theorem join12_04 : ChunkFacts (toRow data12.row) 1 2048 (toTotals ⟨1278899545103891, 7603160003750, 25076473522149, 1261426231585492, 5860944703⟩) :=
  CleanupSegments208.append_exact join12_00 join12_01 rfl rfl rfl
#print axioms join12_04

theorem join12_05 : ChunkFacts (toRow data12.row) 2049 2048 (toTotals ⟨1489132503899, 828638631025, 1400329579376, 917441555548, 1517568074⟩) :=
  CleanupSegments208.append_exact join12_02 join12_03 rfl rfl rfl
#print axioms join12_05

theorem join12_06 : ChunkFacts (toRow data12.row) 1 4096 (toTotals ⟨1280388677607790, 8431798634775, 26476803101525, 1262343673141040, 7378512777⟩) :=
  CleanupSegments208.append_exact join12_04 join12_05 rfl rfl rfl
#print axioms join12_06

theorem join12_07 : ChunkFacts (toRow data12.row) 1 4397 (toTotals ⟨1280460580811566, 8522794704800, 26630578805061, 1262352796711305, 7569390003⟩) :=
  CleanupSegments208.append_exact join12_06 piece0091 rfl rfl rfl
#print axioms join12_07

theorem fact12 : ChunkFacts (toRow data12.row) 1 data12.steps (toTotals data12.total) := join12_07
#print axioms fact12

theorem piece0092 : ChunkFacts (toRow data13.row) 1 512 (toTotals ⟨1228933295589848, 4533345740892, 18331503700197, 1215135137630543, 2686401841⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0092
#print axioms piece0092

theorem piece0093 : ChunkFacts (toRow data13.row) 513 512 (toTotals ⟨58586303486330, 2226714463290, 4407329293335, 56405688656285, 1620234001⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0093
#print axioms piece0093

theorem piece0094 : ChunkFacts (toRow data13.row) 1025 512 (toTotals ⟨12177000208241, 1108845798579, 1989062745709, 11296783261111, 1113161770⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0094
#print axioms piece0094

theorem piece0095 : ChunkFacts (toRow data13.row) 1537 512 (toTotals ⟨4595716182129, 693793956507, 1203602344752, 4085907793884, 891088589⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G05.checked0095
#print axioms piece0095

theorem piece0096 : ChunkFacts (toRow data13.row) 2049 512 (toTotals ⟨1125217079330, 386694262800, 617716415476, 894194926654, 567469718⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0096
#print axioms piece0096

theorem piece0097 : ChunkFacts (toRow data13.row) 2561 512 (toTotals ⟨476315469429, 265852305675, 421478257200, 320689517904, 455387588⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0097
#print axioms piece0097

theorem piece0098 : ChunkFacts (toRow data13.row) 3073 512 (toTotals ⟨199437646054, 182068548735, 288648745840, 92857448949, 351956077⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0098
#print axioms piece0098

theorem piece0099 : ChunkFacts (toRow data13.row) 3585 512 (toTotals ⟨135214879180, 164989552128, 261571960832, 38632470476, 354102912⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0099
#print axioms piece0099

theorem piece0100 : ChunkFacts (toRow data13.row) 4097 512 (toTotals ⟨119470396990, 164989552128, 261571960832, 22887988286, 379407918⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0100
#print axioms piece0100

theorem piece0101 : ChunkFacts (toRow data13.row) 4609 183 (toTotals ⟨39549037523, 58970875077, 93491540688, 5028371912, 113895186⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0101
#print axioms piece0101

theorem join13_00 : ChunkFacts (toRow data13.row) 1 1024 (toTotals ⟨1287519599076178, 6760060204182, 22738832993532, 1271540826286828, 4306635842⟩) :=
  CleanupSegments208.append_exact piece0092 piece0093 rfl rfl rfl
#print axioms join13_00

theorem join13_01 : ChunkFacts (toRow data13.row) 1025 1024 (toTotals ⟨16772716390370, 1802639755086, 3192665090461, 15382691054995, 2004250359⟩) :=
  CleanupSegments208.append_exact piece0094 piece0095 rfl rfl rfl
#print axioms join13_01

theorem join13_02 : ChunkFacts (toRow data13.row) 2049 1024 (toTotals ⟨1601532548759, 652546568475, 1039194672676, 1214884444558, 1022857306⟩) :=
  CleanupSegments208.append_exact piece0096 piece0097 rfl rfl rfl
#print axioms join13_02

theorem join13_03 : ChunkFacts (toRow data13.row) 3073 1024 (toTotals ⟨334652525234, 347058100863, 550220706672, 131489919425, 706058989⟩) :=
  CleanupSegments208.append_exact piece0098 piece0099 rfl rfl rfl
#print axioms join13_03

theorem join13_04 : ChunkFacts (toRow data13.row) 4097 695 (toTotals ⟨159019434513, 223960427205, 355063501520, 27916360198, 493303104⟩) :=
  CleanupSegments208.append_exact piece0100 piece0101 rfl rfl rfl
#print axioms join13_04

theorem join13_05 : ChunkFacts (toRow data13.row) 1 2048 (toTotals ⟨1304292315466548, 8562699959268, 25931498083993, 1286923517341823, 6310886201⟩) :=
  CleanupSegments208.append_exact join13_00 join13_01 rfl rfl rfl
#print axioms join13_05

theorem join13_06 : ChunkFacts (toRow data13.row) 2049 2048 (toTotals ⟨1936185073993, 999604669338, 1589415379348, 1346374363983, 1728916295⟩) :=
  CleanupSegments208.append_exact join13_02 join13_03 rfl rfl rfl
#print axioms join13_06

theorem join13_07 : ChunkFacts (toRow data13.row) 1 4096 (toTotals ⟨1306228500540541, 9562304628606, 27520913463341, 1288269891705806, 8039802496⟩) :=
  CleanupSegments208.append_exact join13_05 join13_06 rfl rfl rfl
#print axioms join13_07

theorem join13_08 : ChunkFacts (toRow data13.row) 1 4791 (toTotals ⟨1306387519975054, 9786265055811, 27875976964861, 1288297808066004, 8533105600⟩) :=
  CleanupSegments208.append_exact join13_07 join13_04 rfl rfl rfl
#print axioms join13_08

theorem fact13 : ChunkFacts (toRow data13.row) 1 data13.steps (toTotals data13.total) := join13_08
#print axioms fact13

theorem piece0102 : ChunkFacts (toRow data14.row) 1 512 (toTotals ⟨996865788590616, 1087211151760, 15522175036221, 982430824706155, 1952527883⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0102
#print axioms piece0102

theorem piece0103 : ChunkFacts (toRow data14.row) 513 512 (toTotals ⟨26009797059188, 359473419296, 2322159792127, 24047110686357, 907961817⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0103
#print axioms piece0103

theorem piece0104 : ChunkFacts (toRow data14.row) 1025 512 (toTotals ⟨3353651859504, 151775312272, 841487445396, 2663939726380, 495116968⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0104
#print axioms piece0104

theorem piece0105 : ChunkFacts (toRow data14.row) 1537 512 (toTotals ⟨484810866727, 65137346160, 325018913806, 224929299081, 243448733⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0105
#print axioms piece0105

theorem piece0106 : ChunkFacts (toRow data14.row) 2049 478 (toTotals ⟨211216156250, 50627075552, 236887634828, 24955596974, 195476070⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0106
#print axioms piece0106

theorem join14_00 : ChunkFacts (toRow data14.row) 1 1024 (toTotals ⟨1022875585649804, 1446684571056, 17844334828348, 1006477935392512, 2860489700⟩) :=
  CleanupSegments208.append_exact piece0102 piece0103 rfl rfl rfl
#print axioms join14_00

theorem join14_01 : ChunkFacts (toRow data14.row) 1025 1024 (toTotals ⟨3838462726231, 216912658432, 1166506359202, 2888869025461, 738565701⟩) :=
  CleanupSegments208.append_exact piece0104 piece0105 rfl rfl rfl
#print axioms join14_01

theorem join14_02 : ChunkFacts (toRow data14.row) 1 2048 (toTotals ⟨1026714048376035, 1663597229488, 19010841187550, 1009366804417973, 3599055401⟩) :=
  CleanupSegments208.append_exact join14_00 join14_01 rfl rfl rfl
#print axioms join14_02

theorem join14_03 : ChunkFacts (toRow data14.row) 1 2526 (toTotals ⟨1026925264532285, 1714224305040, 19247728822378, 1009391760014947, 3794531471⟩) :=
  CleanupSegments208.append_exact join14_02 piece0106 rfl rfl rfl
#print axioms join14_03

theorem fact14 : ChunkFacts (toRow data14.row) 1 data14.steps (toTotals data14.total) := join14_03
#print axioms fact14

theorem piece0107 : ChunkFacts (toRow data15.row) 1 512 (toTotals ⟨1043648648087065, 1731700177746, 16070316754223, 1029310031510588, 2132605191⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0107
#print axioms piece0107

theorem piece0108 : ChunkFacts (toRow data15.row) 513 512 (toTotals ⟨32911549512975, 648258332414, 2754743204664, 30805064640725, 1069485411⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0108
#print axioms piece0108

theorem piece0109 : ChunkFacts (toRow data15.row) 1025 512 (toTotals ⟨4863373007831, 276467693425, 1026834674352, 4113006026904, 615413009⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0109
#print axioms piece0109

theorem piece0110 : ChunkFacts (toRow data15.row) 1537 512 (toTotals ⟨1022005356232, 135196595996, 471816405832, 685385546396, 347396397⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0110
#print axioms piece0110

theorem piece0111 : ChunkFacts (toRow data15.row) 2049 512 (toTotals ⟨224689676652, 79747300864, 253737382912, 50699594604, 233010044⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G06.checked0111
#print axioms piece0111

theorem piece0112 : ChunkFacts (toRow data15.row) 2561 305 (toTotals ⟨113490416309, 47505716335, 151152151930, 9843980714, 139278930⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0112
#print axioms piece0112

theorem join15_00 : ChunkFacts (toRow data15.row) 1 1024 (toTotals ⟨1076560197600040, 2379958510160, 18825059958887, 1060115096151313, 3202090602⟩) :=
  CleanupSegments208.append_exact piece0107 piece0108 rfl rfl rfl
#print axioms join15_00

theorem join15_01 : ChunkFacts (toRow data15.row) 1025 1024 (toTotals ⟨5885378364063, 411664289421, 1498651080184, 4798391573300, 962809406⟩) :=
  CleanupSegments208.append_exact piece0109 piece0110 rfl rfl rfl
#print axioms join15_01

theorem join15_02 : ChunkFacts (toRow data15.row) 2049 817 (toTotals ⟨338180092961, 127253017199, 404889534842, 60543575318, 372288974⟩) :=
  CleanupSegments208.append_exact piece0111 piece0112 rfl rfl rfl
#print axioms join15_02

theorem join15_03 : ChunkFacts (toRow data15.row) 1 2048 (toTotals ⟨1082445575964103, 2791622799581, 20323711039071, 1064913487724613, 4164900008⟩) :=
  CleanupSegments208.append_exact join15_00 join15_01 rfl rfl rfl
#print axioms join15_03

theorem join15_04 : ChunkFacts (toRow data15.row) 1 2865 (toTotals ⟨1082783756057064, 2918875816780, 20728600573913, 1064974031299931, 4537188982⟩) :=
  CleanupSegments208.append_exact join15_03 join15_02 rfl rfl rfl
#print axioms join15_04

theorem fact15 : ChunkFacts (toRow data15.row) 1 data15.steps (toTotals data15.total) := join15_04
#print axioms fact15

theorem piece0113 : ChunkFacts (toRow data16.row) 1 512 (toTotals ⟨1085204478691846, 2377267036848, 16553467005640, 1071028278723054, 2321038617⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0113
#print axioms piece0113

theorem piece0114 : ChunkFacts (toRow data16.row) 513 512 (toTotals ⟨40690112259444, 990262107684, 3200519623918, 38479854743210, 1237955416⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0114
#print axioms piece0114

theorem piece0115 : ChunkFacts (toRow data16.row) 1025 512 (toTotals ⟨6859842425282, 437015208384, 1252288761044, 6044568872622, 751730808⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0115
#print axioms piece0115

theorem piece0116 : ChunkFacts (toRow data16.row) 1537 512 (toTotals ⟨1788861257131, 245222949960, 669881587684, 1364202619407, 498347412⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0116
#print axioms piece0116

theorem piece0117 : ChunkFacts (toRow data16.row) 2049 512 (toTotals ⟨291682277536, 113041798884, 280994328342, 123729748078, 268138840⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0117
#print axioms piece0117

theorem piece0118 : ChunkFacts (toRow data16.row) 2561 512 (toTotals ⟨183883954914, 102076545024, 253737382912, 32223117026, 266180250⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0118
#print axioms piece0118

theorem piece0119 : ChunkFacts (toRow data16.row) 3073 175 (toTotals ⟨55939054303, 34889444100, 86726644550, 4101853853, 86528630⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0119
#print axioms piece0119

theorem join16_00 : ChunkFacts (toRow data16.row) 1 1024 (toTotals ⟨1125894590951290, 3367529144532, 19753986629558, 1109508133466264, 3558994033⟩) :=
  CleanupSegments208.append_exact piece0113 piece0114 rfl rfl rfl
#print axioms join16_00

theorem join16_01 : ChunkFacts (toRow data16.row) 1025 1024 (toTotals ⟨8648703682413, 682238158344, 1922170348728, 7408771492029, 1250078220⟩) :=
  CleanupSegments208.append_exact piece0115 piece0116 rfl rfl rfl
#print axioms join16_01

theorem join16_02 : ChunkFacts (toRow data16.row) 2049 1024 (toTotals ⟨475566232450, 215118343908, 534731711254, 155952865104, 534319090⟩) :=
  CleanupSegments208.append_exact piece0117 piece0118 rfl rfl rfl
#print axioms join16_02

theorem join16_03 : ChunkFacts (toRow data16.row) 1 2048 (toTotals ⟨1134543294633703, 4049767302876, 21676156978286, 1116916904958293, 4809072253⟩) :=
  CleanupSegments208.append_exact join16_00 join16_01 rfl rfl rfl
#print axioms join16_03

theorem join16_04 : ChunkFacts (toRow data16.row) 2049 1199 (toTotals ⟨531505286753, 250007788008, 621458355804, 160054718957, 620847720⟩) :=
  CleanupSegments208.append_exact join16_02 piece0119 rfl rfl rfl
#print axioms join16_04

theorem join16_05 : ChunkFacts (toRow data16.row) 1 3247 (toTotals ⟨1135074799920456, 4299775090884, 22297615334090, 1117076959677250, 5429919973⟩) :=
  CleanupSegments208.append_exact join16_03 join16_04 rfl rfl rfl
#print axioms join16_05

theorem fact16 : ChunkFacts (toRow data16.row) 1 data16.steps (toTotals data16.total) := join16_05
#print axioms fact16

theorem piece0120 : ChunkFacts (toRow data17.row) 1 512 (toTotals ⟨1101566154672413, 2813260490568, 16802594607321, 1087576820555660, 2445672423⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0120
#print axioms piece0120

theorem piece0121 : ChunkFacts (toRow data17.row) 513 512 (toTotals ⟨44529999020639, 1247110722220, 3455268695539, 42321841047320, 1349642494⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0121
#print axioms piece0121

theorem piece0122 : ChunkFacts (toRow data17.row) 1025 512 (toTotals ⟨8122454088236, 571918983702, 1414768893659, 7279604178279, 848380203⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0122
#print axioms piece0122

theorem piece0123 : ChunkFacts (toRow data17.row) 1537 512 (toTotals ⟨2509080982297, 340016324450, 805444936838, 2043652369909, 610283820⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0123
#print axioms piece0123

theorem piece0124 : ChunkFacts (toRow data17.row) 2049 512 (toTotals ⟨440201141014, 160441601232, 344924254896, 255718487350, 331921920⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0124
#print axioms piece0124

theorem piece0125 : ChunkFacts (toRow data17.row) 2561 512 (toTotals ⟨183883954914, 118026005504, 253737382912, 48172577506, 280600730⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0125
#print axioms piece0125

theorem piece0126 : ChunkFacts (toRow data17.row) 3073 512 (toTotals ⟨155722376986, 118026005504, 253737382912, 20010999578, 291408661⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0126
#print axioms piece0126

theorem piece0127 : ChunkFacts (toRow data17.row) 3585 5 (toTotals ⟨1409498362, 1152597710, 2477904130, 84191942, 210405⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G07.checked0127
#print axioms piece0127

theorem join17_00 : ChunkFacts (toRow data17.row) 1 1024 (toTotals ⟨1146096153693052, 4060371212788, 20257863302860, 1129898661602980, 3795314917⟩) :=
  CleanupSegments208.append_exact piece0120 piece0121 rfl rfl rfl
#print axioms join17_00

theorem join17_01 : ChunkFacts (toRow data17.row) 1025 1024 (toTotals ⟨10631535070533, 911935308152, 2220213830497, 9323256548188, 1458664023⟩) :=
  CleanupSegments208.append_exact piece0122 piece0123 rfl rfl rfl
#print axioms join17_01

theorem join17_02 : ChunkFacts (toRow data17.row) 2049 1024 (toTotals ⟨624085095928, 278467606736, 598661637808, 303891064856, 612522650⟩) :=
  CleanupSegments208.append_exact piece0124 piece0125 rfl rfl rfl
#print axioms join17_02

theorem join17_03 : ChunkFacts (toRow data17.row) 3073 517 (toTotals ⟨157131875348, 119178603214, 256215287042, 20095191520, 291619066⟩) :=
  CleanupSegments208.append_exact piece0126 piece0127 rfl rfl rfl
#print axioms join17_03

theorem join17_04 : ChunkFacts (toRow data17.row) 1 2048 (toTotals ⟨1156727688763585, 4972306520940, 22478077133357, 1139221918151168, 5253978940⟩) :=
  CleanupSegments208.append_exact join17_00 join17_01 rfl rfl rfl
#print axioms join17_04

theorem join17_05 : ChunkFacts (toRow data17.row) 2049 1541 (toTotals ⟨781216971276, 397646209950, 854876924850, 323986256376, 904141716⟩) :=
  CleanupSegments208.append_exact join17_02 join17_03 rfl rfl rfl
#print axioms join17_05

theorem join17_06 : ChunkFacts (toRow data17.row) 1 3589 (toTotals ⟨1157508905734861, 5369952730890, 23332954058207, 1139545904407544, 6158120656⟩) :=
  CleanupSegments208.append_exact join17_04 join17_05 rfl rfl rfl
#print axioms join17_06

theorem fact17 : ChunkFacts (toRow data17.row) 1 data17.steps (toTotals data17.total) := join17_06
#print axioms fact17

theorem piece0128 : ChunkFacts (toRow data18.row) 1 512 (toTotals ⟨1154000655142175, 3415851027874, 17335616711461, 1140080889458588, 2585111285⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0128
#print axioms piece0128

theorem piece0129 : ChunkFacts (toRow data18.row) 513 512 (toTotals ⟨49647621649408, 1567408277690, 3782217148918, 47432812778180, 1476284229⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0129
#print axioms piece0129

theorem piece0130 : ChunkFacts (toRow data18.row) 1025 512 (toTotals ⟨9812426221181, 746023539181, 1619347004606, 8939102755756, 967959216⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0130
#print axioms piece0130

theorem piece0131 : ChunkFacts (toRow data18.row) 1537 512 (toTotals ⟨3327739497518, 462895700039, 966667056570, 2823968140987, 745054141⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0131
#print axioms piece0131

theorem piece0132 : ChunkFacts (toRow data18.row) 2049 512 (toTotals ⟨614393896663, 223466889674, 423226025404, 414634760933, 416252732⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0132
#print axioms piece0132

theorem piece0133 : ChunkFacts (toRow data18.row) 2561 512 (toTotals ⟨234793941652, 147582348684, 279507585864, 102868704472, 315745560⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0133
#print axioms piece0133

theorem piece0134 : ChunkFacts (toRow data18.row) 3073 512 (toTotals ⟨155722376986, 133975465472, 253737382912, 35960459546, 316897877⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0134
#print axioms piece0134

theorem piece0135 : ChunkFacts (toRow data18.row) 3585 427 (toTotals ⟨113876401544, 111733444837, 211613012702, 13996833679, 265515325⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0135
#print axioms piece0135

theorem join18_00 : ChunkFacts (toRow data18.row) 1 1024 (toTotals ⟨1203648276791583, 4983259305564, 21117833860379, 1187513702236768, 4061395514⟩) :=
  CleanupSegments208.append_exact piece0128 piece0129 rfl rfl rfl
#print axioms join18_00

theorem join18_01 : ChunkFacts (toRow data18.row) 1025 1024 (toTotals ⟨13140165718699, 1208919239220, 2586014061176, 11763070896743, 1713013357⟩) :=
  CleanupSegments208.append_exact piece0130 piece0131 rfl rfl rfl
#print axioms join18_01

theorem join18_02 : ChunkFacts (toRow data18.row) 2049 1024 (toTotals ⟨849187838315, 371049238358, 702733611268, 517503465405, 731998292⟩) :=
  CleanupSegments208.append_exact piece0132 piece0133 rfl rfl rfl
#print axioms join18_02

theorem join18_03 : ChunkFacts (toRow data18.row) 3073 939 (toTotals ⟨269598778530, 245708910309, 465350395614, 49957293225, 582413202⟩) :=
  CleanupSegments208.append_exact piece0134 piece0135 rfl rfl rfl
#print axioms join18_03

theorem join18_04 : ChunkFacts (toRow data18.row) 1 2048 (toTotals ⟨1216788442510282, 6192178544784, 23703847921555, 1199276773133511, 5774408871⟩) :=
  CleanupSegments208.append_exact join18_00 join18_01 rfl rfl rfl
#print axioms join18_04

theorem join18_05 : ChunkFacts (toRow data18.row) 2049 1963 (toTotals ⟨1118786616845, 616758148667, 1168084006882, 567460758630, 1314411494⟩) :=
  CleanupSegments208.append_exact join18_02 join18_03 rfl rfl rfl
#print axioms join18_05

theorem join18_06 : ChunkFacts (toRow data18.row) 1 4011 (toTotals ⟨1217907229127127, 6808936693451, 24871931928437, 1199844233892141, 7088820365⟩) :=
  CleanupSegments208.append_exact join18_04 join18_05 rfl rfl rfl
#print axioms join18_06

theorem fact18 : ChunkFacts (toRow data18.row) 1 data18.steps (toTotals data18.total) := join18_06
#print axioms fact18

theorem piece0136 : ChunkFacts (toRow data19.row) 1 512 (toTotals ⟨1192369262286903, 3878447681979, 17710375518710, 1178537334450172, 2712193857⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0136
#print axioms piece0136

theorem piece0137 : ChunkFacts (toRow data19.row) 513 512 (toTotals ⟨53655776087378, 1839633168597, 4026541428599, 51468867827376, 1592889659⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0137
#print axioms piece0137

theorem piece0138 : ChunkFacts (toRow data19.row) 1025 512 (toTotals ⟨11181172569789, 914801226696, 1806981529675, 10288992266810, 1078105349⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0138
#print axioms piece0138

theorem piece0139 : ChunkFacts (toRow data19.row) 1537 512 (toTotals ⟨4043249398532, 568311664329, 1083330888422, 3528230174439, 851201964⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0139
#print axioms piece0139

theorem piece0140 : ChunkFacts (toRow data19.row) 2049 512 (toTotals ⟨867422337635, 296622578205, 514104992142, 649939923698, 504015398⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0140
#print axioms piece0140

theorem piece0141 : ChunkFacts (toRow data19.row) 2561 512 (toTotals ⟨375214295780, 204913182045, 354340290590, 225787187235, 400634827⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0141
#print axioms piece0141

theorem piece0142 : ChunkFacts (toRow data19.row) 3073 512 (toTotals ⟨155722376986, 146735033856, 253737382912, 48720027930, 330531413⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0142
#print axioms piece0142

theorem piece0143 : ChunkFacts (toRow data19.row) 3585 512 (toTotals ⟨135108901836, 146735033856, 253737382912, 28106552780, 354510925⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G08.checked0143
#print axioms piece0143

theorem piece0144 : ChunkFacts (toRow data19.row) 4097 332 (toTotals ⟨78962198312, 95148498516, 164532834232, 9577862596, 221664823⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0144
#print axioms piece0144

theorem join19_00 : ChunkFacts (toRow data19.row) 1 1024 (toTotals ⟨1246025038374281, 5718080850576, 21736916947309, 1230006202277548, 4305083516⟩) :=
  CleanupSegments208.append_exact piece0136 piece0137 rfl rfl rfl
#print axioms join19_00

theorem join19_01 : ChunkFacts (toRow data19.row) 1025 1024 (toTotals ⟨15224421968321, 1483112891025, 2890312418097, 13817222441249, 1929307313⟩) :=
  CleanupSegments208.append_exact piece0138 piece0139 rfl rfl rfl
#print axioms join19_01

theorem join19_02 : ChunkFacts (toRow data19.row) 2049 1024 (toTotals ⟨1242636633415, 501535760250, 868445282732, 875727110933, 904650225⟩) :=
  CleanupSegments208.append_exact piece0140 piece0141 rfl rfl rfl
#print axioms join19_02

theorem join19_03 : ChunkFacts (toRow data19.row) 3073 1024 (toTotals ⟨290831278822, 293470067712, 507474765824, 76826580710, 685042338⟩) :=
  CleanupSegments208.append_exact piece0142 piece0143 rfl rfl rfl
#print axioms join19_03

theorem join19_04 : ChunkFacts (toRow data19.row) 1 2048 (toTotals ⟨1261249460342602, 7201193741601, 24627229365406, 1243823424718797, 6234390829⟩) :=
  CleanupSegments208.append_exact join19_00 join19_01 rfl rfl rfl
#print axioms join19_04

theorem join19_05 : ChunkFacts (toRow data19.row) 2049 2048 (toTotals ⟨1533467912237, 795005827962, 1375920048556, 952553691643, 1589692563⟩) :=
  CleanupSegments208.append_exact join19_02 join19_03 rfl rfl rfl
#print axioms join19_05

theorem join19_06 : ChunkFacts (toRow data19.row) 1 4096 (toTotals ⟨1262782928254839, 7996199569563, 26003149413962, 1244775978410440, 7824083392⟩) :=
  CleanupSegments208.append_exact join19_04 join19_05 rfl rfl rfl
#print axioms join19_06

theorem join19_07 : ChunkFacts (toRow data19.row) 1 4428 (toTotals ⟨1262861890453151, 8091348068079, 26167682248194, 1244785556273036, 8045748215⟩) :=
  CleanupSegments208.append_exact join19_06 piece0144 rfl rfl rfl
#print axioms join19_07

theorem fact19 : ChunkFacts (toRow data19.row) 1 data19.steps (toTotals data19.total) := join19_07
#print axioms fact19

theorem piece0145 : ChunkFacts (toRow data20.row) 1 512 (toTotals ⟨1216522932890462, 4268156533916, 17998390086775, 1202792699337603, 2834661789⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0145
#print axioms piece0145

theorem piece0146 : ChunkFacts (toRow data20.row) 513 512 (toTotals ⟨58483944549507, 2114998102208, 4318277251451, 56280665400264, 1707206594⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0146
#print axioms piece0146

theorem piece0147 : ChunkFacts (toRow data20.row) 1025 512 (toTotals ⟨12525189874589, 1068183943364, 1977355766328, 11616018051625, 1179660844⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0147
#print axioms piece0147

theorem piece0148 : ChunkFacts (toRow data20.row) 1537 512 (toTotals ⟨4569913569113, 658799928488, 1170057532972, 4058655964629, 929403102⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0148
#print axioms piece0148

theorem piece0149 : ChunkFacts (toRow data20.row) 2049 512 (toTotals ⟨1254248369473, 381908577636, 633724714366, 1002432232743, 614338269⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0149
#print axioms piece0149

theorem piece0150 : ChunkFacts (toRow data20.row) 2561 512 (toTotals ⟨475631614236, 252163457336, 409349762276, 318445309296, 472928472⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0150
#print axioms piece0150

theorem piece0151 : ChunkFacts (toRow data20.row) 3073 512 (toTotals ⟨202301068225, 173705819884, 281985489994, 94021398115, 367209061⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0151
#print axioms piece0151

theorem piece0152 : ChunkFacts (toRow data20.row) 3585 512 (toTotals ⟨135108901836, 156304709632, 253737382912, 37676228556, 366308941⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0152
#print axioms piece0152

theorem piece0153 : ChunkFacts (toRow data20.row) 4097 512 (toTotals ⟨119364419646, 156304709632, 253737382912, 21931746366, 391898768⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0153
#print axioms piece0153

theorem piece0154 : ChunkFacts (toRow data20.row) 4609 195 (toTotals ⟨42049844514, 59530114020, 96638261070, 4941697464, 128507032⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0154
#print axioms piece0154

theorem join20_00 : ChunkFacts (toRow data20.row) 1 1024 (toTotals ⟨1275006877439969, 6383154636124, 22316667338226, 1259073364737867, 4541868383⟩) :=
  CleanupSegments208.append_exact piece0145 piece0146 rfl rfl rfl
#print axioms join20_00

theorem join20_01 : ChunkFacts (toRow data20.row) 1025 1024 (toTotals ⟨17095103443702, 1726983871852, 3147413299300, 15674674016254, 2109063946⟩) :=
  CleanupSegments208.append_exact piece0147 piece0148 rfl rfl rfl
#print axioms join20_01

theorem join20_02 : ChunkFacts (toRow data20.row) 2049 1024 (toTotals ⟨1729879983709, 634072034972, 1043074476642, 1320877542039, 1087266741⟩) :=
  CleanupSegments208.append_exact piece0149 piece0150 rfl rfl rfl
#print axioms join20_02

theorem join20_03 : ChunkFacts (toRow data20.row) 3073 1024 (toTotals ⟨337409970061, 330010529516, 535722872906, 131697626671, 733518002⟩) :=
  CleanupSegments208.append_exact piece0151 piece0152 rfl rfl rfl
#print axioms join20_03

theorem join20_04 : ChunkFacts (toRow data20.row) 4097 707 (toTotals ⟨161414264160, 215834823652, 350375643982, 26873443830, 520405800⟩) :=
  CleanupSegments208.append_exact piece0153 piece0154 rfl rfl rfl
#print axioms join20_04

theorem join20_05 : ChunkFacts (toRow data20.row) 1 2048 (toTotals ⟨1292101980883671, 8110138507976, 25464080637526, 1274748038754121, 6650932329⟩) :=
  CleanupSegments208.append_exact join20_00 join20_01 rfl rfl rfl
#print axioms join20_05

theorem join20_06 : ChunkFacts (toRow data20.row) 2049 2048 (toTotals ⟨2067289953770, 964082564488, 1578797349548, 1452575168710, 1820784743⟩) :=
  CleanupSegments208.append_exact join20_02 join20_03 rfl rfl rfl
#print axioms join20_06

theorem join20_07 : ChunkFacts (toRow data20.row) 1 4096 (toTotals ⟨1294169270837441, 9074221072464, 27042877987074, 1276200613922831, 8471717072⟩) :=
  CleanupSegments208.append_exact join20_05 join20_06 rfl rfl rfl
#print axioms join20_07

theorem join20_08 : ChunkFacts (toRow data20.row) 1 4803 (toTotals ⟨1294330685101601, 9290055896116, 27393253631056, 1276227487366661, 8992122872⟩) :=
  CleanupSegments208.append_exact join20_07 join20_04 rfl rfl rfl
#print axioms join20_08

theorem fact20 : ChunkFacts (toRow data20.row) 1 data20.steps (toTotals data20.total) := join20_08
#print axioms fact20

theorem piece0155 : ChunkFacts (toRow data21.row) 1 512 (toTotals ⟨995823719811915, 1029626271720, 15391507274180, 981461838809455, 2070861960⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0155
#print axioms piece0155

theorem piece0156 : ChunkFacts (toRow data21.row) 513 512 (toTotals ⟨26600011446323, 344471653800, 2324737197941, 24619745902182, 968147363⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0156
#print axioms piece0156

theorem piece0157 : ChunkFacts (toRow data21.row) 1025 512 (toTotals ⟨3522151060290, 145864552680, 847236263863, 2820779349107, 531009577⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0157
#print axioms piece0157

theorem piece0158 : ChunkFacts (toRow data21.row) 1537 512 (toTotals ⟨528469495786, 63709808040, 334376687759, 257802616067, 265539670⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0158
#print axioms piece0158

theorem piece0159 : ChunkFacts (toRow data21.row) 2049 512 (toTotals ⟨224596131180, 51047608320, 248189133312, 27454606188, 220277183⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G09.checked0159
#print axioms piece0159

theorem join21_00 : ChunkFacts (toRow data21.row) 1 1024 (toTotals ⟨1022423731258238, 1374097925520, 17716244472121, 1006081584711637, 3039009323⟩) :=
  CleanupSegments208.append_exact piece0155 piece0156 rfl rfl rfl
#print axioms join21_00

theorem join21_01 : ChunkFacts (toRow data21.row) 1025 1024 (toTotals ⟨4050620556076, 209574360720, 1181612951622, 3078581965174, 796549247⟩) :=
  CleanupSegments208.append_exact piece0157 piece0158 rfl rfl rfl
#print axioms join21_01

theorem join21_02 : ChunkFacts (toRow data21.row) 1 2048 (toTotals ⟨1026474351814314, 1583672286240, 18897857423743, 1009160166676811, 3835558570⟩) :=
  CleanupSegments208.append_exact join21_00 join21_01 rfl rfl rfl
#print axioms join21_02

theorem join21_03 : ChunkFacts (toRow data21.row) 1 2560 (toTotals ⟨1026698947945494, 1634719894560, 19146046557055, 1009187621282999, 4055835753⟩) :=
  CleanupSegments208.append_exact join21_02 piece0159 rfl rfl rfl
#print axioms join21_03

theorem fact21 : ChunkFacts (toRow data21.row) 1 data21.steps (toTotals data21.total) := join21_03
#print axioms fact21

theorem piece0160 : ChunkFacts (toRow data22.row) 1 512 (toTotals ⟨1034694338642366, 1625441703062, 15883135045576, 1020436645299852, 2251253391⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0160
#print axioms piece0160

theorem piece0161 : ChunkFacts (toRow data22.row) 513 512 (toTotals ⟨33341082341271, 614342480230, 2732504188005, 31222920633496, 1130066589⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0161
#print axioms piece0161

theorem piece0162 : ChunkFacts (toRow data22.row) 1025 512 (toTotals ⟨4958351707407, 262158557196, 1023198481426, 4197311783177, 652563160⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0162
#print axioms piece0162

theorem piece0163 : ChunkFacts (toRow data22.row) 1537 512 (toTotals ⟨1058595525175, 129759688545, 474176972965, 714178240755, 371238658⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0163
#print axioms piece0163

theorem piece0164 : ChunkFacts (toRow data22.row) 2049 512 (toTotals ⟨224596131180, 75070011904, 248189133312, 51477009772, 243244347⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0164
#print axioms piece0164

theorem piece0165 : ChunkFacts (toRow data22.row) 2561 328 (toTotals ⟨121496617870, 48091726376, 158996163528, 10592180718, 156669052⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0165
#print axioms piece0165

theorem join22_00 : ChunkFacts (toRow data22.row) 1 1024 (toTotals ⟨1068035420983637, 2239784183292, 18615639233581, 1051659565933348, 3381319980⟩) :=
  CleanupSegments208.append_exact piece0160 piece0161 rfl rfl rfl
#print axioms join22_00

theorem join22_01 : ChunkFacts (toRow data22.row) 1025 1024 (toTotals ⟨6016947232582, 391918245741, 1497375454391, 4911490023932, 1023801818⟩) :=
  CleanupSegments208.append_exact piece0162 piece0163 rfl rfl rfl
#print axioms join22_01

theorem join22_02 : ChunkFacts (toRow data22.row) 2049 840 (toTotals ⟨346092749050, 123161738280, 407185296840, 62069190490, 399913399⟩) :=
  CleanupSegments208.append_exact piece0164 piece0165 rfl rfl rfl
#print axioms join22_02

theorem join22_03 : ChunkFacts (toRow data22.row) 1 2048 (toTotals ⟨1074052368216219, 2631702429033, 20113014687972, 1056571055957280, 4405121798⟩) :=
  CleanupSegments208.append_exact join22_00 join22_01 rfl rfl rfl
#print axioms join22_03

theorem join22_04 : ChunkFacts (toRow data22.row) 1 2888 (toTotals ⟨1074398460965269, 2754864167313, 20520199984812, 1056633125147770, 4805035197⟩) :=
  CleanupSegments208.append_exact join22_03 join22_02 rfl rfl rfl
#print axioms join22_04

theorem fact22 : ChunkFacts (toRow data22.row) 1 data22.steps (toTotals data22.total) := join22_04
#print axioms fact22

theorem piece0166 : ChunkFacts (toRow data23.row) 1 512 (toTotals ⟨1085050351292781, 2250974297826, 16413445420235, 1070887880170372, 2448777995⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0166
#print axioms piece0166

theorem piece0167 : ChunkFacts (toRow data23.row) 513 512 (toTotals ⟨40934979384858, 936686069739, 3164217551482, 38707447903115, 1304192598⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0167
#print axioms piece0167

theorem piece0168 : ChunkFacts (toRow data23.row) 1025 512 (toTotals ⟨6962519730017, 414574139061, 1244144979393, 6132948889685, 793320638⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0168
#print axioms piece0168

theorem piece0169 : ChunkFacts (toRow data23.row) 1537 512 (toTotals ⟨1827958989507, 233467736076, 665844909084, 1395581816499, 527471052⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0169
#print axioms piece0169

theorem piece0170 : ChunkFacts (toRow data23.row) 2049 512 (toTotals ⟨292445717032, 106599416472, 275334819768, 123710313736, 279788847⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0170
#print axioms piece0170

theorem piece0171 : ChunkFacts (toRow data23.row) 2561 512 (toTotals ⟨183790409442, 96089614848, 248189133312, 31690890978, 276409510⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0171
#print axioms piece0171

theorem piece0172 : ChunkFacts (toRow data23.row) 3073 180 (toTotals ⟨57460204701, 33781505220, 87253992180, 3987717741, 92813372⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0172
#print axioms piece0172

theorem join23_00 : ChunkFacts (toRow data23.row) 1 1024 (toTotals ⟨1125985330677639, 3187660367565, 19577662971717, 1109595328073487, 3752970593⟩) :=
  CleanupSegments208.append_exact piece0166 piece0167 rfl rfl rfl
#print axioms join23_00

theorem join23_01 : ChunkFacts (toRow data23.row) 1025 1024 (toTotals ⟨8790478719524, 648041875137, 1909989888477, 7528530706184, 1320791690⟩) :=
  CleanupSegments208.append_exact piece0168 piece0169 rfl rfl rfl
#print axioms join23_01

theorem join23_02 : ChunkFacts (toRow data23.row) 2049 1024 (toTotals ⟨476236126474, 202689031320, 523523953080, 155401204714, 556198357⟩) :=
  CleanupSegments208.append_exact piece0170 piece0171 rfl rfl rfl
#print axioms join23_02

theorem join23_03 : ChunkFacts (toRow data23.row) 1 2048 (toTotals ⟨1134775809397163, 3835702242702, 21487652860194, 1117123858779671, 5073762283⟩) :=
  CleanupSegments208.append_exact join23_00 join23_01 rfl rfl rfl
#print axioms join23_03

theorem join23_04 : ChunkFacts (toRow data23.row) 2049 1204 (toTotals ⟨533696331175, 236470536540, 610777945260, 159388922455, 649011729⟩) :=
  CleanupSegments208.append_exact join23_02 piece0172 rfl rfl rfl
#print axioms join23_04

theorem join23_05 : ChunkFacts (toRow data23.row) 1 3252 (toTotals ⟨1135309505728338, 4072172779242, 22098430805454, 1117283247702126, 5722774012⟩) :=
  CleanupSegments208.append_exact join23_03 join23_04 rfl rfl rfl
#print axioms join23_05

theorem fact23 : ChunkFacts (toRow data23.row) 1 data23.steps (toTotals data23.total) := join23_05
#print axioms fact23

theorem piece0173 : ChunkFacts (toRow data24.row) 1 512 (toTotals ⟨1100092001644511, 2655419858961, 16639142413314, 1086108279090158, 2572397402⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0173
#print axioms piece0173

theorem piece0174 : ChunkFacts (toRow data24.row) 513 512 (toTotals ⟨44492762228232, 1172880962465, 3398155199369, 42267487991328, 1415039604⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0174
#print axioms piece0174

theorem piece0175 : ChunkFacts (toRow data24.row) 1025 512 (toTotals ⟨8198112771446, 540545139223, 1399360136578, 7339297774091, 890804166⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G10.checked0175
#print axioms piece0175

theorem piece0176 : ChunkFacts (toRow data24.row) 1537 512 (toTotals ⟨2515367640742, 321809892199, 795271664123, 2041905868818, 639599902⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0176
#print axioms piece0176

theorem piece0177 : ChunkFacts (toRow data24.row) 2049 512 (toTotals ⟨432407058294, 149729484570, 334473636690, 247662906174, 342143557⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0177
#print axioms piece0177

theorem piece0178 : ChunkFacts (toRow data24.row) 2561 512 (toTotals ⟨183790409442, 111103617536, 248189133312, 46704893666, 290829990⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0178
#print axioms piece0178

theorem piece0179 : ChunkFacts (toRow data24.row) 3073 502 (toTotals ⟨152805819211, 108933625006, 243341689302, 18397754915, 292852555⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0179
#print axioms piece0179

theorem join24_00 : ChunkFacts (toRow data24.row) 1 1024 (toTotals ⟨1144584763872743, 3828300821426, 20037297612683, 1128375767081486, 3987437006⟩) :=
  CleanupSegments208.append_exact piece0173 piece0174 rfl rfl rfl
#print axioms join24_00

theorem join24_01 : ChunkFacts (toRow data24.row) 1025 1024 (toTotals ⟨10713480412188, 862355031422, 2194631800701, 9381203642909, 1530404068⟩) :=
  CleanupSegments208.append_exact piece0175 piece0176 rfl rfl rfl
#print axioms join24_01

theorem join24_02 : ChunkFacts (toRow data24.row) 2049 1024 (toTotals ⟨616197467736, 260833102106, 582662770002, 294367799840, 632973547⟩) :=
  CleanupSegments208.append_exact piece0177 piece0178 rfl rfl rfl
#print axioms join24_02

theorem join24_03 : ChunkFacts (toRow data24.row) 1 2048 (toTotals ⟨1155298244284931, 4690655852848, 22231929413384, 1137756970724395, 5517841074⟩) :=
  CleanupSegments208.append_exact join24_00 join24_01 rfl rfl rfl
#print axioms join24_03

theorem join24_04 : ChunkFacts (toRow data24.row) 2049 1526 (toTotals ⟨769003286947, 369766727112, 826004459304, 312765554755, 925826102⟩) :=
  CleanupSegments208.append_exact join24_02 piece0179 rfl rfl rfl
#print axioms join24_04

theorem join24_05 : ChunkFacts (toRow data24.row) 1 3574 (toTotals ⟨1156067247571878, 5060422579960, 23057933872688, 1138069736279150, 6443667176⟩) :=
  CleanupSegments208.append_exact join24_03 join24_04 rfl rfl rfl
#print axioms join24_05

theorem fact24 : ChunkFacts (toRow data24.row) 1 data24.steps (toTotals data24.total) := join24_05
#print axioms fact24

theorem piece0180 : ChunkFacts (toRow data25.row) 1 512 (toTotals ⟨1124939856414674, 3138900054668, 16950057472105, 1111128698997237, 2708698269⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0180
#print axioms piece0180

theorem piece0181 : ChunkFacts (toRow data25.row) 513 512 (toTotals ⟨49245327699750, 1464885711772, 3695109619372, 47015103792150, 1538974336⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0181
#print axioms piece0181

theorem piece0182 : ChunkFacts (toRow data25.row) 1025 512 (toTotals ⟨9786937491114, 699312348364, 1587634861906, 8898614977572, 1008606539⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0182
#print axioms piece0182

theorem piece0183 : ChunkFacts (toRow data25.row) 1537 512 (toTotals ⟨3261938910482, 432790347332, 942633961997, 2752095295817, 772426864⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0183
#print axioms piece0183

theorem piece0184 : ChunkFacts (toRow data25.row) 2049 512 (toTotals ⟨598870713279, 207404366792, 408154785642, 398120294429, 426394476⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0184
#print axioms piece0184

theorem piece0185 : ChunkFacts (toRow data25.row) 2561 512 (toTotals ⟨219994184044, 135231588324, 266124676149, 89101096219, 320052089⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0185
#print axioms piece0185

theorem piece0186 : ChunkFacts (toRow data25.row) 3073 512 (toTotals ⟨155628831514, 126117619712, 248189133312, 33557317914, 327141680⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0186
#print axioms piece0186

theorem piece0187 : ChunkFacts (toRow data25.row) 3585 383 (toTotals ⟨102640296712, 94341891308, 185657105583, 11325082437, 243865969⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0187
#print axioms piece0187

theorem join25_00 : ChunkFacts (toRow data25.row) 1 1024 (toTotals ⟨1174185184114424, 4603785766440, 20645167091477, 1158143802789387, 4247672605⟩) :=
  CleanupSegments208.append_exact piece0180 piece0181 rfl rfl rfl
#print axioms join25_00

theorem join25_01 : ChunkFacts (toRow data25.row) 1025 1024 (toTotals ⟨13048876401596, 1132102695696, 2530268823903, 11650710273389, 1781033403⟩) :=
  CleanupSegments208.append_exact piece0182 piece0183 rfl rfl rfl
#print axioms join25_01

theorem join25_02 : ChunkFacts (toRow data25.row) 2049 1024 (toTotals ⟨818864897323, 342635955116, 674279461791, 487221390648, 746446565⟩) :=
  CleanupSegments208.append_exact piece0184 piece0185 rfl rfl rfl
#print axioms join25_02

theorem join25_03 : ChunkFacts (toRow data25.row) 3073 895 (toTotals ⟨258269128226, 220459511020, 433846238895, 44882400351, 571007649⟩) :=
  CleanupSegments208.append_exact piece0186 piece0187 rfl rfl rfl
#print axioms join25_03

theorem join25_04 : ChunkFacts (toRow data25.row) 1 2048 (toTotals ⟨1187234060516020, 5735888462136, 23175435915380, 1169794513062776, 6028706008⟩) :=
  CleanupSegments208.append_exact join25_00 join25_01 rfl rfl rfl
#print axioms join25_04

theorem join25_05 : ChunkFacts (toRow data25.row) 2049 1919 (toTotals ⟨1077134025549, 563095466136, 1108125700686, 532103790999, 1317454214⟩) :=
  CleanupSegments208.append_exact join25_02 join25_03 rfl rfl rfl
#print axioms join25_05

theorem join25_06 : ChunkFacts (toRow data25.row) 1 3967 (toTotals ⟨1188311194541569, 6298983928272, 24283561616066, 1170326616853775, 7346160222⟩) :=
  CleanupSegments208.append_exact join25_04 join25_05 rfl rfl rfl
#print axioms join25_06

theorem fact25 : ChunkFacts (toRow data25.row) 1 data25.steps (toTotals data25.total) := join25_06
#print axioms fact25

theorem piece0188 : ChunkFacts (toRow data26.row) 1 512 (toTotals ⟨1159754726155846, 3594856542875, 17327673360353, 1146021909338368, 2830119540⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0188
#print axioms piece0188

theorem piece0189 : ChunkFacts (toRow data26.row) 513 512 (toTotals ⟨52729989951983, 1716088740655, 3929435062775, 50516643629863, 1649154863⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0189
#print axioms piece0189

theorem piece0190 : ChunkFacts (toRow data26.row) 1025 512 (toTotals ⟨11072043646212, 851434690380, 1758749635439, 10164728701153, 1114665209⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0190
#print axioms piece0190

theorem piece0191 : ChunkFacts (toRow data26.row) 1537 512 (toTotals ⟨3907878300621, 526346350105, 1045011979471, 3389212671255, 873415787⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G11.checked0191
#print axioms piece0191

theorem piece0192 : ChunkFacts (toRow data26.row) 2049 512 (toTotals ⟨838335355183, 272480683550, 492306413650, 618509625083, 509969012⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0192
#print axioms piece0192

theorem piece0193 : ChunkFacts (toRow data26.row) 2561 512 (toTotals ⟨344383420576, 183991907110, 330595681482, 197779646204, 396957478⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0193
#print axioms piece0193

theorem piece0194 : ChunkFacts (toRow data26.row) 3073 512 (toTotals ⟨155628831514, 138128821760, 248189133312, 45568519962, 340775216⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0194
#print axioms piece0194

theorem piece0195 : ChunkFacts (toRow data26.row) 3585 512 (toTotals ⟨135015356364, 138128821760, 248189133312, 24955044812, 364769204⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0195
#print axioms piece0195

theorem piece0196 : ChunkFacts (toRow data26.row) 4097 253 (toTotals ⟨60669848237, 68255062315, 122640333453, 6284577099, 169461957⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0196
#print axioms piece0196

theorem join26_00 : ChunkFacts (toRow data26.row) 1 1024 (toTotals ⟨1212484716107829, 5310945283530, 21257108423128, 1196538552968231, 4479274403⟩) :=
  CleanupSegments208.append_exact piece0188 piece0189 rfl rfl rfl
#print axioms join26_00

theorem join26_01 : ChunkFacts (toRow data26.row) 1025 1024 (toTotals ⟨14979921946833, 1377781040485, 2803761614910, 13553941372408, 1988080996⟩) :=
  CleanupSegments208.append_exact piece0190 piece0191 rfl rfl rfl
#print axioms join26_01

theorem join26_02 : ChunkFacts (toRow data26.row) 2049 1024 (toTotals ⟨1182718775759, 456472590660, 822902095132, 816289271287, 906926490⟩) :=
  CleanupSegments208.append_exact piece0192 piece0193 rfl rfl rfl
#print axioms join26_02

theorem join26_03 : ChunkFacts (toRow data26.row) 3073 1024 (toTotals ⟨290644187878, 276257643520, 496378266624, 70523564774, 705544420⟩) :=
  CleanupSegments208.append_exact piece0194 piece0195 rfl rfl rfl
#print axioms join26_03

theorem join26_04 : ChunkFacts (toRow data26.row) 1 2048 (toTotals ⟨1227464638054662, 6688726324015, 24060870038038, 1210092494340639, 6467355399⟩) :=
  CleanupSegments208.append_exact join26_00 join26_01 rfl rfl rfl
#print axioms join26_04

theorem join26_05 : ChunkFacts (toRow data26.row) 2049 2048 (toTotals ⟨1473362963637, 732730234180, 1319280361756, 886812836061, 1612470910⟩) :=
  CleanupSegments208.append_exact join26_02 join26_03 rfl rfl rfl
#print axioms join26_05

theorem join26_06 : ChunkFacts (toRow data26.row) 1 4096 (toTotals ⟨1228938001018299, 7421456558195, 25380150399794, 1210979307176700, 8079826309⟩) :=
  CleanupSegments208.append_exact join26_04 join26_05 rfl rfl rfl
#print axioms join26_06

theorem join26_07 : ChunkFacts (toRow data26.row) 1 4349 (toTotals ⟨1228998670866536, 7489711620510, 25502790733247, 1210985591753799, 8249288266⟩) :=
  CleanupSegments208.append_exact join26_06 piece0196 rfl rfl rfl
#print axioms join26_07

theorem fact26 : ChunkFacts (toRow data26.row) 1 data26.steps (toTotals data26.total) := join26_07
#print axioms fact26

theorem piece0197 : ChunkFacts (toRow data27.row) 1 512 (toTotals ⟨1207142959127023, 4052144341938, 17765882298768, 1193429221170193, 2967110591⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0197
#print axioms piece0197

theorem piece0198 : ChunkFacts (toRow data27.row) 513 512 (toTotals ⟨58125285064620, 1999073358546, 4217373236917, 55906985186249, 1777670533⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0198
#print axioms piece0198

theorem piece0199 : ChunkFacts (toRow data27.row) 1025 512 (toTotals ⟨12568777270780, 1016084338500, 1944794536520, 11640067072760, 1232290471⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0199
#print axioms piece0199

theorem piece0200 : ChunkFacts (toRow data27.row) 1537 512 (toTotals ⟨4503879270231, 622424234784, 1138567648864, 3987735856151, 961420985⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0200
#print axioms piece0200

theorem piece0201 : ChunkFacts (toRow data27.row) 2049 512 (toTotals ⟨1246015476597, 360274475451, 616110133641, 990179818407, 634344943⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0201
#print axioms piece0201

theorem piece0202 : ChunkFacts (toRow data27.row) 2561 512 (toTotals ⟨469073565989, 238054045020, 397490408820, 309637202189, 486733370⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0202
#print axioms piece0202

theorem piece0203 : ChunkFacts (toRow data27.row) 3073 512 (toTotals ⟨194042175799, 162283184349, 270972120159, 85353239989, 374678392⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0203
#print axioms piece0203

theorem piece0204 : ChunkFacts (toRow data27.row) 3585 512 (toTotals ⟨135015356364, 148638623232, 248189133312, 35464846284, 378533556⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0204
#print axioms piece0204

theorem piece0205 : ChunkFacts (toRow data27.row) 4097 512 (toTotals ⟨119270874174, 148638623232, 248189133312, 19720364094, 404324979⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0205
#print axioms piece0205

theorem piece0206 : ChunkFacts (toRow data27.row) 4609 142 (toTotals ⟨30763855233, 41223993162, 68833704942, 3154143453, 90856300⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0206
#print axioms piece0206

theorem join27_00 : ChunkFacts (toRow data27.row) 1 1024 (toTotals ⟨1265268244191643, 6051217700484, 21983255535685, 1249336206356442, 4744781124⟩) :=
  CleanupSegments208.append_exact piece0197 piece0198 rfl rfl rfl
#print axioms join27_00

theorem join27_01 : ChunkFacts (toRow data27.row) 1025 1024 (toTotals ⟨17072656541011, 1638508573284, 3083362185384, 15627802928911, 2193711456⟩) :=
  CleanupSegments208.append_exact piece0199 piece0200 rfl rfl rfl
#print axioms join27_01

theorem join27_02 : ChunkFacts (toRow data27.row) 2049 1024 (toTotals ⟨1715089042586, 598328520471, 1013600542461, 1299817020596, 1121078313⟩) :=
  CleanupSegments208.append_exact piece0201 piece0202 rfl rfl rfl
#print axioms join27_02

theorem join27_03 : ChunkFacts (toRow data27.row) 3073 1024 (toTotals ⟨329057532163, 310921807581, 519161253471, 120818086273, 753211948⟩) :=
  CleanupSegments208.append_exact piece0203 piece0204 rfl rfl rfl
#print axioms join27_03

theorem join27_04 : ChunkFacts (toRow data27.row) 4097 654 (toTotals ⟨150034729407, 189862616394, 317022838254, 22874507547, 495181279⟩) :=
  CleanupSegments208.append_exact piece0205 piece0206 rfl rfl rfl
#print axioms join27_04

theorem join27_05 : ChunkFacts (toRow data27.row) 1 2048 (toTotals ⟨1282340900732654, 7689726273768, 25066617721069, 1264964009285353, 6938492580⟩) :=
  CleanupSegments208.append_exact join27_00 join27_01 rfl rfl rfl
#print axioms join27_05

theorem join27_06 : ChunkFacts (toRow data27.row) 2049 2048 (toTotals ⟨2044146574749, 909250328052, 1532761795932, 1420635106869, 1874290261⟩) :=
  CleanupSegments208.append_exact join27_02 join27_03 rfl rfl rfl
#print axioms join27_06

theorem join27_07 : ChunkFacts (toRow data27.row) 1 4096 (toTotals ⟨1284385047307403, 8598976601820, 26599379517001, 1266384644392222, 8812782841⟩) :=
  CleanupSegments208.append_exact join27_05 join27_06 rfl rfl rfl
#print axioms join27_07

theorem join27_08 : ChunkFacts (toRow data27.row) 1 4750 (toTotals ⟨1284535082036810, 8788839218214, 26916402355255, 1266407518899769, 9307964120⟩) :=
  CleanupSegments208.append_exact join27_07 join27_04 rfl rfl rfl
#print axioms join27_08

theorem fact27 : ChunkFacts (toRow data27.row) 1 data27.steps (toTotals data27.total) := join27_08
#print axioms fact27

theorem piece0207 : ChunkFacts (toRow data28.row) 1 512 (toTotals ⟨1002524556359351, 1111950720052, 15398187996714, 988238319082689, 2236076516⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G12.checked0207
#print axioms piece0207

theorem piece0208 : ChunkFacts (toRow data28.row) 513 512 (toTotals ⟨29055703931077, 388719614649, 2419362963955, 27025060581771, 1068955246⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0208
#print axioms piece0208

theorem piece0209 : ChunkFacts (toRow data28.row) 1025 512 (toTotals ⟨4146135179594, 169045139758, 910260985230, 3404919334122, 607245340⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0209
#print axioms piece0209

theorem piece0210 : ChunkFacts (toRow data28.row) 1537 512 (toTotals ⟨644662454188, 73996720579, 367638103911, 351021070856, 308930059⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0210
#print axioms piece0210

theorem piece0211 : ChunkFacts (toRow data28.row) 2049 512 (toTotals ⟨224512950636, 53892348416, 241879605760, 36525693292, 239330197⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0211
#print axioms piece0211

theorem piece0212 : ChunkFacts (toRow data28.row) 2561 123 (toTotals ⟨47260065412, 12946794639, 58107795915, 2099064136, 54288579⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0212
#print axioms piece0212

theorem join28_00 : ChunkFacts (toRow data28.row) 1 1024 (toTotals ⟨1031580260290428, 1500670334701, 17817550960669, 1015263379664460, 3305031762⟩) :=
  CleanupSegments208.append_exact piece0207 piece0208 rfl rfl rfl
#print axioms join28_00

theorem join28_01 : ChunkFacts (toRow data28.row) 1025 1024 (toTotals ⟨4790797633782, 243041860337, 1277899089141, 3755940404978, 916175399⟩) :=
  CleanupSegments208.append_exact piece0209 piece0210 rfl rfl rfl
#print axioms join28_01

theorem join28_02 : ChunkFacts (toRow data28.row) 2049 635 (toTotals ⟨271773016048, 66839143055, 299987401675, 38624757428, 293618776⟩) :=
  CleanupSegments208.append_exact piece0211 piece0212 rfl rfl rfl
#print axioms join28_02

theorem join28_03 : ChunkFacts (toRow data28.row) 1 2048 (toTotals ⟨1036371057924210, 1743712195038, 19095450049810, 1019019320069438, 4221207161⟩) :=
  CleanupSegments208.append_exact join28_00 join28_01 rfl rfl rfl
#print axioms join28_03

theorem join28_04 : ChunkFacts (toRow data28.row) 1 2683 (toTotals ⟨1036642830940258, 1810551338093, 19395437451485, 1019057944826866, 4514825937⟩) :=
  CleanupSegments208.append_exact join28_03 join28_02 rfl rfl rfl
#print axioms join28_04

theorem fact28 : ChunkFacts (toRow data28.row) 1 data28.steps (toTotals data28.total) := join28_04
#print axioms fact28

theorem piece0213 : ChunkFacts (toRow data29.row) 1 512 (toTotals ⟨1042567481427564, 1661865405360, 15853601942032, 1028375744890892, 2418241031⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0213
#print axioms piece0213

theorem piece0214 : ChunkFacts (toRow data29.row) 513 512 (toTotals ⟨35180364633077, 645807943302, 2798433658647, 33027738917732, 1233579552⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0214
#print axioms piece0214

theorem piece0215 : ChunkFacts (toRow data29.row) 1025 512 (toTotals ⟨5497078998331, 280843508874, 1070411739857, 4707510767348, 724186534⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0215
#print axioms piece0215

theorem piece0216 : ChunkFacts (toRow data29.row) 1537 512 (toTotals ⟨1278865784772, 146807898000, 526655047854, 899018634918, 437178031⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0216
#print axioms piece0216

theorem piece0217 : ChunkFacts (toRow data29.row) 2049 512 (toTotals ⟨224512950636, 75165643776, 241879605760, 57798988652, 257028757⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0217
#print axioms piece0217

theorem piece0218 : ChunkFacts (toRow data29.row) 2561 440 (toTotals ⟨159795170870, 64595475120, 207865286200, 16525359790, 225347640⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0218
#print axioms piece0218

theorem join29_00 : ChunkFacts (toRow data29.row) 1 1024 (toTotals ⟨1077747846060641, 2307673348662, 18652035600679, 1061403483808624, 3651820583⟩) :=
  CleanupSegments208.append_exact piece0213 piece0214 rfl rfl rfl
#print axioms join29_00

theorem join29_01 : ChunkFacts (toRow data29.row) 1025 1024 (toTotals ⟨6775944783103, 427651406874, 1597066787711, 5606529402266, 1161364565⟩) :=
  CleanupSegments208.append_exact piece0215 piece0216 rfl rfl rfl
#print axioms join29_01

theorem join29_02 : ChunkFacts (toRow data29.row) 2049 952 (toTotals ⟨384308121506, 139761118896, 449744891960, 74324348442, 482376397⟩) :=
  CleanupSegments208.append_exact piece0217 piece0218 rfl rfl rfl
#print axioms join29_02

theorem join29_03 : ChunkFacts (toRow data29.row) 1 2048 (toTotals ⟨1084523790843744, 2735324755536, 20249102388390, 1067010013210890, 4813185148⟩) :=
  CleanupSegments208.append_exact join29_00 join29_01 rfl rfl rfl
#print axioms join29_03

theorem join29_04 : ChunkFacts (toRow data29.row) 1 3000 (toTotals ⟨1084908098965250, 2875085874432, 20698847280350, 1067084337559332, 5295561545⟩) :=
  CleanupSegments208.append_exact join29_03 join29_02 rfl rfl rfl
#print axioms join29_04

theorem fact29 : ChunkFacts (toRow data29.row) 1 data29.steps (toTotals data29.total) := join29_04
#print axioms fact29

theorem piece0219 : ChunkFacts (toRow data30.row) 1 512 (toTotals ⟨1077569354308292, 2162909680486, 16247979080572, 1063484284908206, 2598260029⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0219
#print axioms piece0219

theorem piece0220 : ChunkFacts (toRow data30.row) 513 512 (toTotals ⟨41788753945002, 915901235714, 3160497193555, 39544157987161, 1390917183⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0220
#print axioms piece0220

theorem piece0221 : ChunkFacts (toRow data30.row) 1025 512 (toTotals ⟨7362237602989, 411768454114, 1265616140469, 6508389916634, 854037116⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0221
#print axioms piece0221

theorem piece0222 : ChunkFacts (toRow data30.row) 1537 512 (toTotals ⟨2043917133138, 237662597040, 693325213698, 1588254516480, 582882067⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0222
#print axioms piece0222

theorem piece0223 : ChunkFacts (toRow data30.row) 2049 512 (toTotals ⟨316724684654, 106047931558, 278256030845, 144516585367, 300220627⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G13.checked0223
#print axioms piece0223

theorem piece0224 : ChunkFacts (toRow data30.row) 2561 512 (toTotals ⟨183707228898, 92184280064, 241879605760, 34011903202, 288095664⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0224
#print axioms piece0224

theorem piece0225 : ChunkFacts (toRow data30.row) 3073 241 (toTotals ⟨76181030193, 43391428702, 113853486305, 5718972590, 132750934⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0225
#print axioms piece0225

theorem join30_00 : ChunkFacts (toRow data30.row) 1 1024 (toTotals ⟨1119358108253294, 3078810916200, 19408476274127, 1103028442895367, 3989177212⟩) :=
  CleanupSegments208.append_exact piece0219 piece0220 rfl rfl rfl
#print axioms join30_00

theorem join30_01 : ChunkFacts (toRow data30.row) 1025 1024 (toTotals ⟨9406154736127, 649431051154, 1958941354167, 8096644433114, 1436919183⟩) :=
  CleanupSegments208.append_exact piece0221 piece0222 rfl rfl rfl
#print axioms join30_01

theorem join30_02 : ChunkFacts (toRow data30.row) 2049 1024 (toTotals ⟨500431913552, 198232211622, 520135636605, 178528488569, 588316291⟩) :=
  CleanupSegments208.append_exact piece0223 piece0224 rfl rfl rfl
#print axioms join30_02

theorem join30_03 : ChunkFacts (toRow data30.row) 1 2048 (toTotals ⟨1128764262989421, 3728241967354, 21367417628294, 1111125087328481, 5426096395⟩) :=
  CleanupSegments208.append_exact join30_00 join30_01 rfl rfl rfl
#print axioms join30_03

theorem join30_04 : ChunkFacts (toRow data30.row) 2049 1265 (toTotals ⟨576612943745, 241623640324, 633989122910, 184247461159, 721067225⟩) :=
  CleanupSegments208.append_exact join30_02 piece0225 rfl rfl rfl
#print axioms join30_04

theorem join30_05 : ChunkFacts (toRow data30.row) 1 3313 (toTotals ⟨1129340875933166, 3969865607678, 22001406751204, 1111309334789640, 6147163620⟩) :=
  CleanupSegments208.append_exact join30_03 join30_04 rfl rfl rfl
#print axioms join30_05

theorem fact30 : ChunkFacts (toRow data30.row) 1 data30.steps (toTotals data30.total) := join30_05
#print axioms fact30

theorem piece0226 : ChunkFacts (toRow data31.row) 1 512 (toTotals ⟨1098210252568187, 2561936324632, 16528124796065, 1084244064096754, 2725874753⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0226
#print axioms piece0226

theorem piece0227 : ChunkFacts (toRow data31.row) 513 512 (toTotals ⟨45420799716493, 1145101607312, 3392078019254, 43173823304551, 1505123118⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0227
#print axioms piece0227

theorem piece0228 : ChunkFacts (toRow data31.row) 1025 512 (toTotals ⟨8584034620074, 533702109794, 1417641252081, 7700095477787, 955718734⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0228
#print axioms piece0228

theorem piece0229 : ChunkFacts (toRow data31.row) 1537 512 (toTotals ⟨2669057903631, 322007890300, 815020890346, 2176044903585, 698079751⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0229
#print axioms piece0229

theorem piece0230 : ChunkFacts (toRow data31.row) 2049 512 (toTotals ⟨459035516194, 148539123590, 337781090075, 269793549709, 367231997⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0230
#print axioms piece0230

theorem piece0231 : ChunkFacts (toRow data31.row) 2561 512 (toTotals ⟨183707228898, 106366477312, 241879605760, 48194100450, 302516144⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0231
#print axioms piece0231

theorem piece0232 : ChunkFacts (toRow data31.row) 3073 512 (toTotals ⟨155545650970, 106366477312, 241879605760, 20032522522, 322025967⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0232
#print axioms piece0232

theorem piece0233 : ChunkFacts (toRow data31.row) 3585 44 (toTotals ⟨12322223653, 9140869144, 20786528620, 676564177, 17565015⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0233
#print axioms piece0233

theorem join31_00 : ChunkFacts (toRow data31.row) 1 1024 (toTotals ⟨1143631052284680, 3707037931944, 19920202815319, 1127417887401305, 4230997871⟩) :=
  CleanupSegments208.append_exact piece0226 piece0227 rfl rfl rfl
#print axioms join31_00

theorem join31_01 : ChunkFacts (toRow data31.row) 1025 1024 (toTotals ⟨11253092523705, 855710000094, 2232662142427, 9876140381372, 1653798485⟩) :=
  CleanupSegments208.append_exact piece0228 piece0229 rfl rfl rfl
#print axioms join31_01

theorem join31_02 : ChunkFacts (toRow data31.row) 2049 1024 (toTotals ⟨642742745092, 254905600902, 579660695835, 317987650159, 669748141⟩) :=
  CleanupSegments208.append_exact piece0230 piece0231 rfl rfl rfl
#print axioms join31_02

theorem join31_03 : ChunkFacts (toRow data31.row) 3073 556 (toTotals ⟨167867874623, 115507346456, 262666134380, 20709086699, 339590982⟩) :=
  CleanupSegments208.append_exact piece0232 piece0233 rfl rfl rfl
#print axioms join31_03

theorem join31_04 : ChunkFacts (toRow data31.row) 1 2048 (toTotals ⟨1154884144808385, 4562747932038, 22152864957746, 1137294027782677, 5884796356⟩) :=
  CleanupSegments208.append_exact join31_00 join31_01 rfl rfl rfl
#print axioms join31_04

theorem join31_05 : ChunkFacts (toRow data31.row) 2049 1580 (toTotals ⟨810610619715, 370412947358, 842326830215, 338696736858, 1009339123⟩) :=
  CleanupSegments208.append_exact join31_02 join31_03 rfl rfl rfl
#print axioms join31_05

theorem join31_06 : ChunkFacts (toRow data31.row) 1 3628 (toTotals ⟨1155694755428100, 4933160879396, 22995191787961, 1137632724519535, 6894135479⟩) :=
  CleanupSegments208.append_exact join31_04 join31_05 rfl rfl rfl
#print axioms join31_06

theorem fact31 : ChunkFacts (toRow data31.row) 1 data31.steps (toTotals data31.total) := join31_06
#print axioms fact31

theorem piece0234 : ChunkFacts (toRow data32.row) 1 512 (toTotals ⟨1125804700866473, 3025253736021, 16828395650480, 1112001558952014, 2862444967⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0234
#print axioms piece0234

theorem piece0235 : ChunkFacts (toRow data32.row) 513 512 (toTotals ⟨50186195818041, 1421626745902, 3676664492934, 47931158071009, 1628922139⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0235
#print axioms piece0235

theorem piece0236 : ChunkFacts (toRow data32.row) 1025 512 (toTotals ⟨10213064062973, 686562370164, 1601979967272, 9297646465865, 1076825055⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0236
#print axioms piece0236

theorem piece0237 : ChunkFacts (toRow data32.row) 1537 512 (toTotals ⟨3427707694353, 429219204667, 957975516719, 2898951382301, 834345864⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0237
#print axioms piece0237

theorem piece0238 : ChunkFacts (toRow data32.row) 2049 512 (toTotals ⟨609577642078, 200835974537, 402975202565, 407438414050, 447698763⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0238
#print axioms piece0238

theorem piece0239 : ChunkFacts (toRow data32.row) 2561 512 (toTotals ⟨234138937462, 132791898756, 266445503220, 100485332998, 339360688⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G14.checked0239
#print axioms piece0239

theorem piece0240 : ChunkFacts (toRow data32.row) 3073 512 (toTotals ⟨155545650970, 120548674048, 241879605760, 34214719258, 339067887⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0240
#print axioms piece0240

theorem piece0241 : ChunkFacts (toRow data32.row) 3585 426 (toTotals ⟨113476930461, 100300263954, 201251390730, 12525803685, 284088876⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0241
#print axioms piece0241

theorem join32_00 : ChunkFacts (toRow data32.row) 1 1024 (toTotals ⟨1175990896684514, 4446880481923, 20505060143414, 1159932717023023, 4491367106⟩) :=
  CleanupSegments208.append_exact piece0234 piece0235 rfl rfl rfl
#print axioms join32_00

theorem join32_01 : ChunkFacts (toRow data32.row) 1025 1024 (toTotals ⟨13640771757326, 1115781574831, 2559955483991, 12196597848166, 1911170919⟩) :=
  CleanupSegments208.append_exact piece0236 piece0237 rfl rfl rfl
#print axioms join32_01

theorem join32_02 : ChunkFacts (toRow data32.row) 2049 1024 (toTotals ⟨843716579540, 333627873293, 669420705785, 507923747048, 787059451⟩) :=
  CleanupSegments208.append_exact piece0238 piece0239 rfl rfl rfl
#print axioms join32_02

theorem join32_03 : ChunkFacts (toRow data32.row) 3073 938 (toTotals ⟨269022581431, 220848938002, 443130996490, 46740522943, 623156763⟩) :=
  CleanupSegments208.append_exact piece0240 piece0241 rfl rfl rfl
#print axioms join32_03

theorem join32_04 : ChunkFacts (toRow data32.row) 1 2048 (toTotals ⟨1189631668441840, 5562662056754, 23065015627405, 1172129314871189, 6402538025⟩) :=
  CleanupSegments208.append_exact join32_00 join32_01 rfl rfl rfl
#print axioms join32_04

theorem join32_05 : ChunkFacts (toRow data32.row) 2049 1962 (toTotals ⟨1112739160971, 554476811295, 1112551702275, 554664269991, 1410216214⟩) :=
  CleanupSegments208.append_exact join32_02 join32_03 rfl rfl rfl
#print axioms join32_05

theorem join32_06 : ChunkFacts (toRow data32.row) 1 4010 (toTotals ⟨1190744407602811, 6117138868049, 24177567329680, 1172683979141180, 7812754239⟩) :=
  CleanupSegments208.append_exact join32_04 join32_05 rfl rfl rfl
#print axioms join32_06

theorem fact32 : ChunkFacts (toRow data32.row) 1 data32.steps (toTotals data32.total) := join32_06
#print axioms fact32

theorem piece0242 : ChunkFacts (toRow data33.row) 1 512 (toTotals ⟨1161243040271479, 3461456014344, 17204348365907, 1147500147919916, 2986666866⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0242
#print axioms piece0242

theorem piece0243 : ChunkFacts (toRow data33.row) 513 512 (toTotals ⟨53763380798062, 1659242255592, 3895584433013, 51527038620641, 1741264581⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0243
#print axioms piece0243

theorem piece0244 : ChunkFacts (toRow data33.row) 1025 512 (toTotals ⟨11453532415821, 831553175136, 1766193543386, 10518892047571, 1185194069⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0244
#print axioms piece0244

theorem piece0245 : ChunkFacts (toRow data33.row) 1537 512 (toTotals ⟨3943795601069, 506196403080, 1025059313629, 3424932690520, 913071672⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0245
#print axioms piece0245

theorem piece0246 : ChunkFacts (toRow data33.row) 2049 512 (toTotals ⟨968683592259, 274350722280, 513899678019, 729134636520, 556720416⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0246
#print axioms piece0246

theorem piece0247 : ChunkFacts (toRow data33.row) 2561 512 (toTotals ⟨357167111010, 179551599464, 329277510185, 207441200289, 419284893⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0247
#print axioms piece0247

theorem piece0248 : ChunkFacts (toRow data33.row) 3073 512 (toTotals ⟨155545650970, 131894431744, 241879605760, 45560476954, 352701423⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0248
#print axioms piece0248

theorem piece0249 : ChunkFacts (toRow data33.row) 3585 512 (toTotals ⟨134932175820, 131894431744, 241879605760, 24947001804, 376982478⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0249
#print axioms piece0249

theorem piece0250 : ChunkFacts (toRow data33.row) 4097 283 (toTotals ⟨67585510822, 72902586296, 133695172715, 6792924403, 199149009⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0250
#print axioms piece0250

theorem join33_00 : ChunkFacts (toRow data33.row) 1 1024 (toTotals ⟨1215006421069541, 5120698269936, 21099932798920, 1199027186540557, 4727931447⟩) :=
  CleanupSegments208.append_exact piece0242 piece0243 rfl rfl rfl
#print axioms join33_00

theorem join33_01 : ChunkFacts (toRow data33.row) 1025 1024 (toTotals ⟨15397328016890, 1337749578216, 2791252857015, 13943824738091, 2098265741⟩) :=
  CleanupSegments208.append_exact piece0244 piece0245 rfl rfl rfl
#print axioms join33_01

theorem join33_02 : ChunkFacts (toRow data33.row) 2049 1024 (toTotals ⟨1325850703269, 453902321744, 843177188204, 936575836809, 976005309⟩) :=
  CleanupSegments208.append_exact piece0246 piece0247 rfl rfl rfl
#print axioms join33_02

theorem join33_03 : ChunkFacts (toRow data33.row) 3073 1024 (toTotals ⟨290477826790, 263788863488, 483759211520, 70507478758, 729683901⟩) :=
  CleanupSegments208.append_exact piece0248 piece0249 rfl rfl rfl
#print axioms join33_03

theorem join33_04 : ChunkFacts (toRow data33.row) 1 2048 (toTotals ⟨1230403749086431, 6458447848152, 23891185655935, 1212971011278648, 6826197188⟩) :=
  CleanupSegments208.append_exact join33_00 join33_01 rfl rfl rfl
#print axioms join33_04

theorem join33_05 : ChunkFacts (toRow data33.row) 2049 2048 (toTotals ⟨1616328530059, 717691185232, 1326936399724, 1007083315567, 1705689210⟩) :=
  CleanupSegments208.append_exact join33_02 join33_03 rfl rfl rfl
#print axioms join33_05

theorem join33_06 : ChunkFacts (toRow data33.row) 1 4096 (toTotals ⟨1232020077616490, 7176139033384, 25218122055659, 1213978094594215, 8531886398⟩) :=
  CleanupSegments208.append_exact join33_04 join33_05 rfl rfl rfl
#print axioms join33_06

theorem join33_07 : ChunkFacts (toRow data33.row) 1 4379 (toTotals ⟨1232087663127312, 7249041619680, 25351817228374, 1213984887518618, 8731035407⟩) :=
  CleanupSegments208.append_exact join33_06 piece0250 rfl rfl rfl
#print axioms join33_07

theorem fact33 : ChunkFacts (toRow data33.row) 1 data33.steps (toTotals data33.total) := join33_07
#print axioms fact33

theorem piece0251 : ChunkFacts (toRow data34.row) 1 512 (toTotals ⟨1209298784374607, 3940224259496, 17654660163400, 1195584348470703, 3138693651⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0251
#print axioms piece0251

theorem piece0252 : ChunkFacts (toRow data34.row) 513 512 (toTotals ⟨59283403355873, 1957802426012, 4200485014206, 57040720767679, 1883739414⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0252
#print axioms piece0252

theorem piece0253 : ChunkFacts (toRow data34.row) 1025 512 (toTotals ⟨13072185980363, 1004919450448, 1958846870022, 12118258560789, 1313775217⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0253
#print axioms piece0253

theorem piece0254 : ChunkFacts (toRow data34.row) 1537 512 (toTotals ⟨4563729955000, 608491036950, 1124267745679, 4047953246271, 1011844637⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0254
#print axioms piece0254

theorem piece0255 : ChunkFacts (toRow data34.row) 2049 512 (toTotals ⟨1417727158032, 369570878074, 648445208723, 1138852827383, 700824948⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G15.checked0255
#print axioms piece0255

theorem piece0256 : ChunkFacts (toRow data34.row) 2561 512 (toTotals ⟨475684776504, 231926009026, 391637096045, 315973689485, 511183391⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0256
#print axioms piece0256

theorem piece0257 : ChunkFacts (toRow data34.row) 3073 512 (toTotals ⟨207270929826, 161145212544, 272114556480, 96301585890, 399252251⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0257
#print axioms piece0257

theorem piece0258 : ChunkFacts (toRow data34.row) 3585 512 (toTotals ⟨134932175820, 143240188928, 241879605760, 36292758988, 392713166⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0258
#print axioms piece0258

theorem piece0259 : ChunkFacts (toRow data34.row) 4097 512 (toTotals ⟨119187693630, 143240188928, 241879605760, 20548276798, 419016652⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0259
#print axioms piece0259

theorem piece0260 : ChunkFacts (toRow data34.row) 4609 214 (toTotals ⟨45982812938, 59869922716, 101098116470, 4754619184, 157233592⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0260
#print axioms piece0260

theorem join34_00 : ChunkFacts (toRow data34.row) 1 1024 (toTotals ⟨1268582187730480, 5898026685508, 21855145177606, 1252625069238382, 5022433065⟩) :=
  CleanupSegments208.append_exact piece0251 piece0252 rfl rfl rfl
#print axioms join34_00

theorem join34_01 : ChunkFacts (toRow data34.row) 1025 1024 (toTotals ⟨17635915935363, 1613410487398, 3083114615701, 16166211807060, 2325619854⟩) :=
  CleanupSegments208.append_exact piece0253 piece0254 rfl rfl rfl
#print axioms join34_01

theorem join34_02 : ChunkFacts (toRow data34.row) 2049 1024 (toTotals ⟨1893411934536, 601496887100, 1040082304768, 1454826516868, 1212008339⟩) :=
  CleanupSegments208.append_exact piece0255 piece0256 rfl rfl rfl
#print axioms join34_02

theorem join34_03 : ChunkFacts (toRow data34.row) 3073 1024 (toTotals ⟨342203105646, 304385401472, 513994162240, 132594344878, 791965417⟩) :=
  CleanupSegments208.append_exact piece0257 piece0258 rfl rfl rfl
#print axioms join34_03

theorem join34_04 : ChunkFacts (toRow data34.row) 4097 726 (toTotals ⟨165170506568, 203110111644, 342977722230, 25302895982, 576250244⟩) :=
  CleanupSegments208.append_exact piece0259 piece0260 rfl rfl rfl
#print axioms join34_04

theorem join34_05 : ChunkFacts (toRow data34.row) 1 2048 (toTotals ⟨1286218103665843, 7511437172906, 24938259793307, 1268791281045442, 7348052919⟩) :=
  CleanupSegments208.append_exact join34_00 join34_01 rfl rfl rfl
#print axioms join34_05

theorem join34_06 : ChunkFacts (toRow data34.row) 2049 2048 (toTotals ⟨2235615040182, 905882288572, 1554076467008, 1587420861746, 2003973756⟩) :=
  CleanupSegments208.append_exact join34_02 join34_03 rfl rfl rfl
#print axioms join34_06

theorem join34_07 : ChunkFacts (toRow data34.row) 1 4096 (toTotals ⟨1288453718706025, 8417319461478, 26492336260315, 1270378701907188, 9352026675⟩) :=
  CleanupSegments208.append_exact join34_05 join34_06 rfl rfl rfl
#print axioms join34_07

theorem join34_08 : ChunkFacts (toRow data34.row) 1 4822 (toTotals ⟨1288618889212593, 8620429573122, 26835313982545, 1270404004803170, 9928276919⟩) :=
  CleanupSegments208.append_exact join34_07 join34_04 rfl rfl rfl
#print axioms join34_08

theorem fact34 : ChunkFacts (toRow data34.row) 1 data34.steps (toTotals data34.total) := join34_08
#print axioms fact34

theorem piece0261 : ChunkFacts (toRow data35.row) 1 512 (toTotals ⟨998663063789593, 1029156179744, 15202557495323, 984489662474014, 2363419681⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0261
#print axioms piece0261

theorem piece0262 : ChunkFacts (toRow data35.row) 513 512 (toTotals ⟨29924875297547, 367264452896, 2421266429394, 27870873321049, 1138406332⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0262
#print axioms piece0262

theorem piece0263 : ChunkFacts (toRow data35.row) 1025 512 (toTotals ⟨4341521732680, 160034854144, 915891345928, 3585665240896, 649249288⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0263
#print axioms piece0263

theorem piece0264 : ChunkFacts (toRow data35.row) 1537 512 (toTotals ⟨745990969103, 73705372752, 391579409204, 428116932651, 346513834⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0264
#print axioms piece0264

theorem piece0265 : ChunkFacts (toRow data35.row) 2049 512 (toTotals ⟨224438502764, 49719566336, 234922708992, 39235360108, 248390147⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0265
#print axioms piece0265

theorem piece0266 : ChunkFacts (toRow data35.row) 2561 168 (toTotals ⟨63990380293, 16314232704, 77084013888, 3220599109, 78719561⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0266
#print axioms piece0266

theorem join35_00 : ChunkFacts (toRow data35.row) 1 1024 (toTotals ⟨1028587939087140, 1396420632640, 17623823924717, 1012360535795063, 3501826013⟩) :=
  CleanupSegments208.append_exact piece0261 piece0262 rfl rfl rfl
#print axioms join35_00

theorem join35_01 : ChunkFacts (toRow data35.row) 1025 1024 (toTotals ⟨5087512701783, 233740226896, 1307470755132, 4013782173547, 995763122⟩) :=
  CleanupSegments208.append_exact piece0263 piece0264 rfl rfl rfl
#print axioms join35_01

theorem join35_02 : ChunkFacts (toRow data35.row) 2049 680 (toTotals ⟨288428883057, 66033799040, 312006722880, 42455959217, 327109708⟩) :=
  CleanupSegments208.append_exact piece0265 piece0266 rfl rfl rfl
#print axioms join35_02

theorem join35_03 : ChunkFacts (toRow data35.row) 1 2048 (toTotals ⟨1033675451788923, 1630160859536, 18931294679849, 1016374317968610, 4497589135⟩) :=
  CleanupSegments208.append_exact join35_00 join35_01 rfl rfl rfl
#print axioms join35_03

theorem join35_04 : ChunkFacts (toRow data35.row) 1 2728 (toTotals ⟨1033963880671980, 1696194658576, 19243301402729, 1016416773927827, 4824698843⟩) :=
  CleanupSegments208.append_exact join35_03 join35_02 rfl rfl rfl
#print axioms join35_04

theorem fact35 : ChunkFacts (toRow data35.row) 1 data35.steps (toTotals data35.total) := join35_04
#print axioms fact35

theorem piece0267 : ChunkFacts (toRow data36.row) 1 512 (toTotals ⟨1046299908537429, 1594380304110, 15714044539345, 1032180244302194, 2556061449⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0267
#print axioms piece0267

theorem piece0268 : ChunkFacts (toRow data36.row) 513 512 (toTotals ⟨36278479256064, 626512728120, 2800053363514, 34104938620670, 1311405196⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0268
#print axioms piece0268

theorem piece0269 : ChunkFacts (toRow data36.row) 1025 512 (toTotals ⟨5824489170582, 274447072065, 1082345635878, 5016590606769, 775375475⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0269
#print axioms piece0269

theorem piece0270 : ChunkFacts (toRow data36.row) 1537 512 (toTotals ⟨1427533936362, 149394908970, 554133615074, 1022795230258, 488269813⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0270
#print axioms piece0270

theorem piece0271 : ChunkFacts (toRow data36.row) 2049 512 (toTotals ⟨224438502764, 71219919360, 234922708992, 60735713132, 267268611⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G16.checked0271
#print axioms piece0271

theorem piece0272 : ChunkFacts (toRow data36.row) 2561 501 (toTotals ⟨180017340423, 69689803905, 229875541416, 19831602912, 268163165⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0272
#print axioms piece0272

theorem join36_00 : ChunkFacts (toRow data36.row) 1 1024 (toTotals ⟨1082578387793493, 2220893032230, 18514097902859, 1066285182922864, 3867466645⟩) :=
  CleanupSegments208.append_exact piece0267 piece0268 rfl rfl rfl
#print axioms join36_00

theorem join36_01 : ChunkFacts (toRow data36.row) 1025 1024 (toTotals ⟨7252023106944, 423841981035, 1636479250952, 6039385837027, 1263645288⟩) :=
  CleanupSegments208.append_exact piece0269 piece0270 rfl rfl rfl
#print axioms join36_01

theorem join36_02 : ChunkFacts (toRow data36.row) 2049 1013 (toTotals ⟨404455843187, 140909723265, 464798250408, 80567316044, 535431776⟩) :=
  CleanupSegments208.append_exact piece0271 piece0272 rfl rfl rfl
#print axioms join36_02

theorem join36_03 : ChunkFacts (toRow data36.row) 1 2048 (toTotals ⟨1089830410900437, 2644735013265, 20150577153811, 1072324568759891, 5131111933⟩) :=
  CleanupSegments208.append_exact join36_00 join36_01 rfl rfl rfl
#print axioms join36_03

theorem join36_04 : ChunkFacts (toRow data36.row) 1 3061 (toTotals ⟨1090234866743624, 2785644736530, 20615375404219, 1072405136075935, 5666543709⟩) :=
  CleanupSegments208.append_exact join36_03 join36_02 rfl rfl rfl
#print axioms join36_04

theorem fact36 : ChunkFacts (toRow data36.row) 1 data36.steps (toTotals data36.total) := join36_04
#print axioms fact36

theorem piece0273 : ChunkFacts (toRow data37.row) 1 512 (toTotals ⟨1079778405691008, 2070695012694, 16080654932331, 1065768445771371, 2744870989⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0273
#print axioms piece0273

theorem piece0274 : ChunkFacts (toRow data37.row) 513 512 (toTotals ⟨42658010723547, 885905355159, 3149993640282, 40393922438424, 1474670186⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0274
#print axioms piece0274

theorem piece0275 : ChunkFacts (toRow data37.row) 1025 512 (toTotals ⟨7737851233902, 403630285058, 1282242398322, 6859239120638, 914000535⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0275
#print axioms piece0275

theorem piece0276 : ChunkFacts (toRow data37.row) 1537 512 (toTotals ⟨2261130507145, 238493296074, 717904726968, 1781719076251, 641113304⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0276
#print axioms piece0276

theorem piece0277 : ChunkFacts (toRow data37.row) 2049 512 (toTotals ⟨338207948436, 103722406304, 278970716928, 162959637812, 319429743⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0277
#print axioms piece0277

theorem piece0278 : ChunkFacts (toRow data37.row) 2561 512 (toTotals ⟨183632781026, 87345184256, 234922708992, 36055256290, 298340868⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0278
#print axioms piece0278

theorem piece0279 : ChunkFacts (toRow data37.row) 3073 297 (toTotals ⟨93052295189, 50667030711, 136273524552, 7445801348, 172352109⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0279
#print axioms piece0279

theorem join37_00 : ChunkFacts (toRow data37.row) 1 1024 (toTotals ⟨1122436416414555, 2956600367853, 19230648572613, 1106162368209795, 4219541175⟩) :=
  CleanupSegments208.append_exact piece0273 piece0274 rfl rfl rfl
#print axioms join37_00

theorem join37_01 : ChunkFacts (toRow data37.row) 1025 1024 (toTotals ⟨9998981741047, 642123581132, 2000147125290, 8640958196889, 1555113839⟩) :=
  CleanupSegments208.append_exact piece0275 piece0276 rfl rfl rfl
#print axioms join37_01

theorem join37_02 : ChunkFacts (toRow data37.row) 2049 1024 (toTotals ⟨521840729462, 191067590560, 513893425920, 199014894102, 617770611⟩) :=
  CleanupSegments208.append_exact piece0277 piece0278 rfl rfl rfl
#print axioms join37_02

theorem join37_03 : ChunkFacts (toRow data37.row) 1 2048 (toTotals ⟨1132435398155602, 3598723948985, 21230795697903, 1114803326406684, 5774655014⟩) :=
  CleanupSegments208.append_exact join37_00 join37_01 rfl rfl rfl
#print axioms join37_03

theorem join37_04 : ChunkFacts (toRow data37.row) 2049 1321 (toTotals ⟨614893024651, 241734621271, 650166950472, 206460695450, 790122720⟩) :=
  CleanupSegments208.append_exact join37_02 piece0279 rfl rfl rfl
#print axioms join37_04

theorem join37_05 : ChunkFacts (toRow data37.row) 1 3369 (toTotals ⟨1133050291180253, 3840458570256, 21880962648375, 1115009787102134, 6564777734⟩) :=
  CleanupSegments208.append_exact join37_03 join37_04 rfl rfl rfl
#print axioms join37_05

theorem fact37 : ChunkFacts (toRow data37.row) 1 data37.steps (toTotals data37.total) := join37_05
#print axioms fact37

theorem piece0280 : ChunkFacts (toRow data38.row) 1 512 (toTotals ⟨1100292246185333, 2525325649616, 16363810010479, 1086453761824470, 2902064254⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0280
#print axioms piece0280

theorem piece0281 : ChunkFacts (toRow data38.row) 513 512 (toTotals ⟨47096983432340, 1150300383932, 3417124460090, 44830159356182, 1616305496⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0281
#print axioms piece0281

theorem piece0282 : ChunkFacts (toRow data38.row) 1025 512 (toTotals ⟨9401262202357, 551101396167, 1471920142610, 8480443455914, 1046191010⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0282
#print axioms piece0282

theorem piece0283 : ChunkFacts (toRow data38.row) 1537 512 (toTotals ⟨2980910228480, 339916592722, 864596762412, 2456230058790, 789149217⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0283
#print axioms piece0283

theorem piece0284 : ChunkFacts (toRow data38.row) 2049 512 (toTotals ⟨511844533171, 154599401565, 351007563240, 315436371496, 406554541⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0284
#print axioms piece0284

theorem piece0285 : ChunkFacts (toRow data38.row) 2561 512 (toTotals ⟨183632781026, 103470449152, 234922708992, 52180521186, 315645444⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0285
#print axioms piece0285

theorem piece0286 : ChunkFacts (toRow data38.row) 3073 512 (toTotals ⟨155471203098, 103470449152, 234922708992, 24018943258, 335699053⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0286
#print axioms piece0286

theorem piece0287 : ChunkFacts (toRow data38.row) 3585 163 (toTotals ⟨44897758956, 32940787523, 74789846808, 3048699671, 99345194⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G17.checked0287
#print axioms piece0287

theorem join38_00 : ChunkFacts (toRow data38.row) 1 1024 (toTotals ⟨1147389229617673, 3675626033548, 19780934470569, 1131283921180652, 4518369750⟩) :=
  CleanupSegments208.append_exact piece0280 piece0281 rfl rfl rfl
#print axioms join38_00

theorem join38_01 : ChunkFacts (toRow data38.row) 1025 1024 (toTotals ⟨12382172430837, 891017988889, 2336516905022, 10936673514704, 1835340227⟩) :=
  CleanupSegments208.append_exact piece0282 piece0283 rfl rfl rfl
#print axioms join38_01

theorem join38_02 : ChunkFacts (toRow data38.row) 2049 1024 (toTotals ⟨695477314197, 258069850717, 585930272232, 367616892682, 722199985⟩) :=
  CleanupSegments208.append_exact piece0284 piece0285 rfl rfl rfl
#print axioms join38_02

theorem join38_03 : ChunkFacts (toRow data38.row) 3073 675 (toTotals ⟨200368962054, 136411236675, 309712555800, 27067642929, 435044247⟩) :=
  CleanupSegments208.append_exact piece0286 piece0287 rfl rfl rfl
#print axioms join38_03

theorem join38_04 : ChunkFacts (toRow data38.row) 1 2048 (toTotals ⟨1159771402048510, 4566644022437, 22117451375591, 1142220594695356, 6353709977⟩) :=
  CleanupSegments208.append_exact join38_00 join38_01 rfl rfl rfl
#print axioms join38_04

theorem join38_05 : ChunkFacts (toRow data38.row) 2049 1699 (toTotals ⟨895846276251, 394481087392, 895642828032, 394684535611, 1157244232⟩) :=
  CleanupSegments208.append_exact join38_02 join38_03 rfl rfl rfl
#print axioms join38_05

theorem join38_06 : ChunkFacts (toRow data38.row) 1 3747 (toTotals ⟨1160667248324761, 4961125109829, 23013094203623, 1142615279230967, 7510954209⟩) :=
  CleanupSegments208.append_exact join38_04 join38_05 rfl rfl rfl
#print axioms join38_06

theorem fact38 : ChunkFacts (toRow data38.row) 1 data38.steps (toTotals data38.total) := join38_06
#print axioms fact38

theorem piece0288 : ChunkFacts (toRow data39.row) 1 512 (toTotals ⟨1124535398135767, 2964033107889, 16631883433755, 1110867547809901, 3039594998⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0288
#print axioms piece0288

theorem piece0289 : ChunkFacts (toRow data39.row) 513 512 (toTotals ⟨51910576343477, 1417511557952, 3684197925732, 49643889975697, 1740806141⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0289
#print axioms piece0289

theorem piece0290 : ChunkFacts (toRow data39.row) 1025 512 (toTotals ⟨10827576452521, 698937319409, 1643995141884, 9882518630046, 1166919979⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0290
#print axioms piece0290

theorem piece0291 : ChunkFacts (toRow data39.row) 1537 512 (toTotals ⟨3630914822831, 430642203334, 958562853616, 3102994172549, 896829104⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0291
#print axioms piece0291

theorem piece0292 : ChunkFacts (toRow data39.row) 2049 512 (toTotals ⟨797659252332, 217604464357, 448554549988, 566709166701, 513221668⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0292
#print axioms piece0292

theorem piece0293 : ChunkFacts (toRow data39.row) 2561 512 (toTotals ⟨272500587240, 138143442745, 277594216680, 133049813305, 374187744⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0293
#print axioms piece0293

theorem piece0294 : ChunkFacts (toRow data39.row) 3073 512 (toTotals ⟨155471203098, 116908169728, 234922708992, 37456663834, 352740973⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0294
#print axioms piece0294

theorem piece0295 : ChunkFacts (toRow data39.row) 3585 512 (toTotals ⟨134857727948, 116908169728, 234922708992, 16843188684, 375236178⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0295
#print axioms piece0295

theorem piece0296 : ChunkFacts (toRow data39.row) 4097 38 (toTotals ⟨9333184647, 8676778222, 17435669808, 574293061, 12679992⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0296
#print axioms piece0296

theorem join39_00 : ChunkFacts (toRow data39.row) 1 1024 (toTotals ⟨1176445974479244, 4381544665841, 20316081359487, 1160511437785598, 4780401139⟩) :=
  CleanupSegments208.append_exact piece0288 piece0289 rfl rfl rfl
#print axioms join39_00

theorem join39_01 : ChunkFacts (toRow data39.row) 1025 1024 (toTotals ⟨14458491275352, 1129579522743, 2602557995500, 12985512802595, 2063749083⟩) :=
  CleanupSegments208.append_exact piece0290 piece0291 rfl rfl rfl
#print axioms join39_01

theorem join39_02 : ChunkFacts (toRow data39.row) 2049 1024 (toTotals ⟨1070159839572, 355747907102, 726148766668, 699758980006, 887409412⟩) :=
  CleanupSegments208.append_exact piece0292 piece0293 rfl rfl rfl
#print axioms join39_02

theorem join39_03 : ChunkFacts (toRow data39.row) 3073 1024 (toTotals ⟨290328931046, 233816339456, 469845417984, 54299852518, 727977151⟩) :=
  CleanupSegments208.append_exact piece0294 piece0295 rfl rfl rfl
#print axioms join39_03

theorem join39_04 : ChunkFacts (toRow data39.row) 1 2048 (toTotals ⟨1190904465754596, 5511124188584, 22918639354987, 1173496950588193, 6844150222⟩) :=
  CleanupSegments208.append_exact join39_00 join39_01 rfl rfl rfl
#print axioms join39_04

theorem join39_05 : ChunkFacts (toRow data39.row) 2049 2048 (toTotals ⟨1360488770618, 589564246558, 1195994184652, 754058832524, 1615386563⟩) :=
  CleanupSegments208.append_exact join39_02 join39_03 rfl rfl rfl
#print axioms join39_05

theorem join39_06 : ChunkFacts (toRow data39.row) 1 4096 (toTotals ⟨1192264954525214, 6100688435142, 24114633539639, 1174251009420717, 8459536785⟩) :=
  CleanupSegments208.append_exact join39_04 join39_05 rfl rfl rfl
#print axioms join39_06

theorem join39_07 : ChunkFacts (toRow data39.row) 1 4134 (toTotals ⟨1192274287709861, 6109365213364, 24132069209447, 1174251583713778, 8472216777⟩) :=
  CleanupSegments208.append_exact join39_06 piece0296 rfl rfl rfl
#print axioms join39_07

theorem fact39 : ChunkFacts (toRow data39.row) 1 data39.steps (toTotals data39.total) := join39_07
#print axioms fact39

theorem piece0297 : ChunkFacts (toRow data40.row) 1 512 (toTotals ⟨1159349774440262, 3383943499404, 16997793108211, 1145735924831455, 3172617447⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0297
#print axioms piece0297

theorem piece0298 : ChunkFacts (toRow data40.row) 513 512 (toTotals ⟨55690538331784, 1654571843652, 3914978665618, 53430131509818, 1863852921⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0298
#print axioms piece0298

theorem piece0299 : ChunkFacts (toRow data40.row) 1025 512 (toTotals ⟨12220798381991, 844739211316, 1812479270942, 11253058322365, 1285256984⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0299
#print axioms piece0299

theorem piece0300 : ChunkFacts (toRow data40.row) 1537 512 (toTotals ⟨4084473089302, 502156071898, 1017293530864, 3569335630336, 968139137⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0300
#print axioms piece0300

theorem piece0301 : ChunkFacts (toRow data40.row) 2049 512 (toTotals ⟨1237986542843, 298201917572, 572611634806, 963576825609, 646446710⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0301
#print axioms piece0301

theorem piece0302 : ChunkFacts (toRow data40.row) 2561 512 (toTotals ⟨403411760825, 186999530250, 344125062000, 246286229075, 464642766⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0302
#print axioms piece0302

theorem piece0303 : ChunkFacts (toRow data40.row) 3073 512 (toTotals ⟨155471203098, 127658345984, 234922708992, 48206840090, 366374509⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G18.checked0303
#print axioms piece0303

theorem piece0304 : ChunkFacts (toRow data40.row) 3585 512 (toTotals ⟨134857727948, 127658345984, 234922708992, 27593364940, 391146450⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0304
#print axioms piece0304

theorem piece0305 : ChunkFacts (toRow data40.row) 4097 409 (toTotals ⟨96239364871, 101977077163, 187662867144, 10553574890, 309769498⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0305
#print axioms piece0305

theorem join40_00 : ChunkFacts (toRow data40.row) 1 1024 (toTotals ⟨1215040312772046, 5038515343056, 20912771773829, 1199166056341273, 5036470368⟩) :=
  CleanupSegments208.append_exact piece0297 piece0298 rfl rfl rfl
#print axioms join40_00

theorem join40_01 : ChunkFacts (toRow data40.row) 1025 1024 (toTotals ⟨16305271471293, 1346895283214, 2829772801806, 14822393952701, 2253396121⟩) :=
  CleanupSegments208.append_exact piece0299 piece0300 rfl rfl rfl
#print axioms join40_01

theorem join40_02 : ChunkFacts (toRow data40.row) 2049 1024 (toTotals ⟨1641398303668, 485201447822, 916736696806, 1209863054684, 1111089476⟩) :=
  CleanupSegments208.append_exact piece0301 piece0302 rfl rfl rfl
#print axioms join40_02

theorem join40_03 : ChunkFacts (toRow data40.row) 3073 1024 (toTotals ⟨290328931046, 255316691968, 469845417984, 75800205030, 757520959⟩) :=
  CleanupSegments208.append_exact piece0303 piece0304 rfl rfl rfl
#print axioms join40_03

theorem join40_04 : ChunkFacts (toRow data40.row) 1 2048 (toTotals ⟨1231345584243339, 6385410626270, 23742544575635, 1213988450293974, 7289866489⟩) :=
  CleanupSegments208.append_exact join40_00 join40_01 rfl rfl rfl
#print axioms join40_04

theorem join40_05 : ChunkFacts (toRow data40.row) 2049 2048 (toTotals ⟨1931727234714, 740518139790, 1386582114790, 1285663259714, 1868610435⟩) :=
  CleanupSegments208.append_exact join40_02 join40_03 rfl rfl rfl
#print axioms join40_05

theorem join40_06 : ChunkFacts (toRow data40.row) 1 4096 (toTotals ⟨1233277311478053, 7125928766060, 25129126690425, 1215274113553688, 9158476924⟩) :=
  CleanupSegments208.append_exact join40_04 join40_05 rfl rfl rfl
#print axioms join40_06

theorem join40_07 : ChunkFacts (toRow data40.row) 1 4505 (toTotals ⟨1233373550842924, 7227905843223, 25316789557569, 1215284667128578, 9468246422⟩) :=
  CleanupSegments208.append_exact join40_06 piece0305 rfl rfl rfl
#print axioms join40_07

theorem fact40 : ChunkFacts (toRow data40.row) 1 data40.steps (toTotals data40.total) := join40_07
#print axioms fact40

theorem piece0306 : ChunkFacts (toRow data41.row) 1 512 (toTotals ⟨1207086505212700, 3800602078427, 17423902225637, 1193463205065490, 3315992066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0306
#print axioms piece0306

theorem piece0307 : ChunkFacts (toRow data41.row) 513 512 (toTotals ⟨60529556526894, 1908733733830, 4174404076430, 58263886184294, 1993531298⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0307
#print axioms piece0307

theorem piece0308 : ChunkFacts (toRow data41.row) 1025 512 (toTotals ⟨13860850929881, 998002715248, 1988297253674, 12870556391455, 1408930133⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0308
#print axioms piece0308

theorem piece0309 : ChunkFacts (toRow data41.row) 1537 512 (toTotals ⟨4632966915543, 595910419566, 1114566215056, 4114311120053, 1066032031⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0309
#print axioms piece0309

theorem piece0310 : ChunkFacts (toRow data41.row) 2049 512 (toTotals ⟨1659328808877, 380140519220, 686494587360, 1352974740737, 779297537⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0310
#print axioms piece0310

theorem piece0311 : ChunkFacts (toRow data41.row) 2561 512 (toTotals ⟨487084846806, 225407265622, 386337736272, 326154376156, 534938757⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0311
#print axioms piece0311

theorem piece0312 : ChunkFacts (toRow data41.row) 3073 512 (toTotals ⟨230821329880, 162228982146, 278053050096, 114997261930, 429869299⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0312
#print axioms piece0312

theorem piece0313 : ChunkFacts (toRow data41.row) 3585 512 (toTotals ⟨134857727948, 137064750592, 234922708992, 36999769548, 404910802⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0313
#print axioms piece0313

theorem piece0314 : ChunkFacts (toRow data41.row) 4097 512 (toTotals ⟨119113245758, 137064750592, 234922708992, 21255287358, 431527618⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0314
#print axioms piece0314

theorem piece0315 : ChunkFacts (toRow data41.row) 4609 282 (toTotals ⟨60132247731, 75492694662, 129391023312, 6233919081, 222482822⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0315
#print axioms piece0315

theorem join41_00 : ChunkFacts (toRow data41.row) 1 1024 (toTotals ⟨1267616061739594, 5709335812257, 21598306302067, 1251727091249784, 5309523364⟩) :=
  CleanupSegments208.append_exact piece0306 piece0307 rfl rfl rfl
#print axioms join41_00

theorem join41_01 : ChunkFacts (toRow data41.row) 1025 1024 (toTotals ⟨18493817845424, 1593913134814, 3102863468730, 16984867511508, 2474962164⟩) :=
  CleanupSegments208.append_exact piece0308 piece0309 rfl rfl rfl
#print axioms join41_01

theorem join41_02 : ChunkFacts (toRow data41.row) 2049 1024 (toTotals ⟨2146413655683, 605547784842, 1072832323632, 1679129116893, 1314236294⟩) :=
  CleanupSegments208.append_exact piece0310 piece0311 rfl rfl rfl
#print axioms join41_02

theorem join41_03 : ChunkFacts (toRow data41.row) 3073 1024 (toTotals ⟨365679057828, 299293732738, 512975759088, 151997031478, 834780101⟩) :=
  CleanupSegments208.append_exact piece0312 piece0313 rfl rfl rfl
#print axioms join41_03

theorem join41_04 : ChunkFacts (toRow data41.row) 4097 794 (toTotals ⟨179245493489, 212557445254, 364313732304, 27489206439, 654010440⟩) :=
  CleanupSegments208.append_exact piece0314 piece0315 rfl rfl rfl
#print axioms join41_04

theorem join41_05 : ChunkFacts (toRow data41.row) 1 2048 (toTotals ⟨1286109879585018, 7303248947071, 24701169770797, 1268711958761292, 7784485528⟩) :=
  CleanupSegments208.append_exact join41_00 join41_01 rfl rfl rfl
#print axioms join41_05

theorem join41_06 : ChunkFacts (toRow data41.row) 2049 2048 (toTotals ⟨2512092713511, 904841517580, 1585808082720, 1831126148371, 2149016395⟩) :=
  CleanupSegments208.append_exact join41_02 join41_03 rfl rfl rfl
#print axioms join41_06

theorem join41_07 : ChunkFacts (toRow data41.row) 1 4096 (toTotals ⟨1288621972298529, 8208090464651, 26286977853517, 1270543084909663, 9933501923⟩) :=
  CleanupSegments208.append_exact join41_05 join41_06 rfl rfl rfl
#print axioms join41_07

theorem join41_08 : ChunkFacts (toRow data41.row) 1 4890 (toTotals ⟨1288801217792018, 8420647909905, 26651291585821, 1270570574116102, 10587512363⟩) :=
  CleanupSegments208.append_exact join41_07 join41_04 rfl rfl rfl
#print axioms join41_08

theorem fact41 : ChunkFacts (toRow data41.row) 1 data41.steps (toTotals data41.total) := join41_08
#print axioms fact41

theorem piece0316 : ChunkFacts (toRow data42.row) 1 512 (toTotals ⟨1095212526029577, 1105686039495, 15190706495766, 1081127505573306, 2688143463⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0316
#print axioms piece0316

theorem piece0317 : ChunkFacts (toRow data42.row) 513 512 (toTotals ⟨36206809268924, 420828994193, 2537331807462, 34090306455655, 1341301179⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0317
#print axioms piece0317

theorem piece0318 : ChunkFacts (toRow data42.row) 1025 512 (toTotals ⟨5593589176526, 184729864244, 980177678888, 4798141361882, 784643903⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0318
#print axioms piece0318

theorem piece0319 : ChunkFacts (toRow data42.row) 1537 512 (toTotals ⟨1181268625271, 97252493325, 481272872678, 797248245918, 473871980⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G19.checked0319
#print axioms piece0319

theorem piece0320 : ChunkFacts (toRow data42.row) 2049 512 (toTotals ⟨224371481452, 51070027264, 219419615232, 56021893484, 272412034⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0320
#print axioms piece0320

theorem piece0321 : ChunkFacts (toRow data42.row) 2561 399 (toTotals ⟨145812749784, 39798712653, 170993020464, 14618441973, 214155221⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0321
#print axioms piece0321

theorem join42_00 : ChunkFacts (toRow data42.row) 1 1024 (toTotals ⟨1131419335298501, 1526515033688, 17728038303228, 1115217812028961, 4029444642⟩) :=
  CleanupSegments208.append_exact piece0316 piece0317 rfl rfl rfl
#print axioms join42_00

theorem join42_01 : ChunkFacts (toRow data42.row) 1025 1024 (toTotals ⟨6774857801797, 281982357569, 1461450551566, 5595389607800, 1258515883⟩) :=
  CleanupSegments208.append_exact piece0318 piece0319 rfl rfl rfl
#print axioms join42_01

theorem join42_02 : ChunkFacts (toRow data42.row) 2049 911 (toTotals ⟨370184231236, 90868739917, 390412635696, 70640335457, 486567255⟩) :=
  CleanupSegments208.append_exact piece0320 piece0321 rfl rfl rfl
#print axioms join42_02

theorem join42_03 : ChunkFacts (toRow data42.row) 1 2048 (toTotals ⟨1138194193100298, 1808497391257, 19189488854794, 1120813201636761, 5287960525⟩) :=
  CleanupSegments208.append_exact join42_00 join42_01 rfl rfl rfl
#print axioms join42_03

theorem join42_04 : ChunkFacts (toRow data42.row) 1 2959 (toTotals ⟨1138564377331534, 1899366131174, 19579901490490, 1120883841972218, 5774527780⟩) :=
  CleanupSegments208.append_exact join42_03 join42_02 rfl rfl rfl
#print axioms join42_04

theorem fact42 : ChunkFacts (toRow data42.row) 1 data42.steps (toTotals data42.total) := join42_04
#print axioms fact42

theorem piece0322 : ChunkFacts (toRow data43.row) 1 512 (toTotals ⟨1137527160415869, 1653811057015, 15624661572022, 1123556309900862, 2904430517⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0322
#print axioms piece0322

theorem piece0323 : ChunkFacts (toRow data43.row) 513 512 (toTotals ⟨42699230445000, 687889324230, 2882753082395, 40504366686835, 1528408675⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0323
#print axioms piece0323

theorem piece0324 : ChunkFacts (toRow data43.row) 1025 512 (toTotals ⟨7656196620834, 318668988610, 1189495665681, 6785369943763, 946468379⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0324
#print axioms piece0324

theorem piece0325 : ChunkFacts (toRow data43.row) 1537 512 (toTotals ⟨2033369425098, 188659861355, 660095505558, 1561933780895, 660829621⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0325
#print axioms piece0325

theorem piece0326 : ChunkFacts (toRow data43.row) 2049 512 (toTotals ⟨250750751686, 74430574465, 228419247888, 96762078263, 298429178⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0326
#print axioms piece0326

theorem piece0327 : ChunkFacts (toRow data43.row) 2561 512 (toTotals ⟨183565759714, 71498037760, 219419615232, 35644182242, 305837849⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0327
#print axioms piece0327

theorem piece0328 : ChunkFacts (toRow data43.row) 3073 243 (toTotals ⟨76722836791, 33933639015, 104138606448, 6517869358, 142762688⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0328
#print axioms piece0328

theorem join43_00 : ChunkFacts (toRow data43.row) 1 1024 (toTotals ⟨1180226390860869, 2341700381245, 18507414654417, 1164060676587697, 4432839192⟩) :=
  CleanupSegments208.append_exact piece0322 piece0323 rfl rfl rfl
#print axioms join43_00

theorem join43_01 : ChunkFacts (toRow data43.row) 1025 1024 (toTotals ⟨9689566045932, 507328849965, 1849591171239, 8347303724658, 1607298000⟩) :=
  CleanupSegments208.append_exact piece0324 piece0325 rfl rfl rfl
#print axioms join43_01

theorem join43_02 : ChunkFacts (toRow data43.row) 2049 1024 (toTotals ⟨434316511400, 145928612225, 447838863120, 132406260505, 604267027⟩) :=
  CleanupSegments208.append_exact piece0326 piece0327 rfl rfl rfl
#print axioms join43_02

theorem join43_03 : ChunkFacts (toRow data43.row) 1 2048 (toTotals ⟨1189915956906801, 2849029231210, 20357005825656, 1172407980312355, 6040137192⟩) :=
  CleanupSegments208.append_exact join43_00 join43_01 rfl rfl rfl
#print axioms join43_03

theorem join43_04 : ChunkFacts (toRow data43.row) 2049 1267 (toTotals ⟨511039348191, 179862251240, 551977469568, 138924129863, 747029715⟩) :=
  CleanupSegments208.append_exact join43_02 piece0328 rfl rfl rfl
#print axioms join43_04

theorem join43_05 : ChunkFacts (toRow data43.row) 1 3315 (toTotals ⟨1190426996254992, 3028891482450, 20908983295224, 1172546904442218, 6787166907⟩) :=
  CleanupSegments208.append_exact join43_03 join43_04 rfl rfl rfl
#print axioms join43_05

theorem fact43 : ChunkFacts (toRow data43.row) 1 data43.steps (toTotals data43.total) := join43_05
#print axioms fact43

theorem piece0329 : ChunkFacts (toRow data44.row) 1 512 (toTotals ⟨1179898900437451, 2204115531012, 16026651966542, 1166076364001921, 3133413110⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0329
#print axioms piece0329

theorem piece0330 : ChunkFacts (toRow data44.row) 513 512 (toTotals ⟨51148643134401, 1001775483684, 3269220300968, 48881198317117, 1727145437⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0330
#print axioms piece0330

theorem piece0331 : ChunkFacts (toRow data44.row) 1025 512 (toTotals ⟨10204637145325, 483519444120, 1425690106462, 9262466482983, 1127087124⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0331
#print axioms piece0331

theorem piece0332 : ChunkFacts (toRow data44.row) 1537 512 (toTotals ⟨3032484496763, 287493330132, 792899608624, 2527078218271, 817166406⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0332
#print axioms piece0332

theorem piece0333 : ChunkFacts (toRow data44.row) 2049 512 (toTotals ⟨645467596737, 141390162360, 359373086352, 427484672745, 446800329⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0333
#print axioms piece0333

theorem piece0334 : ChunkFacts (toRow data44.row) 2561 512 (toTotals ⟨183565759714, 89372547072, 219419615232, 53518691554, 326026521⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0334
#print axioms piece0334

theorem piece0335 : ChunkFacts (toRow data44.row) 3073 512 (toTotals ⟨155404181786, 89372547072, 219419615232, 25357113626, 344253018⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G20.checked0335
#print axioms piece0335

theorem piece0336 : ChunkFacts (toRow data44.row) 3585 122 (toTotals ⟨33773266445, 21295802232, 52283580192, 2785488485, 73572891⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0336
#print axioms piece0336

theorem join44_00 : ChunkFacts (toRow data44.row) 1 1024 (toTotals ⟨1231047543571852, 3205891014696, 19295872267510, 1214957562319038, 4860558547⟩) :=
  CleanupSegments208.append_exact piece0329 piece0330 rfl rfl rfl
#print axioms join44_00

theorem join44_01 : ChunkFacts (toRow data44.row) 1025 1024 (toTotals ⟨13237121642088, 771012774252, 2218589715086, 11789544701254, 1944253530⟩) :=
  CleanupSegments208.append_exact piece0331 piece0332 rfl rfl rfl
#print axioms join44_01

theorem join44_02 : ChunkFacts (toRow data44.row) 2049 1024 (toTotals ⟨829033356451, 230762709432, 578792701584, 481003364299, 772826850⟩) :=
  CleanupSegments208.append_exact piece0333 piece0334 rfl rfl rfl
#print axioms join44_02

theorem join44_03 : ChunkFacts (toRow data44.row) 3073 634 (toTotals ⟨189177448231, 110668349304, 271703195424, 28142602111, 417825909⟩) :=
  CleanupSegments208.append_exact piece0335 piece0336 rfl rfl rfl
#print axioms join44_03

theorem join44_04 : ChunkFacts (toRow data44.row) 1 2048 (toTotals ⟨1244284665213940, 3976903788948, 21514461982596, 1226747107020292, 6804812077⟩) :=
  CleanupSegments208.append_exact join44_00 join44_01 rfl rfl rfl
#print axioms join44_04

theorem join44_05 : ChunkFacts (toRow data44.row) 2049 1658 (toTotals ⟨1018210804682, 341431058736, 850495897008, 509145966410, 1190652759⟩) :=
  CleanupSegments208.append_exact join44_02 join44_03 rfl rfl rfl
#print axioms join44_05

theorem join44_06 : ChunkFacts (toRow data44.row) 1 3706 (toTotals ⟨1245302876018622, 4318334847684, 22364957879604, 1227256252986702, 7995464836⟩) :=
  CleanupSegments208.append_exact join44_04 join44_05 rfl rfl rfl
#print axioms join44_06

theorem fact44 : ChunkFacts (toRow data44.row) 1 data44.steps (toTotals data44.total) := join44_06
#print axioms fact44

theorem piece0337 : ChunkFacts (toRow data45.row) 1 512 (toTotals ⟨1195014832956778, 2634719646000, 16253431825788, 1181396120776990, 3309521987⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0337
#print axioms piece0337

theorem piece0338 : ChunkFacts (toRow data45.row) 513 512 (toTotals ⟨54797514649770, 1264297366800, 3499414986660, 52562397029910, 1885246588⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0338
#print axioms piece0338

theorem piece0339 : ChunkFacts (toRow data45.row) 1025 512 (toTotals ⟨12075207421565, 647586893200, 1619716200422, 11103078114343, 1279727122⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0339
#print axioms piece0339

theorem piece0340 : ChunkFacts (toRow data45.row) 1537 512 (toTotals ⟨3791309520313, 384830607200, 893609783584, 3282530343929, 941163745⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0340
#print axioms piece0340

theorem piece0341 : ChunkFacts (toRow data45.row) 2049 512 (toTotals ⟨1033021428212, 214294620800, 477694787376, 769621261636, 593007979⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0341
#print axioms piece0341

theorem piece0342 : ChunkFacts (toRow data45.row) 2561 512 (toTotals ⟨274029982606, 122892239600, 257560915536, 139361306670, 386948399⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0342
#print axioms piece0342

theorem piece0343 : ChunkFacts (toRow data45.row) 3073 512 (toTotals ⟨155404181786, 104693555200, 219419615232, 40678121754, 364703322⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0343
#print axioms piece0343

theorem piece0344 : ChunkFacts (toRow data45.row) 3585 512 (toTotals ⟨134790706636, 104693555200, 219419615232, 20064646604, 384321420⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0344
#print axioms piece0344

theorem piece0345 : ChunkFacts (toRow data45.row) 4097 25 (toTotals ⟨6146565505, 5111990000, 10713848400, 544707105, 6402375⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0345
#print axioms piece0345

theorem join45_00 : ChunkFacts (toRow data45.row) 1 1024 (toTotals ⟨1249812347606548, 3899017012800, 19752846812448, 1233958517806900, 5194768575⟩) :=
  CleanupSegments208.append_exact piece0337 piece0338 rfl rfl rfl
#print axioms join45_00

theorem join45_01 : ChunkFacts (toRow data45.row) 1025 1024 (toTotals ⟨15866516941878, 1032417500400, 2513325984006, 14385608458272, 2220890867⟩) :=
  CleanupSegments208.append_exact piece0339 piece0340 rfl rfl rfl
#print axioms join45_01

theorem join45_02 : ChunkFacts (toRow data45.row) 2049 1024 (toTotals ⟨1307051410818, 337186860400, 735255702912, 908982568306, 979956378⟩) :=
  CleanupSegments208.append_exact piece0341 piece0342 rfl rfl rfl
#print axioms join45_02

theorem join45_03 : ChunkFacts (toRow data45.row) 3073 1024 (toTotals ⟨290194888422, 209387110400, 438839230464, 60742768358, 749024742⟩) :=
  CleanupSegments208.append_exact piece0343 piece0344 rfl rfl rfl
#print axioms join45_03

theorem join45_04 : ChunkFacts (toRow data45.row) 1 2048 (toTotals ⟨1265678864548426, 4931434513200, 22266172796454, 1248344126265172, 7415659442⟩) :=
  CleanupSegments208.append_exact join45_00 join45_01 rfl rfl rfl
#print axioms join45_04

theorem join45_05 : ChunkFacts (toRow data45.row) 2049 2048 (toTotals ⟨1597246299240, 546573970800, 1174094933376, 969725336664, 1728981120⟩) :=
  CleanupSegments208.append_exact join45_02 join45_03 rfl rfl rfl
#print axioms join45_05

theorem join45_06 : ChunkFacts (toRow data45.row) 1 4096 (toTotals ⟨1267276110847666, 5478008484000, 23440267729830, 1249313851601836, 9144640562⟩) :=
  CleanupSegments208.append_exact join45_04 join45_05 rfl rfl rfl
#print axioms join45_06

theorem join45_07 : ChunkFacts (toRow data45.row) 1 4121 (toTotals ⟨1267282257413171, 5483120474000, 23450981578230, 1249314396308941, 9151042937⟩) :=
  CleanupSegments208.append_exact join45_06 piece0345 rfl rfl rfl
#print axioms join45_07

theorem fact45 : ChunkFacts (toRow data45.row) 1 data45.steps (toTotals data45.total) := join45_07
#print axioms fact45

theorem piece0346 : ChunkFacts (toRow data46.row) 1 512 (toTotals ⟨1251978716849224, 3160207273400, 16730956552190, 1238407967570434, 3466899124⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0346
#print axioms piece0346

theorem piece0347 : ChunkFacts (toRow data46.row) 513 512 (toTotals ⟨60684338596261, 1555441402080, 3793226123293, 58446553875048, 2031472782⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0347
#print axioms piece0347

theorem piece0348 : ChunkFacts (toRow data46.row) 1025 512 (toTotals ⟨13761456705163, 813280202120, 1802457040729, 12772279866554, 1423972728⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0348
#print axioms piece0348

theorem piece0349 : ChunkFacts (toRow data46.row) 1537 512 (toTotals ⟨4341430999749, 465255923808, 956178658240, 3850508265317, 1025748528⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0349
#print axioms piece0349

theorem piece0350 : ChunkFacts (toRow data46.row) 2049 512 (toTotals ⟨1566728354597, 302370467248, 605138565030, 1263960256815, 749519119⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0350
#print axioms piece0350

theorem piece0351 : ChunkFacts (toRow data46.row) 2561 512 (toTotals ⟨434728934314, 176421008584, 329557976784, 281591966114, 496381016⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G21.checked0351
#print axioms piece0351

theorem piece0352 : ChunkFacts (toRow data46.row) 3073 512 (toTotals ⟨155404181786, 117461061632, 219419615232, 53445628186, 381745242⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0352
#print axioms piece0352

theorem piece0353 : ChunkFacts (toRow data46.row) 3585 512 (toTotals ⟨134790706636, 117461061632, 219419615232, 32832153036, 405709594⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0353
#print axioms piece0353

theorem piece0354 : ChunkFacts (toRow data46.row) 4097 450 (toTotals ⟨105346899654, 103237261200, 192849271200, 15734889654, 356552404⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0354
#print axioms piece0354

theorem join46_00 : ChunkFacts (toRow data46.row) 1 1024 (toTotals ⟨1312663055445485, 4715648675480, 20524182675483, 1296854521445482, 5498371906⟩) :=
  CleanupSegments208.append_exact piece0346 piece0347 rfl rfl rfl
#print axioms join46_00

theorem join46_01 : ChunkFacts (toRow data46.row) 1025 1024 (toTotals ⟨18102887704912, 1278536125928, 2758635698969, 16622788131871, 2449721256⟩) :=
  CleanupSegments208.append_exact piece0348 piece0349 rfl rfl rfl
#print axioms join46_01

theorem join46_02 : ChunkFacts (toRow data46.row) 2049 1024 (toTotals ⟨2001457288911, 478791475832, 934696541814, 1545552222929, 1245900135⟩) :=
  CleanupSegments208.append_exact piece0350 piece0351 rfl rfl rfl
#print axioms join46_02

theorem join46_03 : ChunkFacts (toRow data46.row) 3073 1024 (toTotals ⟨290194888422, 234922123264, 438839230464, 86277781222, 787454836⟩) :=
  CleanupSegments208.append_exact piece0352 piece0353 rfl rfl rfl
#print axioms join46_03

theorem join46_04 : ChunkFacts (toRow data46.row) 1 2048 (toTotals ⟨1330765943150397, 5994184801408, 23282818374452, 1313477309577353, 7948093162⟩) :=
  CleanupSegments208.append_exact join46_00 join46_01 rfl rfl rfl
#print axioms join46_04

theorem join46_05 : ChunkFacts (toRow data46.row) 2049 2048 (toTotals ⟨2291652177333, 713713599096, 1373535772278, 1631830004151, 2033354971⟩) :=
  CleanupSegments208.append_exact join46_02 join46_03 rfl rfl rfl
#print axioms join46_05

theorem join46_06 : ChunkFacts (toRow data46.row) 1 4096 (toTotals ⟨1333057595327730, 6707898400504, 24656354146730, 1315109139581504, 9981448133⟩) :=
  CleanupSegments208.append_exact join46_04 join46_05 rfl rfl rfl
#print axioms join46_06

theorem join46_07 : ChunkFacts (toRow data46.row) 1 4546 (toTotals ⟨1333162942227384, 6811135661704, 24849203417930, 1315124874471158, 10338000537⟩) :=
  CleanupSegments208.append_exact join46_06 piece0354 rfl rfl rfl
#print axioms join46_07

theorem fact46 : ChunkFacts (toRow data46.row) 1 data46.steps (toTotals data46.total) := join46_07
#print axioms fact46

theorem piece0355 : ChunkFacts (toRow data47.row) 1 512 (toTotals ⟨1256872722086095, 3479145586432, 16831455851446, 1243520411821081, 3607245519⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0355
#print axioms piece0355

theorem piece0356 : ChunkFacts (toRow data47.row) 513 512 (toTotals ⟨63394529625503, 1778224424946, 3971960324430, 61200793726019, 2159880184⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0356
#print axioms piece0356

theorem piece0357 : ChunkFacts (toRow data47.row) 1025 512 (toTotals ⟨15514180714763, 969781908374, 1970008024857, 14513954598280, 1553277559⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0357
#print axioms piece0357

theorem piece0358 : ChunkFacts (toRow data47.row) 1537 512 (toTotals ⟨4855004916944, 560323977402, 1050031970224, 4365296924122, 1129663842⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0358
#print axioms piece0358

theorem piece0359 : ChunkFacts (toRow data47.row) 2049 512 (toTotals ⟨2057890424442, 383773298274, 710052650046, 1731611072670, 891589500⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0359
#print axioms piece0359

theorem piece0360 : ChunkFacts (toRow data47.row) 2561 512 (toTotals ⟨522266352905, 214454214760, 368556384960, 368164182705, 568092680⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0360
#print axioms piece0360

theorem piece0361 : ChunkFacts (toRow data47.row) 3073 512 (toTotals ⟨247705967923, 154855892286, 266131994256, 136429865953, 458621632⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0361
#print axioms piece0361

theorem piece0362 : ChunkFacts (toRow data47.row) 3585 512 (toTotals ⟨134790706636, 127675067392, 219419615232, 43046158796, 421440282⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0362
#print axioms piece0362

theorem piece0363 : ChunkFacts (toRow data47.row) 4097 512 (toTotals ⟨119046224446, 127675067392, 219419615232, 27301676606, 447532359⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0363
#print axioms piece0363

theorem piece0364 : ChunkFacts (toRow data47.row) 4609 347 (toTotals ⟨73460944265, 86529782002, 148708215792, 11282510475, 292162494⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0364
#print axioms piece0364

theorem join47_00 : ChunkFacts (toRow data47.row) 1 1024 (toTotals ⟨1320267251711598, 5257370011378, 20803416175876, 1304721205547100, 5767125703⟩) :=
  CleanupSegments208.append_exact piece0355 piece0356 rfl rfl rfl
#print axioms join47_00

theorem join47_01 : ChunkFacts (toRow data47.row) 1025 1024 (toTotals ⟨20369185631707, 1530105885776, 3020039995081, 18879251522402, 2682941401⟩) :=
  CleanupSegments208.append_exact piece0357 piece0358 rfl rfl rfl
#print axioms join47_01

theorem join47_02 : ChunkFacts (toRow data47.row) 2049 1024 (toTotals ⟨2580156777347, 598227513034, 1078609035006, 2099775255375, 1459682180⟩) :=
  CleanupSegments208.append_exact piece0359 piece0360 rfl rfl rfl
#print axioms join47_02

theorem join47_03 : ChunkFacts (toRow data47.row) 3073 1024 (toTotals ⟨382496674559, 282530959678, 485551609488, 179476024749, 880061914⟩) :=
  CleanupSegments208.append_exact piece0361 piece0362 rfl rfl rfl
#print axioms join47_03

theorem join47_04 : ChunkFacts (toRow data47.row) 4097 859 (toTotals ⟨192507168711, 214204849394, 368127831024, 38584187081, 739694853⟩) :=
  CleanupSegments208.append_exact piece0363 piece0364 rfl rfl rfl
#print axioms join47_04

theorem join47_05 : ChunkFacts (toRow data47.row) 1 2048 (toTotals ⟨1340636437343305, 6787475897154, 23823456170957, 1323600457069502, 8450067104⟩) :=
  CleanupSegments208.append_exact join47_00 join47_01 rfl rfl rfl
#print axioms join47_05

theorem join47_06 : ChunkFacts (toRow data47.row) 2049 2048 (toTotals ⟨2962653451906, 880758472712, 1564160644494, 2279251280124, 2339744094⟩) :=
  CleanupSegments208.append_exact join47_02 join47_03 rfl rfl rfl
#print axioms join47_06

theorem join47_07 : ChunkFacts (toRow data47.row) 1 4096 (toTotals ⟨1343599090795211, 7668234369866, 25387616815451, 1325879708349626, 10789811198⟩) :=
  CleanupSegments208.append_exact join47_05 join47_06 rfl rfl rfl
#print axioms join47_07

theorem join47_08 : ChunkFacts (toRow data47.row) 1 4955 (toTotals ⟨1343791597963922, 7882439219260, 25755744646475, 1325918292536707, 11529506051⟩) :=
  CleanupSegments208.append_exact join47_07 join47_04 rfl rfl rfl
#print axioms join47_08

theorem fact47 : ChunkFacts (toRow data47.row) 1 data47.steps (toTotals data47.total) := join47_08
#print axioms fact47

theorem piece0365 : ChunkFacts (toRow data48.row) 1 512 (toTotals ⟨1308724570740742, 3862614659544, 17253316183306, 1295333869216980, 3741157818⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0365
#print axioms piece0365

theorem piece0366 : ChunkFacts (toRow data48.row) 513 512 (toTotals ⟨68785204243495, 2009944697952, 4208426862953, 66586722078494, 2282779698⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0366
#print axioms piece0366

theorem piece0367 : ChunkFacts (toRow data48.row) 1025 512 (toTotals ⟨17553412687781, 1118633082816, 2137878723826, 16534167046771, 1682531551⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G22.checked0367
#print axioms piece0367

theorem piece0368 : ChunkFacts (toRow data48.row) 1537 512 (toTotals ⟨5210717043116, 636764436792, 1119967891114, 4727513588794, 1213626971⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0368
#print axioms piece0368

theorem piece0369 : ChunkFacts (toRow data48.row) 2049 512 (toTotals ⟨2514799650947, 451471007904, 793362174734, 2172908484117, 1005905784⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0369
#print axioms piece0369

theorem piece0370 : ChunkFacts (toRow data48.row) 2561 512 (toTotals ⟨652642033939, 258776414952, 419554303344, 491864145547, 647456204⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0370
#print axioms piece0370

theorem piece0371 : ChunkFacts (toRow data48.row) 3073 512 (toTotals ⟨357184138749, 200095757016, 324415329552, 232864566213, 557873355⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0371
#print axioms piece0371

theorem piece0372 : ChunkFacts (toRow data48.row) 3585 512 (toTotals ⟨134790706636, 135335571456, 219419615232, 50706662860, 433238298⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0372
#print axioms piece0372

theorem piece0373 : ChunkFacts (toRow data48.row) 4097 512 (toTotals ⟨119046224446, 135335571456, 219419615232, 34962180670, 460903239⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0373
#print axioms piece0373

theorem piece0374 : ChunkFacts (toRow data48.row) 4609 512 (toTotals ⟨106626416820, 135335571456, 219419615232, 22542373044, 488581249⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0374
#print axioms piece0374

theorem piece0375 : ChunkFacts (toRow data48.row) 5121 193 (toTotals ⟨37479936506, 51015166584, 82710909648, 5784193442, 159574436⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0375
#print axioms piece0375

theorem join48_00 : ChunkFacts (toRow data48.row) 1 1024 (toTotals ⟨1377509774984237, 5872559357496, 21461743046259, 1361920591295474, 6023937516⟩) :=
  CleanupSegments208.append_exact piece0365 piece0366 rfl rfl rfl
#print axioms join48_00

theorem join48_01 : ChunkFacts (toRow data48.row) 1025 1024 (toTotals ⟨22764129730897, 1755397519608, 3257846614940, 21261680635565, 2896158522⟩) :=
  CleanupSegments208.append_exact piece0367 piece0368 rfl rfl rfl
#print axioms join48_01

theorem join48_02 : ChunkFacts (toRow data48.row) 2049 1024 (toTotals ⟨3167441684886, 710247422856, 1212916478078, 2664772629664, 1653361988⟩) :=
  CleanupSegments208.append_exact piece0369 piece0370 rfl rfl rfl
#print axioms join48_02

theorem join48_03 : ChunkFacts (toRow data48.row) 3073 1024 (toTotals ⟨491974845385, 335431328472, 543834944784, 283571229073, 991111653⟩) :=
  CleanupSegments208.append_exact piece0371 piece0372 rfl rfl rfl
#print axioms join48_03

theorem join48_04 : ChunkFacts (toRow data48.row) 4097 1024 (toTotals ⟨225672641266, 270671142912, 438839230464, 57504553714, 949484488⟩) :=
  CleanupSegments208.append_exact piece0373 piece0374 rfl rfl rfl
#print axioms join48_04

theorem join48_05 : ChunkFacts (toRow data48.row) 1 2048 (toTotals ⟨1400273904715134, 7627956877104, 24719589661199, 1383182271931039, 8920096038⟩) :=
  CleanupSegments208.append_exact join48_00 join48_01 rfl rfl rfl
#print axioms join48_05

theorem join48_06 : ChunkFacts (toRow data48.row) 2049 2048 (toTotals ⟨3659416530271, 1045678751328, 1756751422862, 2948343858737, 2644473641⟩) :=
  CleanupSegments208.append_exact join48_02 join48_03 rfl rfl rfl
#print axioms join48_06

theorem join48_07 : ChunkFacts (toRow data48.row) 4097 1217 (toTotals ⟨263152577772, 321686309496, 521550140112, 63288747156, 1109058924⟩) :=
  CleanupSegments208.append_exact join48_04 piece0375 rfl rfl rfl
#print axioms join48_07

theorem join48_08 : ChunkFacts (toRow data48.row) 1 4096 (toTotals ⟨1403933321245405, 8673635628432, 26476341084061, 1386130615789776, 11564569679⟩) :=
  CleanupSegments208.append_exact join48_05 join48_06 rfl rfl rfl
#print axioms join48_08

theorem join48_09 : ChunkFacts (toRow data48.row) 1 5313 (toTotals ⟨1404196473823177, 8995321937928, 26997891224173, 1386193904536932, 12673628603⟩) :=
  CleanupSegments208.append_exact join48_08 join48_07 rfl rfl rfl
#print axioms join48_09

theorem fact48 : ChunkFacts (toRow data48.row) 1 data48.steps (toTotals data48.total) := join48_09
#print axioms fact48

theorem piece0376 : ChunkFacts (toRow data49.row) 1 512 (toTotals ⟨1087543643139077, 910001619276, 14926025781074, 1073527618977279, 2914927617⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0376
#print axioms piece0376

theorem piece0377 : ChunkFacts (toRow data49.row) 513 512 (toTotals ⟨36303537912366, 344474958140, 2472309821718, 34175703048788, 1449153977⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0377
#print axioms piece0377

theorem piece0378 : ChunkFacts (toRow data49.row) 1025 512 (toTotals ⟨5658963333939, 152891373601, 967847422176, 4844007285364, 853408786⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0378
#print axioms piece0378

theorem piece0379 : ChunkFacts (toRow data49.row) 1537 512 (toTotals ⟨1182384648086, 80976103904, 475833594039, 787527157951, 517842505⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0379
#print axioms piece0379

theorem piece0380 : ChunkFacts (toRow data49.row) 2049 512 (toTotals ⟨224255678828, 41794118144, 210752589312, 55297207660, 288171342⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0380
#print axioms piece0380

theorem piece0381 : ChunkFacts (toRow data49.row) 2561 409 (toTotals ⟨149118433229, 33386317033, 168355095759, 14149654503, 231396631⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0381
#print axioms piece0381

theorem join49_00 : ChunkFacts (toRow data49.row) 1 1024 (toTotals ⟨1123847181051443, 1254476577416, 17398335602792, 1107703322026067, 4364081594⟩) :=
  CleanupSegments208.append_exact piece0376 piece0377 rfl rfl rfl
#print axioms join49_00

theorem join49_01 : ChunkFacts (toRow data49.row) 1025 1024 (toTotals ⟨6841347982025, 233867477505, 1443681016215, 5631534443315, 1371251291⟩) :=
  CleanupSegments208.append_exact piece0378 piece0379 rfl rfl rfl
#print axioms join49_01

theorem join49_02 : ChunkFacts (toRow data49.row) 2049 921 (toTotals ⟨373374112057, 75180435177, 379107685071, 69446862163, 519567973⟩) :=
  CleanupSegments208.append_exact piece0380 piece0381 rfl rfl rfl
#print axioms join49_02

theorem join49_03 : ChunkFacts (toRow data49.row) 1 2048 (toTotals ⟨1130688529033468, 1488344054921, 18842016619007, 1113334856469382, 5735332885⟩) :=
  CleanupSegments208.append_exact join49_00 join49_01 rfl rfl rfl
#print axioms join49_03

theorem join49_04 : ChunkFacts (toRow data49.row) 1 2969 (toTotals ⟨1131061903145525, 1563524490098, 19221124304078, 1113404303331545, 6254900858⟩) :=
  CleanupSegments208.append_exact join49_03 join49_02 rfl rfl rfl
#print axioms join49_04

theorem fact49 : ChunkFacts (toRow data49.row) 1 data49.steps (toTotals data49.total) := join49_04
#print axioms fact49

theorem piece0382 : ChunkFacts (toRow data50.row) 1 512 (toTotals ⟨1109929748084569, 1366562447270, 15229622935898, 1096066687595941, 3110391967⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0382
#print axioms piece0382

theorem piece0383 : ChunkFacts (toRow data50.row) 513 512 (toTotals ⟨41184778553011, 560891938021, 2730765308419, 39014905182613, 1616428102⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G23.checked0383
#print axioms piece0383

theorem piece0384 : ChunkFacts (toRow data50.row) 1025 512 (toTotals ⟨7512793084682, 262346975425, 1136427041358, 6638713018749, 996898175⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0384
#print axioms piece0384

theorem piece0385 : ChunkFacts (toRow data50.row) 1537 512 (toTotals ⟨1966017100862, 158705181538, 637808484516, 1486913797884, 699559916⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0385
#print axioms piece0385

theorem piece0386 : ChunkFacts (toRow data50.row) 2049 512 (toTotals ⟨224255678828, 60369281536, 210752589312, 73872371052, 307049806⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0386
#print axioms piece0386

theorem piece0387 : ChunkFacts (toRow data50.row) 2561 512 (toTotals ⟨183449957090, 60369281536, 210752589312, 33066649314, 320551270⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0387
#print axioms piece0387

theorem piece0388 : ChunkFacts (toRow data50.row) 3073 222 (toTotals ⟨70266228345, 26175743166, 91381005522, 5060965989, 135980717⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0388
#print axioms piece0388

theorem join50_00 : ChunkFacts (toRow data50.row) 1 1024 (toTotals ⟨1151114526637580, 1927454385291, 17960388244317, 1135081592778554, 4726820069⟩) :=
  CleanupSegments208.append_exact piece0382 piece0383 rfl rfl rfl
#print axioms join50_00

theorem join50_01 : ChunkFacts (toRow data50.row) 1025 1024 (toTotals ⟨9478810185544, 421052156963, 1774235525874, 8125626816633, 1696458091⟩) :=
  CleanupSegments208.append_exact piece0384 piece0385 rfl rfl rfl
#print axioms join50_01

theorem join50_02 : ChunkFacts (toRow data50.row) 2049 1024 (toTotals ⟨407705635918, 120738563072, 421505178624, 106939020366, 627601076⟩) :=
  CleanupSegments208.append_exact piece0386 piece0387 rfl rfl rfl
#print axioms join50_02

theorem join50_03 : ChunkFacts (toRow data50.row) 1 2048 (toTotals ⟨1160593336823124, 2348506542254, 19734623770191, 1143207219595187, 6423278160⟩) :=
  CleanupSegments208.append_exact join50_00 join50_01 rfl rfl rfl
#print axioms join50_03

theorem join50_04 : ChunkFacts (toRow data50.row) 2049 1246 (toTotals ⟨477971864263, 146914306238, 512886184146, 111999986355, 763581793⟩) :=
  CleanupSegments208.append_exact join50_02 piece0388 rfl rfl rfl
#print axioms join50_04

theorem join50_05 : ChunkFacts (toRow data50.row) 1 3294 (toTotals ⟨1161071308687387, 2495420848492, 20247509954337, 1143319219581542, 7186859953⟩) :=
  CleanupSegments208.append_exact join50_03 join50_04 rfl rfl rfl
#print axioms join50_05

theorem fact50 : ChunkFacts (toRow data50.row) 1 data50.steps (toTotals data50.total) := join50_05
#print axioms fact50

theorem piece0389 : ChunkFacts (toRow data51.row) 1 512 (toTotals ⟨1150101139803895, 1820658529173, 15598583412814, 1136323214920254, 3343852618⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0389
#print axioms piece0389

theorem piece0390 : ChunkFacts (toRow data51.row) 513 512 (toTotals ⟨49022669121212, 813275622438, 3076572853756, 46759371889894, 1815741767⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0390
#print axioms piece0390

theorem piece0391 : ChunkFacts (toRow data51.row) 1025 512 (toTotals ⟨9820509244999, 396320795349, 1351102552695, 8865727487653, 1177774078⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0391
#print axioms piece0391

theorem piece0392 : ChunkFacts (toRow data51.row) 1537 512 (toTotals ⟨2833202104643, 234933189954, 740220239318, 2327915055279, 836285395⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0392
#print axioms piece0392

theorem piece0393 : ChunkFacts (toRow data51.row) 2049 512 (toTotals ⟨596498056776, 113339788629, 331157396372, 378680449033, 449422409⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0393
#print axioms piece0393

theorem piece0394 : ChunkFacts (toRow data51.row) 2561 512 (toTotals ⟨183449957090, 75461601792, 210752589312, 48158969570, 339297894⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0394
#print axioms piece0394

theorem piece0395 : ChunkFacts (toRow data51.row) 3073 512 (toTotals ⟨155288379162, 75461601792, 210752589312, 19997391642, 356204582⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0395
#print axioms piece0395

theorem piece0396 : ChunkFacts (toRow data51.row) 3585 32 (toTotals ⟨8960272220, 4716350112, 13172036832, 504585500, 13298785⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0396
#print axioms piece0396

theorem join51_00 : ChunkFacts (toRow data51.row) 1 1024 (toTotals ⟨1199123808925107, 2633934151611, 18675156266570, 1183082586810148, 5159594385⟩) :=
  CleanupSegments208.append_exact piece0389 piece0390 rfl rfl rfl
#print axioms join51_00

theorem join51_01 : ChunkFacts (toRow data51.row) 1025 1024 (toTotals ⟨12653711349642, 631253985303, 2091322792013, 11193642542932, 2014059473⟩) :=
  CleanupSegments208.append_exact piece0391 piece0392 rfl rfl rfl
#print axioms join51_01

theorem join51_02 : ChunkFacts (toRow data51.row) 2049 1024 (toTotals ⟨779948013866, 188801390421, 541909985684, 426839418603, 788720303⟩) :=
  CleanupSegments208.append_exact piece0393 piece0394 rfl rfl rfl
#print axioms join51_02

theorem join51_03 : ChunkFacts (toRow data51.row) 3073 544 (toTotals ⟨164248651382, 80177951904, 223924626144, 20501977142, 369503367⟩) :=
  CleanupSegments208.append_exact piece0395 piece0396 rfl rfl rfl
#print axioms join51_03

theorem join51_04 : ChunkFacts (toRow data51.row) 1 2048 (toTotals ⟨1211777520274749, 3265188136914, 20766479058583, 1194276229353080, 7173653858⟩) :=
  CleanupSegments208.append_exact join51_00 join51_01 rfl rfl rfl
#print axioms join51_04

theorem join51_05 : ChunkFacts (toRow data51.row) 2049 1568 (toTotals ⟨944196665248, 268979342325, 765834611828, 447341395745, 1158223670⟩) :=
  CleanupSegments208.append_exact join51_02 join51_03 rfl rfl rfl
#print axioms join51_05

theorem join51_06 : ChunkFacts (toRow data51.row) 1 3616 (toTotals ⟨1212721716939997, 3534167479239, 21532313670411, 1194723570748825, 8331877528⟩) :=
  CleanupSegments208.append_exact join51_04 join51_05 rfl rfl rfl
#print axioms join51_06

theorem fact51 : ChunkFacts (toRow data51.row) 1 data51.steps (toTotals data51.total) := join51_06
#print axioms fact51

theorem piece0397 : ChunkFacts (toRow data52.row) 1 512 (toTotals ⟨1175614237393857, 2244427119315, 15865932519136, 1161992731994036, 3522585855⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0397
#print axioms piece0397

theorem piece0398 : ChunkFacts (toRow data52.row) 513 512 (toTotals ⟨54382960430794, 1064160505035, 3350004879809, 52097116056020, 1976049184⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0398
#print axioms piece0398

theorem piece0399 : ChunkFacts (toRow data52.row) 1025 512 (toTotals ⟨11689928859803, 538627589505, 1535810432883, 10692746016425, 1335503506⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G24.checked0399
#print axioms piece0399

theorem piece0400 : ChunkFacts (toRow data52.row) 1537 512 (toTotals ⟨3475864683390, 314621366706, 825838478726, 2964647571370, 954325235⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0400
#print axioms piece0400

theorem piece0401 : ChunkFacts (toRow data52.row) 2049 512 (toTotals ⟨959710098178, 175643226918, 443329680412, 692023644684, 601462696⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0401
#print axioms piece0401

theorem piece0402 : ChunkFacts (toRow data52.row) 2561 512 (toTotals ⟨225215142409, 96551396109, 227629261503, 94137277015, 376086662⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0402
#print axioms piece0402

theorem piece0403 : ChunkFacts (toRow data52.row) 3073 512 (toTotals ⟨155288379162, 89392974336, 210752589312, 33928764186, 376654886⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0403
#print axioms piece0403

theorem piece0404 : ChunkFacts (toRow data52.row) 3585 391 (toTotals ⟨104418115145, 68266900323, 160945825041, 11739190427, 288220765⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0404
#print axioms piece0404

theorem join52_00 : ChunkFacts (toRow data52.row) 1 1024 (toTotals ⟨1229997197824651, 3308587624350, 19215937398945, 1214089848050056, 5498635039⟩) :=
  CleanupSegments208.append_exact piece0397 piece0398 rfl rfl rfl
#print axioms join52_00

theorem join52_01 : ChunkFacts (toRow data52.row) 1025 1024 (toTotals ⟨15165793543193, 853248956211, 2361648911609, 13657393587795, 2289828741⟩) :=
  CleanupSegments208.append_exact piece0399 piece0400 rfl rfl rfl
#print axioms join52_01

theorem join52_02 : ChunkFacts (toRow data52.row) 2049 1024 (toTotals ⟨1184925240587, 272194623027, 670958941915, 786160921699, 977549358⟩) :=
  CleanupSegments208.append_exact piece0401 piece0402 rfl rfl rfl
#print axioms join52_02

theorem join52_03 : ChunkFacts (toRow data52.row) 3073 903 (toTotals ⟨259706494307, 157659874659, 371698414353, 45667954613, 664875651⟩) :=
  CleanupSegments208.append_exact piece0403 piece0404 rfl rfl rfl
#print axioms join52_03

theorem join52_04 : ChunkFacts (toRow data52.row) 1 2048 (toTotals ⟨1245162991367844, 4161836580561, 21577586310554, 1227747241637851, 7788463780⟩) :=
  CleanupSegments208.append_exact join52_00 join52_01 rfl rfl rfl
#print axioms join52_04

theorem join52_05 : ChunkFacts (toRow data52.row) 2049 1927 (toTotals ⟨1444631734894, 429854497686, 1042657356268, 831828876312, 1642425009⟩) :=
  CleanupSegments208.append_exact join52_02 join52_03 rfl rfl rfl
#print axioms join52_05

theorem join52_06 : ChunkFacts (toRow data52.row) 1 3975 (toTotals ⟨1246607623102738, 4591691078247, 22620243666822, 1228579070514163, 9430888789⟩) :=
  CleanupSegments208.append_exact join52_04 join52_05 rfl rfl rfl
#print axioms join52_06

theorem fact52 : ChunkFacts (toRow data52.row) 1 data52.steps (toTotals data52.total) := join52_06
#print axioms fact52

theorem piece0405 : ChunkFacts (toRow data53.row) 1 512 (toTotals ⟨1199771648331297, 2666656093110, 16117824855692, 1186320479568715, 3701982091⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0405
#print axioms piece0405

theorem piece0406 : ChunkFacts (toRow data53.row) 513 512 (toTotals ⟨58292606864421, 1320008892465, 3573212278692, 56039403478194, 2142106206⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0406
#print axioms piece0406

theorem piece0407 : ChunkFacts (toRow data53.row) 1025 512 (toTotals ⟨13583138200055, 705511556040, 1728339209944, 12560310546151, 1501825421⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0407
#print axioms piece0407

theorem piece0408 : ChunkFacts (toRow data53.row) 1537 512 (toTotals ⟨4133683805543, 398767401240, 897461429000, 3634989777783, 1059719684⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0408
#print axioms piece0408

theorem piece0409 : ChunkFacts (toRow data53.row) 2049 512 (toTotals ⟨1498530583136, 259118088660, 571885932612, 1185762739184, 774053980⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0409
#print axioms piece0409

theorem piece0410 : ChunkFacts (toRow data53.row) 2561 512 (toTotals ⟨378088580821, 143483614515, 292666193361, 228906001975, 484314430⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0410
#print axioms piece0410

theorem piece0411 : ChunkFacts (toRow data53.row) 3073 512 (toTotals ⟨155288379162, 103324346880, 210752589312, 47860136730, 397105190⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0411
#print axioms piece0411

theorem piece0412 : ChunkFacts (toRow data53.row) 3585 512 (toTotals ⟨134674904012, 103324346880, 210752589312, 27246661580, 420295612⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0412
#print axioms piece0412

theorem piece0413 : ChunkFacts (toRow data53.row) 4097 317 (toTotals ⟨75253864911, 63972300705, 130485489867, 8740675749, 253922124⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0413
#print axioms piece0413

theorem join53_00 : ChunkFacts (toRow data53.row) 1 1024 (toTotals ⟨1258064255195718, 3986664985575, 19691037134384, 1242359883046909, 5844088297⟩) :=
  CleanupSegments208.append_exact piece0405 piece0406 rfl rfl rfl
#print axioms join53_00

theorem join53_01 : ChunkFacts (toRow data53.row) 1025 1024 (toTotals ⟨17716822005598, 1104278957280, 2625800638944, 16195300323934, 2561545105⟩) :=
  CleanupSegments208.append_exact piece0407 piece0408 rfl rfl rfl
#print axioms join53_01

theorem join53_02 : ChunkFacts (toRow data53.row) 2049 1024 (toTotals ⟨1876619163957, 402601703175, 864552125973, 1414668741159, 1258368410⟩) :=
  CleanupSegments208.append_exact piece0409 piece0410 rfl rfl rfl
#print axioms join53_02

theorem join53_03 : ChunkFacts (toRow data53.row) 3073 1024 (toTotals ⟨289963283174, 206648693760, 421505178624, 75106798310, 817400802⟩) :=
  CleanupSegments208.append_exact piece0411 piece0412 rfl rfl rfl
#print axioms join53_03

theorem join53_04 : ChunkFacts (toRow data53.row) 1 2048 (toTotals ⟨1275781077201316, 5090943942855, 22316837773328, 1258555183370843, 8405633402⟩) :=
  CleanupSegments208.append_exact join53_00 join53_01 rfl rfl rfl
#print axioms join53_04

theorem join53_05 : ChunkFacts (toRow data53.row) 2049 2048 (toTotals ⟨2166582447131, 609250396935, 1286057304597, 1489775539469, 2075769212⟩) :=
  CleanupSegments208.append_exact join53_02 join53_03 rfl rfl rfl
#print axioms join53_05

theorem join53_06 : ChunkFacts (toRow data53.row) 1 4096 (toTotals ⟨1277947659648447, 5700194339790, 23602895077925, 1260044958910312, 10481402614⟩) :=
  CleanupSegments208.append_exact join53_04 join53_05 rfl rfl rfl
#print axioms join53_06

theorem join53_07 : ChunkFacts (toRow data53.row) 1 4413 (toTotals ⟨1278022913513358, 5764166640495, 23733380567792, 1260053699586061, 10735324738⟩) :=
  CleanupSegments208.append_exact join53_06 piece0413 rfl rfl rfl
#print axioms join53_07

theorem fact53 : ChunkFacts (toRow data53.row) 1 data53.steps (toTotals data53.total) := join53_07
#print axioms fact53

theorem piece0414 : ChunkFacts (toRow data54.row) 1 512 (toTotals ⟨1249189237545272, 3076153189578, 16531438454472, 1235733952280378, 3843231991⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0414
#print axioms piece0414

theorem piece0415 : ChunkFacts (toRow data54.row) 513 512 (toTotals ⟨62712198069000, 1549953634131, 3815032247910, 60447119455221, 2275159053⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G25.checked0415
#print axioms piece0415

theorem piece0416 : ChunkFacts (toRow data54.row) 1025 512 (toTotals ⟨15210070611252, 836671438092, 1873449901749, 14173292147595, 1629680091⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0416
#print axioms piece0416

theorem piece0417 : ChunkFacts (toRow data54.row) 1537 512 (toTotals ⟨4537954975854, 470682670220, 964968117764, 4043669528310, 1146839931⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0417
#print axioms piece0417

theorem piece0418 : ChunkFacts (toRow data54.row) 2049 512 (toTotals ⟨1977674123193, 330357649846, 672952626243, 1635079146796, 918171889⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0418
#print axioms piece0418

theorem piece0419 : ChunkFacts (toRow data54.row) 2561 512 (toTotals ⟨480049613077, 180355041860, 337533443820, 322871211117, 569428900⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0419
#print axioms piece0419

theorem piece0420 : ChunkFacts (toRow data54.row) 3073 512 (toTotals ⟨194355268944, 122729406534, 229687392258, 87397283220, 436033864⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0420
#print axioms piece0420

theorem piece0421 : ChunkFacts (toRow data54.row) 3585 512 (toTotals ⟨134674904012, 112611928576, 210752589312, 36534243276, 436026300⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0421
#print axioms piece0421

theorem piece0422 : ChunkFacts (toRow data54.row) 4097 512 (toTotals ⟨118930421822, 112611928576, 210752589312, 20789761086, 461323498⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0422
#print axioms piece0422

theorem piece0423 : ChunkFacts (toRow data54.row) 4609 154 (toTotals ⟨33219507411, 33871556642, 63390427254, 3700636799, 121782384⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0423
#print axioms piece0423

theorem join54_00 : ChunkFacts (toRow data54.row) 1 1024 (toTotals ⟨1311901435614272, 4626106823709, 20346470702382, 1296181071735599, 6118391044⟩) :=
  CleanupSegments208.append_exact piece0414 piece0415 rfl rfl rfl
#print axioms join54_00

theorem join54_01 : ChunkFacts (toRow data54.row) 1025 1024 (toTotals ⟨19748025587106, 1307354108312, 2838418019513, 18216961675905, 2776520022⟩) :=
  CleanupSegments208.append_exact piece0416 piece0417 rfl rfl rfl
#print axioms join54_01

theorem join54_02 : ChunkFacts (toRow data54.row) 2049 1024 (toTotals ⟨2457723736270, 510712691706, 1010486070063, 1957950357913, 1487600789⟩) :=
  CleanupSegments208.append_exact piece0418 piece0419 rfl rfl rfl
#print axioms join54_02

theorem join54_03 : ChunkFacts (toRow data54.row) 3073 1024 (toTotals ⟨329030172956, 235341335110, 440439981570, 123931526496, 872060164⟩) :=
  CleanupSegments208.append_exact piece0420 piece0421 rfl rfl rfl
#print axioms join54_03

theorem join54_04 : ChunkFacts (toRow data54.row) 4097 666 (toTotals ⟨152149929233, 146483485218, 274143016566, 24490397885, 583105882⟩) :=
  CleanupSegments208.append_exact piece0422 piece0423 rfl rfl rfl
#print axioms join54_04

theorem join54_05 : ChunkFacts (toRow data54.row) 1 2048 (toTotals ⟨1331649461201378, 5933460932021, 23184888721895, 1314398033411504, 8894911066⟩) :=
  CleanupSegments208.append_exact join54_00 join54_01 rfl rfl rfl
#print axioms join54_05

theorem join54_06 : ChunkFacts (toRow data54.row) 2049 2048 (toTotals ⟨2786753909226, 746054026816, 1450926051633, 2081881884409, 2359660953⟩) :=
  CleanupSegments208.append_exact join54_02 join54_03 rfl rfl rfl
#print axioms join54_06

theorem join54_07 : ChunkFacts (toRow data54.row) 1 4096 (toTotals ⟨1334436215110604, 6679514958837, 24635814773528, 1316479915295913, 11254572019⟩) :=
  CleanupSegments208.append_exact join54_05 join54_06 rfl rfl rfl
#print axioms join54_07

theorem join54_08 : ChunkFacts (toRow data54.row) 1 4762 (toTotals ⟨1334588365039837, 6825998444055, 24909957790094, 1316504405693798, 11837677901⟩) :=
  CleanupSegments208.append_exact join54_07 join54_04 rfl rfl rfl
#print axioms join54_08

theorem fact54 : ChunkFacts (toRow data54.row) 1 data54.steps (toTotals data54.total) := join54_08
#print axioms fact54

theorem piece0424 : ChunkFacts (toRow data55.row) 1 512 (toTotals ⟨1270905727926523, 3464855263173, 16753377712308, 1257617205477388, 4032305280⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0424
#print axioms piece0424

theorem piece0425 : ChunkFacts (toRow data55.row) 513 512 (toTotals ⟨66071791320376, 1811643039711, 4023917967216, 63859516392871, 2448090097⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0425
#print axioms piece0425

theorem piece0426 : ChunkFacts (toRow data55.row) 1025 512 (toTotals ⟨17457285743301, 1036957593642, 2092721905117, 16401521431826, 1814064865⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0426
#print axioms piece0426

theorem piece0427 : ChunkFacts (toRow data55.row) 1537 512 (toTotals ⟨5122373032372, 583015698999, 1073554264831, 4631834466540, 1283600647⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0427
#print axioms piece0427

theorem piece0428 : ChunkFacts (toRow data55.row) 2049 512 (toTotals ⟨2601541228273, 423857022951, 785790164659, 2239608086565, 1092193744⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0428
#print axioms piece0428

theorem piece0429 : ChunkFacts (toRow data55.row) 2561 512 (toTotals ⟨635618751182, 235098715077, 398865740319, 471851725940, 678569521⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0429
#print axioms piece0429

theorem piece0430 : ChunkFacts (toRow data55.row) 3073 512 (toTotals ⟨346217535370, 180994470018, 307073108646, 220138896742, 580872618⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0430
#print axioms piece0430

theorem piece0431 : ChunkFacts (toRow data55.row) 3585 512 (toTotals ⟨134674904012, 124221405696, 210752589312, 48143720396, 455689660⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G26.checked0431
#print axioms piece0431

theorem piece0432 : ChunkFacts (toRow data55.row) 4097 512 (toTotals ⟨118930421822, 124221405696, 210752589312, 32399238206, 483608298⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0432
#print axioms piece0432

theorem piece0433 : ChunkFacts (toRow data55.row) 4609 512 (toTotals ⟨106510614196, 124221405696, 210752589312, 19979430580, 511556874⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0433
#print axioms piece0433

theorem piece0434 : ChunkFacts (toRow data55.row) 5121 165 (toTotals ⟨32089265386, 40032288945, 67918314915, 4203239416, 141182724⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0434
#print axioms piece0434

theorem join55_00 : ChunkFacts (toRow data55.row) 1 1024 (toTotals ⟨1336977519246899, 5276498302884, 20777295679524, 1321476721870259, 6480395377⟩) :=
  CleanupSegments208.append_exact piece0424 piece0425 rfl rfl rfl
#print axioms join55_00

theorem join55_01 : ChunkFacts (toRow data55.row) 1025 1024 (toTotals ⟨22579658775673, 1619973292641, 3166276169948, 21033355898366, 3097665512⟩) :=
  CleanupSegments208.append_exact piece0426 piece0427 rfl rfl rfl
#print axioms join55_01

theorem join55_02 : ChunkFacts (toRow data55.row) 2049 1024 (toTotals ⟨3237159979455, 658955738028, 1184655904978, 2711459812505, 1770763265⟩) :=
  CleanupSegments208.append_exact piece0428 piece0429 rfl rfl rfl
#print axioms join55_02

theorem join55_03 : ChunkFacts (toRow data55.row) 3073 1024 (toTotals ⟨480892439382, 305215875714, 517825697958, 268282617138, 1036562278⟩) :=
  CleanupSegments208.append_exact piece0430 piece0431 rfl rfl rfl
#print axioms join55_03

theorem join55_04 : ChunkFacts (toRow data55.row) 4097 1024 (toTotals ⟨225441036018, 248442811392, 421505178624, 52378668786, 995165172⟩) :=
  CleanupSegments208.append_exact piece0432 piece0433 rfl rfl rfl
#print axioms join55_04

theorem join55_05 : ChunkFacts (toRow data55.row) 1 2048 (toTotals ⟨1359557178022572, 6896471595525, 23943571849472, 1342510077768625, 9578060889⟩) :=
  CleanupSegments208.append_exact join55_00 join55_01 rfl rfl rfl
#print axioms join55_05

theorem join55_06 : ChunkFacts (toRow data55.row) 2049 2048 (toTotals ⟨3718052418837, 964171613742, 1702481602936, 2979742429643, 2807325543⟩) :=
  CleanupSegments208.append_exact join55_02 join55_03 rfl rfl rfl
#print axioms join55_06

theorem join55_07 : ChunkFacts (toRow data55.row) 4097 1189 (toTotals ⟨257530301404, 288475100337, 489423493539, 56581908202, 1136347896⟩) :=
  CleanupSegments208.append_exact join55_04 piece0434 rfl rfl rfl
#print axioms join55_07

theorem join55_08 : ChunkFacts (toRow data55.row) 1 4096 (toTotals ⟨1363275230441409, 7860643209267, 25646053452408, 1345489820198268, 12385386432⟩) :=
  CleanupSegments208.append_exact join55_05 join55_06 rfl rfl rfl
#print axioms join55_08

theorem join55_09 : ChunkFacts (toRow data55.row) 1 5285 (toTotals ⟨1363532760742813, 8149118309604, 26135476945947, 1345546402106470, 13521734328⟩) :=
  CleanupSegments208.append_exact join55_08 join55_07 rfl rfl rfl
#print axioms join55_09

theorem fact55 : ChunkFacts (toRow data55.row) 1 data55.steps (toTotals data55.total) := join55_09
#print axioms fact55

theorem piece0435 : ChunkFacts (toRow data56.row) 1 512 (toTotals ⟨1088323003036218, 846526132493, 14795385969145, 1074374143199566, 3185150162⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0435
#print axioms piece0435

theorem piece0436 : ChunkFacts (toRow data56.row) 513 512 (toTotals ⟨37631827086791, 325857552902, 2475974049196, 35481710590497, 1595038644⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0436
#print axioms piece0436

theorem piece0437 : ChunkFacts (toRow data56.row) 1025 512 (toTotals ⟨6085146288027, 146763128443, 988134811725, 5243774604745, 953428888⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0437
#print axioms piece0437

theorem piece0438 : ChunkFacts (toRow data56.row) 1537 512 (toTotals ⟨1335096657305, 80753399077, 503441326182, 912408730200, 601736744⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0438
#print axioms piece0438

theorem piece0439 : ChunkFacts (toRow data56.row) 2049 512 (toTotals ⟨224159135596, 38318573056, 203416375296, 59061333356, 308656357⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0439
#print axioms piece0439

theorem piece0440 : ChunkFacts (toRow data56.row) 2561 486 (toTotals ⟨174801190352, 36372708018, 193086637488, 18087260882, 296259689⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0440
#print axioms piece0440

theorem join56_00 : ChunkFacts (toRow data56.row) 1 1024 (toTotals ⟨1125954830123009, 1172383685395, 17271360018341, 1109855853790063, 4780188806⟩) :=
  CleanupSegments208.append_exact piece0435 piece0436 rfl rfl rfl
#print axioms join56_00

theorem join56_01 : ChunkFacts (toRow data56.row) 1025 1024 (toTotals ⟨7420242945332, 227516527520, 1491576137907, 6156183334945, 1555165632⟩) :=
  CleanupSegments208.append_exact piece0437 piece0438 rfl rfl rfl
#print axioms join56_01

theorem join56_02 : ChunkFacts (toRow data56.row) 2049 998 (toTotals ⟨398960325948, 74691281074, 396503012784, 77148594238, 604916046⟩) :=
  CleanupSegments208.append_exact piece0439 piece0440 rfl rfl rfl
#print axioms join56_02

theorem join56_03 : ChunkFacts (toRow data56.row) 1 2048 (toTotals ⟨1133375073068341, 1399900212915, 18762936156248, 1116012037125008, 6335354438⟩) :=
  CleanupSegments208.append_exact join56_00 join56_01 rfl rfl rfl
#print axioms join56_03

theorem join56_04 : ChunkFacts (toRow data56.row) 1 3046 (toTotals ⟨1133774033394289, 1474591493989, 19159439169032, 1116089185719246, 6940270484⟩) :=
  CleanupSegments208.append_exact join56_03 join56_02 rfl rfl rfl
#print axioms join56_04

theorem fact56 : ChunkFacts (toRow data56.row) 1 data56.steps (toTotals data56.total) := join56_04
#print axioms fact56

theorem piece0441 : ChunkFacts (toRow data57.row) 1 512 (toTotals ⟨1108509704135861, 1320419116090, 15065321863968, 1094764801387983, 3409049505⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0441
#print axioms piece0441

theorem piece0442 : ChunkFacts (toRow data57.row) 513 512 (toTotals ⟨42913305069665, 552663093735, 2746274613213, 40719693550187, 1785865993⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0442
#print axioms piece0442

theorem piece0443 : ChunkFacts (toRow data57.row) 1025 512 (toTotals ⟨8238571080282, 266284147540, 1179666806478, 7325188421344, 1128436052⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0443
#print axioms piece0443

theorem piece0444 : ChunkFacts (toRow data57.row) 1537 512 (toTotals ⟨2118856288007, 157502807335, 637988944152, 1638370151190, 780983613⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0444
#print axioms piece0444

theorem piece0445 : ChunkFacts (toRow data57.row) 2049 512 (toTotals ⟨347045216462, 66795559775, 248667997092, 165172779145, 376379638⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0445
#print axioms piece0445

theorem piece0446 : ChunkFacts (toRow data57.row) 2561 512 (toTotals ⟨183353413858, 57477859840, 203416375296, 37414898402, 343913491⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0446
#print axioms piece0446

theorem piece0447 : ChunkFacts (toRow data57.row) 3073 333 (toTotals ⟨103592487620, 37383061185, 132300103464, 8675445341, 223316954⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G27.checked0447
#print axioms piece0447

theorem join57_00 : ChunkFacts (toRow data57.row) 1 1024 (toTotals ⟨1151423009205526, 1873082209825, 17811596477181, 1135484494938170, 5194915498⟩) :=
  CleanupSegments208.append_exact piece0441 piece0442 rfl rfl rfl
#print axioms join57_00

theorem join57_01 : ChunkFacts (toRow data57.row) 1025 1024 (toTotals ⟨10357427368289, 423786954875, 1817655750630, 8963558572534, 1909419665⟩) :=
  CleanupSegments208.append_exact piece0443 piece0444 rfl rfl rfl
#print axioms join57_01

theorem join57_02 : ChunkFacts (toRow data57.row) 2049 1024 (toTotals ⟨530398630320, 124273419615, 452084372388, 202587677547, 720293129⟩) :=
  CleanupSegments208.append_exact piece0445 piece0446 rfl rfl rfl
#print axioms join57_02

theorem join57_03 : ChunkFacts (toRow data57.row) 1 2048 (toTotals ⟨1161780436573815, 2296869164700, 19629252227811, 1144448053510704, 7104335163⟩) :=
  CleanupSegments208.append_exact join57_00 join57_01 rfl rfl rfl
#print axioms join57_03

theorem join57_04 : ChunkFacts (toRow data57.row) 2049 1357 (toTotals ⟨633991117940, 161656480800, 584384475852, 211263122888, 943610083⟩) :=
  CleanupSegments208.append_exact join57_02 piece0447 rfl rfl rfl
#print axioms join57_04

theorem join57_05 : ChunkFacts (toRow data57.row) 1 3405 (toTotals ⟨1162414427691755, 2458525645500, 20213636703663, 1144659316633592, 8047945246⟩) :=
  CleanupSegments208.append_exact join57_03 join57_04 rfl rfl rfl
#print axioms join57_05

theorem fact57 : ChunkFacts (toRow data57.row) 1 data57.steps (toTotals data57.total) := join57_05
#print axioms fact57

theorem piece0448 : ChunkFacts (toRow data58.row) 1 512 (toTotals ⟨1149421748068499, 1716751913696, 15413450534276, 1135725049447919, 3622875736⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0448
#print axioms piece0448

theorem piece0449 : ChunkFacts (toRow data58.row) 513 512 (toTotals ⟨49953251631188, 771248601893, 3055780965795, 47668719267286, 1971962741⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0449
#print axioms piece0449

theorem piece0450 : ChunkFacts (toRow data58.row) 1025 512 (toTotals ⟨10221581086681, 380616193142, 1359467965556, 9242729314267, 1294579899⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0450
#print axioms piece0450

theorem piece0451 : ChunkFacts (toRow data58.row) 1537 512 (toTotals ⟨2847007057672, 220768368697, 719832251400, 2347943174969, 899171184⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0451
#print axioms piece0451

theorem piece0452 : ChunkFacts (toRow data58.row) 2049 512 (toTotals ⟨738400954281, 117038793349, 363918851070, 491520896560, 530476724⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0452
#print axioms piece0452

theorem piece0453 : ChunkFacts (toRow data58.row) 2561 512 (toTotals ⟨183353413858, 70250717696, 203416375296, 50187756258, 361218067⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0453
#print axioms piece0453

theorem piece0454 : ChunkFacts (toRow data58.row) 3073 512 (toTotals ⟨155191835930, 70250717696, 203416375296, 22026178330, 378381736⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0454
#print axioms piece0454

theorem piece0455 : ChunkFacts (toRow data58.row) 3585 111 (toTotals ⟨30727628473, 15230136063, 44100034488, 1857730048, 74113663⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0455
#print axioms piece0455

theorem join58_00 : ChunkFacts (toRow data58.row) 1 1024 (toTotals ⟨1199374999699687, 2488000515589, 18469231500071, 1183393768715205, 5594838477⟩) :=
  CleanupSegments208.append_exact piece0448 piece0449 rfl rfl rfl
#print axioms join58_00

theorem join58_01 : ChunkFacts (toRow data58.row) 1025 1024 (toTotals ⟨13068588144353, 601384561839, 2079300216956, 11590672489236, 2193751083⟩) :=
  CleanupSegments208.append_exact piece0450 piece0451 rfl rfl rfl
#print axioms join58_01

theorem join58_02 : ChunkFacts (toRow data58.row) 2049 1024 (toTotals ⟨921754368139, 187289511045, 567335226366, 541708652818, 891694791⟩) :=
  CleanupSegments208.append_exact piece0452 piece0453 rfl rfl rfl
#print axioms join58_02

theorem join58_03 : ChunkFacts (toRow data58.row) 3073 623 (toTotals ⟨185919464403, 85480853759, 247516409784, 23883908378, 452495399⟩) :=
  CleanupSegments208.append_exact piece0454 piece0455 rfl rfl rfl
#print axioms join58_03

theorem join58_04 : ChunkFacts (toRow data58.row) 1 2048 (toTotals ⟨1212443587844040, 3089385077428, 20548531717027, 1194984441204441, 7788589560⟩) :=
  CleanupSegments208.append_exact join58_00 join58_01 rfl rfl rfl
#print axioms join58_04

theorem join58_05 : ChunkFacts (toRow data58.row) 2049 1647 (toTotals ⟨1107673832542, 272770364804, 814851636150, 565592561196, 1344190190⟩) :=
  CleanupSegments208.append_exact join58_02 join58_03 rfl rfl rfl
#print axioms join58_05

theorem join58_06 : ChunkFacts (toRow data58.row) 1 3695 (toTotals ⟨1213551261676582, 3362155442232, 21363383353177, 1195550033765637, 9132779750⟩) :=
  CleanupSegments208.append_exact join58_04 join58_05 rfl rfl rfl
#print axioms join58_06

theorem fact58 : ChunkFacts (toRow data58.row) 1 data58.steps (toTotals data58.total) := join58_06
#print axioms fact58

theorem piece0456 : ChunkFacts (toRow data59.row) 1 512 (toTotals ⟨1175594091135749, 2109804169620, 15675348349871, 1162028546955498, 3820966877⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0456
#print axioms piece0456

theorem piece0457 : ChunkFacts (toRow data59.row) 513 512 (toTotals ⟨55694293768572, 1009903955760, 3334739546758, 53369458177574, 2152474848⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0457
#print axioms piece0457

theorem piece0458 : ChunkFacts (toRow data59.row) 1025 512 (toTotals ⟨12130498396143, 517113634380, 1545932976305, 11101679054218, 1469317810⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0458
#print axioms piece0458

theorem piece0459 : ChunkFacts (toRow data59.row) 1537 512 (toTotals ⟨3563673552946, 297068729440, 808429617984, 3052312664402, 1028684032⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0459
#print axioms piece0459

theorem piece0460 : ChunkFacts (toRow data59.row) 2049 512 (toTotals ⟨1104658494844, 176100786120, 470338950006, 810420330958, 690342737⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0460
#print axioms piece0460

theorem piece0461 : ChunkFacts (toRow data59.row) 2561 512 (toTotals ⟨245525434335, 93077211080, 228048826992, 110553818423, 411137861⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0461
#print axioms piece0461

theorem piece0462 : ChunkFacts (toRow data59.row) 3073 512 (toTotals ⟨155191835930, 83023575040, 203416375296, 34799035674, 398832040⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0462
#print axioms piece0462

theorem piece0463 : ChunkFacts (toRow data59.row) 3585 454 (toTotals ⟨120198168994, 73618560680, 180373114032, 13443615642, 358032707⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G28.checked0463
#print axioms piece0463

theorem join59_00 : ChunkFacts (toRow data59.row) 1 1024 (toTotals ⟨1231288384904321, 3119708125380, 19010087896629, 1215398005133072, 5973441725⟩) :=
  CleanupSegments208.append_exact piece0456 piece0457 rfl rfl rfl
#print axioms join59_00

theorem join59_01 : ChunkFacts (toRow data59.row) 1025 1024 (toTotals ⟨15694171949089, 814182363820, 2354362594289, 14153991718620, 2498001842⟩) :=
  CleanupSegments208.append_exact piece0458 piece0459 rfl rfl rfl
#print axioms join59_01

theorem join59_02 : ChunkFacts (toRow data59.row) 2049 1024 (toTotals ⟨1350183929179, 269177997200, 698387776998, 920974149381, 1101480598⟩) :=
  CleanupSegments208.append_exact piece0460 piece0461 rfl rfl rfl
#print axioms join59_02

theorem join59_03 : ChunkFacts (toRow data59.row) 3073 966 (toTotals ⟨275390004924, 156642135720, 383789489328, 48242651316, 756864747⟩) :=
  CleanupSegments208.append_exact piece0462 piece0463 rfl rfl rfl
#print axioms join59_03

theorem join59_04 : ChunkFacts (toRow data59.row) 1 2048 (toTotals ⟨1246982556853410, 3933890489200, 21364450490918, 1229551996851692, 8471443567⟩) :=
  CleanupSegments208.append_exact join59_00 join59_01 rfl rfl rfl
#print axioms join59_04

theorem join59_05 : ChunkFacts (toRow data59.row) 2049 1990 (toTotals ⟨1625573934103, 425820132920, 1082177266326, 969216800697, 1858345345⟩) :=
  CleanupSegments208.append_exact join59_02 join59_03 rfl rfl rfl
#print axioms join59_05

theorem join59_06 : ChunkFacts (toRow data59.row) 1 4038 (toTotals ⟨1248608130787513, 4359710622120, 22446627757244, 1230521213652389, 10329788912⟩) :=
  CleanupSegments208.append_exact join59_04 join59_05 rfl rfl rfl
#print axioms join59_06

theorem fact59 : ChunkFacts (toRow data59.row) 1 data59.steps (toTotals data59.total) := join59_06
#print axioms fact59

theorem piece0464 : ChunkFacts (toRow data60.row) 1 512 (toTotals ⟨1198905549769091, 2500249478104, 15908807717934, 1185496991529261, 4004659843⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0464
#print axioms piece0464

theorem piece0465 : ChunkFacts (toRow data60.row) 513 512 (toTotals ⟨59460230478897, 1247037549320, 3553038268313, 57154229759904, 2325807988⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0465
#print axioms piece0465

theorem piece0466 : ChunkFacts (toRow data60.row) 1025 512 (toTotals ⟨14113068948147, 672820259168, 1729459520205, 13056429687110, 1643099458⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0466
#print axioms piece0466

theorem piece0467 : ChunkFacts (toRow data60.row) 1537 512 (toTotals ⟨4131605691693, 372520894328, 871599937656, 3632526648365, 1130378805⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0467
#print axioms piece0467

theorem piece0468 : ChunkFacts (toRow data60.row) 2049 512 (toTotals ⟨1651703292592, 255768991736, 595199799750, 1312272484578, 874993128⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0468
#print axioms piece0468

theorem piece0469 : ChunkFacts (toRow data60.row) 2561 512 (toTotals ⟨393687138394, 136584757840, 290027253840, 240244642394, 523568352⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0469
#print axioms piece0469

theorem piece0470 : ChunkFacts (toRow data60.row) 3073 512 (toTotals ⟨155191835930, 95796432896, 203416375296, 47571893530, 419282344⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0470
#print axioms piece0470

theorem piece0471 : ChunkFacts (toRow data60.row) 3585 512 (toTotals ⟨134578360780, 95796432896, 203416375296, 26958418380, 442762548⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0471
#print axioms piece0471

theorem piece0472 : ChunkFacts (toRow data60.row) 4097 357 (toTotals ⟨84299526109, 66795559656, 141835246056, 9259839709, 304901471⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0472
#print axioms piece0472

theorem join60_00 : ChunkFacts (toRow data60.row) 1 1024 (toTotals ⟨1258365780247988, 3747287027424, 19461845986247, 1242651221289165, 6330467831⟩) :=
  CleanupSegments208.append_exact piece0464 piece0465 rfl rfl rfl
#print axioms join60_00

theorem join60_01 : ChunkFacts (toRow data60.row) 1025 1024 (toTotals ⟨18244674639840, 1045341153496, 2601059457861, 16688956335475, 2773478263⟩) :=
  CleanupSegments208.append_exact piece0466 piece0467 rfl rfl rfl
#print axioms join60_01

theorem join60_02 : ChunkFacts (toRow data60.row) 2049 1024 (toTotals ⟨2045390430986, 392353749576, 885227053590, 1552517126972, 1398561480⟩) :=
  CleanupSegments208.append_exact piece0468 piece0469 rfl rfl rfl
#print axioms join60_02

theorem join60_03 : ChunkFacts (toRow data60.row) 3073 1024 (toTotals ⟨289770196710, 191592865792, 406832750592, 74530311910, 862044892⟩) :=
  CleanupSegments208.append_exact piece0470 piece0471 rfl rfl rfl
#print axioms join60_03

theorem join60_04 : ChunkFacts (toRow data60.row) 1 2048 (toTotals ⟨1276610454887828, 4792628180920, 22062905444108, 1259340177624640, 9103946094⟩) :=
  CleanupSegments208.append_exact join60_00 join60_01 rfl rfl rfl
#print axioms join60_04

theorem join60_05 : ChunkFacts (toRow data60.row) 2049 2048 (toTotals ⟨2335160627696, 583946615368, 1292059804182, 1627047438882, 2260606372⟩) :=
  CleanupSegments208.append_exact join60_02 join60_03 rfl rfl rfl
#print axioms join60_05

theorem join60_06 : ChunkFacts (toRow data60.row) 1 4096 (toTotals ⟨1278945615515524, 5376574796288, 23354965248290, 1260967225063522, 11364552466⟩) :=
  CleanupSegments208.append_exact join60_04 join60_05 rfl rfl rfl
#print axioms join60_06

theorem join60_07 : ChunkFacts (toRow data60.row) 1 4453 (toTotals ⟨1279029915041633, 5443370355944, 23496800494346, 1260976484903231, 11669453937⟩) :=
  CleanupSegments208.append_exact join60_06 piece0472 rfl rfl rfl
#print axioms join60_07

theorem fact60 : ChunkFacts (toRow data60.row) 1 data60.steps (toTotals data60.total) := join60_07
#print axioms fact60

theorem piece0473 : ChunkFacts (toRow data61.row) 1 512 (toTotals ⟨1241382001357469, 2923163281404, 16277156341529, 1228028008297344, 4176416887⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0473
#print axioms piece0473

theorem piece0474 : ChunkFacts (toRow data61.row) 513 512 (toTotals ⟨63743499558307, 1489958839188, 3789942801507, 61443515595988, 2487045106⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0474
#print axioms piece0474

theorem piece0475 : ChunkFacts (toRow data61.row) 1025 512 (toTotals ⟨16143125824845, 826576858464, 1903727302464, 15065975380845, 1805189922⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0475
#print axioms piece0475

theorem piece0476 : ChunkFacts (toRow data61.row) 1537 512 (toTotals ⟨4581393281378, 457777223928, 955429732944, 4083740772362, 1244417734⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0476
#print axioms piece0476

theorem piece0477 : ChunkFacts (toRow data61.row) 2049 512 (toTotals ⟨2256142444539, 336992225244, 708389312514, 1884745357269, 1055151546⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0477
#print axioms piece0477

theorem piece0478 : ChunkFacts (toRow data61.row) 2561 512 (toTotals ⟨494515678127, 174213130632, 332935395504, 335793413255, 616315252⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0478
#print axioms piece0478

theorem piece0479 : ChunkFacts (toRow data61.row) 3073 512 (toTotals ⟨223599050022, 123487589016, 235994779152, 111091859886, 487192908⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G29.checked0479
#print axioms piece0479

theorem piece0480 : ChunkFacts (toRow data61.row) 3585 512 (toTotals ⟨134578360780, 106440480768, 203416375296, 37602466252, 462425908⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0480
#print axioms piece0480

theorem piece0481 : ChunkFacts (toRow data61.row) 4097 512 (toTotals ⟨118833878590, 106440480768, 203416375296, 21857984062, 488504295⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0481
#print axioms piece0481

theorem piece0482 : ChunkFacts (toRow data61.row) 4609 261 (toTotals ⟨55631434973, 54259698204, 103694675688, 6196457489, 236184255⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0482
#print axioms piece0482

theorem join61_00 : ChunkFacts (toRow data61.row) 1 1024 (toTotals ⟨1305125500915776, 4413122120592, 20067099143036, 1289471523893332, 6663461993⟩) :=
  CleanupSegments208.append_exact piece0473 piece0474 rfl rfl rfl
#print axioms join61_00

theorem join61_01 : ChunkFacts (toRow data61.row) 1025 1024 (toTotals ⟨20724519106223, 1284354082392, 2859157035408, 19149716153207, 3049607656⟩) :=
  CleanupSegments208.append_exact piece0475 piece0476 rfl rfl rfl
#print axioms join61_01

theorem join61_02 : ChunkFacts (toRow data61.row) 2049 1024 (toTotals ⟨2750658122666, 511205355876, 1041324708018, 2220538770524, 1671466798⟩) :=
  CleanupSegments208.append_exact piece0477 piece0478 rfl rfl rfl
#print axioms join61_02

theorem join61_03 : ChunkFacts (toRow data61.row) 3073 1024 (toTotals ⟨358177410802, 229928069784, 439411154448, 148694326138, 949618816⟩) :=
  CleanupSegments208.append_exact piece0479 piece0480 rfl rfl rfl
#print axioms join61_03

theorem join61_04 : ChunkFacts (toRow data61.row) 4097 773 (toTotals ⟨174465313563, 160700178972, 307111050984, 28054441551, 724688550⟩) :=
  CleanupSegments208.append_exact piece0481 piece0482 rfl rfl rfl
#print axioms join61_04

theorem join61_05 : ChunkFacts (toRow data61.row) 1 2048 (toTotals ⟨1325850020021999, 5697476202984, 22926256178444, 1308621240046539, 9713069649⟩) :=
  CleanupSegments208.append_exact join61_00 join61_01 rfl rfl rfl
#print axioms join61_05

theorem join61_06 : ChunkFacts (toRow data61.row) 2049 2048 (toTotals ⟨3108835533468, 741133425660, 1480735862466, 2369233096662, 2621085614⟩) :=
  CleanupSegments208.append_exact join61_02 join61_03 rfl rfl rfl
#print axioms join61_06

theorem join61_07 : ChunkFacts (toRow data61.row) 1 4096 (toTotals ⟨1328958855555467, 6438609628644, 24406992040910, 1310990473143201, 12334155263⟩) :=
  CleanupSegments208.append_exact join61_05 join61_06 rfl rfl rfl
#print axioms join61_07

theorem join61_08 : ChunkFacts (toRow data61.row) 1 4869 (toTotals ⟨1329133320869030, 6599309807616, 24714103091894, 1311018527584752, 13058843813⟩) :=
  CleanupSegments208.append_exact join61_07 join61_04 rfl rfl rfl
#print axioms join61_08

theorem fact61 : ChunkFacts (toRow data61.row) 1 data61.steps (toTotals data61.total) := join61_08
#print axioms fact61

theorem piece0483 : ChunkFacts (toRow data62.row) 1 512 (toTotals ⟨1252903504725383, 3281568346350, 16418413874687, 1239766659197046, 4374119050⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0483
#print axioms piece0483

theorem piece0484 : ChunkFacts (toRow data62.row) 513 512 (toTotals ⟨67811240923540, 1747349389161, 4021718932742, 65536871379959, 2671516464⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0484
#print axioms piece0484

theorem piece0485 : ChunkFacts (toRow data62.row) 1025 512 (toTotals ⟨18229583895185, 1011226148262, 2102800274505, 17138009768942, 1992602381⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0485
#print axioms piece0485

theorem piece0486 : ChunkFacts (toRow data62.row) 1537 512 (toTotals ⟨5262661901123, 561868531497, 1061147363616, 4763383069004, 1386827297⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0486
#print axioms piece0486

theorem piece0487 : ChunkFacts (toRow data62.row) 2049 512 (toTotals ⟨2860832002282, 424888779618, 815769067506, 2469951714394, 1236804829⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0487
#print axioms piece0487

theorem piece0488 : ChunkFacts (toRow data62.row) 2561 512 (toTotals ⟨673596345045, 229824124605, 399284096040, 504136373610, 740268315⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0488
#print axioms piece0488

theorem piece0489 : ChunkFacts (toRow data62.row) 3073 512 (toTotals ⟨373535482992, 179285685264, 311481324672, 241339843584, 642588893⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0489
#print axioms piece0489

theorem piece0490 : ChunkFacts (toRow data62.row) 3585 512 (toTotals ⟨134578360780, 117084529152, 203416375296, 48246514636, 482089268⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0490
#print axioms piece0490

theorem piece0491 : ChunkFacts (toRow data62.row) 4097 512 (toTotals ⟨118833878590, 117084529152, 203416375296, 32502032446, 510789095⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0491
#print axioms piece0491

theorem piece0492 : ChunkFacts (toRow data62.row) 4609 512 (toTotals ⟨106414070964, 117084529152, 203416375296, 20082224820, 539475220⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0492
#print axioms piece0492

theorem piece0493 : ChunkFacts (toRow data62.row) 5121 251 (toTotals ⟨48376916486, 57398860971, 99721699608, 6054077849, 244338217⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0493
#print axioms piece0493

theorem join62_00 : ChunkFacts (toRow data62.row) 1 1024 (toTotals ⟨1320714745648923, 5028917735511, 20440132807429, 1305303530577005, 7045635514⟩) :=
  CleanupSegments208.append_exact piece0483 piece0484 rfl rfl rfl
#print axioms join62_00

theorem join62_01 : ChunkFacts (toRow data62.row) 1025 1024 (toTotals ⟨23492245796308, 1573094679759, 3163947638121, 21901392837946, 3379429678⟩) :=
  CleanupSegments208.append_exact piece0485 piece0486 rfl rfl rfl
#print axioms join62_01

theorem join62_02 : ChunkFacts (toRow data62.row) 2049 1024 (toTotals ⟨3534428347327, 654712904223, 1215053163546, 2974088088004, 1977073144⟩) :=
  CleanupSegments208.append_exact piece0487 piece0488 rfl rfl rfl
#print axioms join62_02

theorem join62_03 : ChunkFacts (toRow data62.row) 3073 1024 (toTotals ⟨508113843772, 296370214416, 514897699968, 289586358220, 1124678161⟩) :=
  CleanupSegments208.append_exact piece0489 piece0490 rfl rfl rfl
#print axioms join62_03

theorem join62_04 : ChunkFacts (toRow data62.row) 4097 1024 (toTotals ⟨225247949554, 234169058304, 406832750592, 52584257266, 1050264315⟩) :=
  CleanupSegments208.append_exact piece0491 piece0492 rfl rfl rfl
#print axioms join62_04

theorem join62_05 : ChunkFacts (toRow data62.row) 1 2048 (toTotals ⟨1344206991445231, 6602012415270, 23604080445550, 1327204923414951, 10425065192⟩) :=
  CleanupSegments208.append_exact join62_00 join62_01 rfl rfl rfl
#print axioms join62_05

theorem join62_06 : ChunkFacts (toRow data62.row) 2049 2048 (toTotals ⟨4042542191099, 951083118639, 1729950863514, 3263674446224, 3101751305⟩) :=
  CleanupSegments208.append_exact join62_02 join62_03 rfl rfl rfl
#print axioms join62_06

theorem join62_07 : ChunkFacts (toRow data62.row) 4097 1275 (toTotals ⟨273624866040, 291567919275, 506554450200, 58638335115, 1294602532⟩) :=
  CleanupSegments208.append_exact join62_04 piece0493 rfl rfl rfl
#print axioms join62_07

theorem join62_08 : ChunkFacts (toRow data62.row) 1 4096 (toTotals ⟨1348249533636330, 7553095533909, 25334031309064, 1330468597861175, 13526816497⟩) :=
  CleanupSegments208.append_exact join62_05 join62_06 rfl rfl rfl
#print axioms join62_08

theorem join62_09 : ChunkFacts (toRow data62.row) 1 5371 (toTotals ⟨1348523158502370, 7844663453184, 25840585759264, 1330527236196290, 14821419029⟩) :=
  CleanupSegments208.append_exact join62_08 join62_07 rfl rfl rfl
#print axioms join62_09

theorem fact62 : ChunkFacts (toRow data62.row) 1 data62.steps (toTotals data62.total) := join62_09
#print axioms fact62

theorem piece0494 : ChunkFacts (toRow data63.row) 1 512 (toTotals ⟨1086563296440127, 835091105450, 14669507909459, 1072728879636118, 3470854929⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0494
#print axioms piece0494

theorem piece0495 : ChunkFacts (toRow data63.row) 513 512 (toTotals ⟨39762884019031, 330535623572, 2529313517104, 37564106125499, 1766138626⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G30.checked0495
#print axioms piece0495

theorem piece0496 : ChunkFacts (toRow data63.row) 1025 512 (toTotals ⟨6710940181833, 151410404796, 1023498227952, 5838852358677, 1071553626⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0496
#print axioms piece0496

theorem piece0497 : ChunkFacts (toRow data63.row) 1537 512 (toTotals ⟨1535342065642, 85770055896, 531259970040, 1089852151498, 694689512⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0497
#print axioms piece0497

theorem piece0498 : ChunkFacts (toRow data63.row) 2049 512 (toTotals ⟨266416685144, 39457143061, 212737134230, 93136693975, 347473242⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0498
#print axioms piece0498

theorem piece0499 : ChunkFacts (toRow data63.row) 2561 512 (toTotals ⟨183271695074, 37342065152, 197126310400, 23487449826, 341322554⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0499
#print axioms piece0499

theorem piece0500 : ChunkFacts (toRow data63.row) 3073 79 (toTotals ⟨25538592743, 5761763959, 30415973675, 884383027, 47758768⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0500
#print axioms piece0500

theorem join63_00 : ChunkFacts (toRow data63.row) 1 1024 (toTotals ⟨1126326180459158, 1165626729022, 17198821426563, 1110292985761617, 5236993555⟩) :=
  CleanupSegments208.append_exact piece0494 piece0495 rfl rfl rfl
#print axioms join63_00

theorem join63_01 : ChunkFacts (toRow data63.row) 1025 1024 (toTotals ⟨8246282247475, 237180460692, 1554758197992, 6928704510175, 1766243138⟩) :=
  CleanupSegments208.append_exact piece0496 piece0497 rfl rfl rfl
#print axioms join63_01

theorem join63_02 : ChunkFacts (toRow data63.row) 2049 1024 (toTotals ⟨449688380218, 76799208213, 409863444630, 116624143801, 688795796⟩) :=
  CleanupSegments208.append_exact piece0498 piece0499 rfl rfl rfl
#print axioms join63_02

theorem join63_03 : ChunkFacts (toRow data63.row) 1 2048 (toTotals ⟨1134572462706633, 1402807189714, 18753579624555, 1117221690271792, 7003236693⟩) :=
  CleanupSegments208.append_exact join63_00 join63_01 rfl rfl rfl
#print axioms join63_03

theorem join63_04 : ChunkFacts (toRow data63.row) 2049 1103 (toTotals ⟨475226972961, 82560972172, 440279418305, 117508526828, 736554564⟩) :=
  CleanupSegments208.append_exact join63_02 piece0500 rfl rfl rfl
#print axioms join63_04

theorem join63_05 : ChunkFacts (toRow data63.row) 1 3151 (toTotals ⟨1135047689679594, 1485368161886, 19193859042860, 1117339198798620, 7739791257⟩) :=
  CleanupSegments208.append_exact join63_03 join63_04 rfl rfl rfl
#print axioms join63_05

theorem fact63 : ChunkFacts (toRow data63.row) 1 data63.steps (toTotals data63.total) := join63_05
#print axioms fact63

theorem piece0501 : ChunkFacts (toRow data64.row) 1 512 (toTotals ⟨1107525202783439, 1256504057492, 14932061360926, 1093849645480005, 3688937001⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0501
#print axioms piece0501

theorem piece0502 : ChunkFacts (toRow data64.row) 513 512 (toTotals ⟨44308440321315, 532771232308, 2768024723675, 42073186829948, 1951483060⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0502
#print axioms piece0502

theorem piece0503 : ChunkFacts (toRow data64.row) 1025 512 (toTotals ⟨8699492886803, 260949175008, 1202782069131, 7757659992680, 1249063672⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0503
#print axioms piece0503

theorem piece0504 : ChunkFacts (toRow data64.row) 1537 512 (toTotals ⟨2185259888835, 150214674772, 626358014315, 1709116549292, 842383776⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0504
#print axioms piece0504

theorem piece0505 : ChunkFacts (toRow data64.row) 2049 512 (toTotals ⟨459480024641, 70515391952, 277729353730, 252266062863, 446019419⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0505
#print axioms piece0505

theorem piece0506 : ChunkFacts (toRow data64.row) 2561 512 (toTotals ⟨183271695074, 54047725568, 197126310400, 40193110242, 365837370⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0506
#print axioms piece0506

theorem piece0507 : ChunkFacts (toRow data64.row) 3073 412 (toTotals ⟨126623753974, 43491529168, 158625077900, 11490205242, 296744761⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0507
#print axioms piece0507

theorem join64_00 : ChunkFacts (toRow data64.row) 1 1024 (toTotals ⟨1151833643104754, 1789275289800, 17700086084601, 1135922832309953, 5640420061⟩) :=
  CleanupSegments208.append_exact piece0501 piece0502 rfl rfl rfl
#print axioms join64_00

theorem join64_01 : ChunkFacts (toRow data64.row) 1025 1024 (toTotals ⟨10884752775638, 411163849780, 1829140083446, 9466776541972, 2091447448⟩) :=
  CleanupSegments208.append_exact piece0503 piece0504 rfl rfl rfl
#print axioms join64_01

theorem join64_02 : ChunkFacts (toRow data64.row) 2049 1024 (toTotals ⟨642751719715, 124563117520, 474855664130, 292459173105, 811856789⟩) :=
  CleanupSegments208.append_exact piece0505 piece0506 rfl rfl rfl
#print axioms join64_02

theorem join64_03 : ChunkFacts (toRow data64.row) 1 2048 (toTotals ⟨1162718395880392, 2200439139580, 19529226168047, 1145389608851925, 7731867509⟩) :=
  CleanupSegments208.append_exact join64_00 join64_01 rfl rfl rfl
#print axioms join64_03

theorem join64_04 : ChunkFacts (toRow data64.row) 2049 1436 (toTotals ⟨769375473689, 168054646688, 633480742030, 303949378347, 1108601550⟩) :=
  CleanupSegments208.append_exact join64_02 piece0507 rfl rfl rfl
#print axioms join64_04

theorem join64_05 : ChunkFacts (toRow data64.row) 1 3484 (toTotals ⟨1163487771354081, 2368493786268, 20162706910077, 1145693558230272, 8840469059⟩) :=
  CleanupSegments208.append_exact join64_03 join64_04 rfl rfl rfl
#print axioms join64_05

theorem fact64 : ChunkFacts (toRow data64.row) 1 data64.steps (toTotals data64.total) := join64_05
#print axioms fact64

theorem piece0508 : ChunkFacts (toRow data65.row) 1 512 (toTotals ⟨1148487754259869, 1650597582178, 15269845507527, 1134868506334520, 3921458676⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0508
#print axioms piece0508

theorem piece0509 : ChunkFacts (toRow data65.row) 513 512 (toTotals ⟨51495081695878, 753059859980, 3084426426527, 49163715129331, 2159237078⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0509
#print axioms piece0509

theorem piece0510 : ChunkFacts (toRow data65.row) 1025 512 (toTotals ⟨10751460204479, 377704546756, 1386539896105, 9742624855130, 1434697600⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0510
#print axioms piece0510

theorem piece0511 : ChunkFacts (toRow data65.row) 1537 512 (toTotals ⟨2915560445407, 214041277360, 709905688840, 2419696033927, 973036194⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G31.checked0511
#print axioms piece0511

theorem piece0512 : ChunkFacts (toRow data65.row) 2049 512 (toTotals ⟨891468715481, 123987325300, 399945812485, 615510228296, 626329724⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0512
#print axioms piece0512

theorem piece0513 : ChunkFacts (toRow data65.row) 2561 512 (toTotals ⟨183271695074, 66822642688, 197126310400, 52968027362, 384583994⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0513
#print axioms piece0513

theorem piece0514 : ChunkFacts (toRow data65.row) 3073 512 (toTotals ⟨155110117146, 66822642688, 197126310400, 24806449434, 402269742⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0514
#print axioms piece0514

theorem piece0515 : ChunkFacts (toRow data65.row) 3585 206 (toTotals ⟨56274319618, 26885672644, 79312538950, 3847453312, 156589880⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0515
#print axioms piece0515

theorem join65_00 : ChunkFacts (toRow data65.row) 1 1024 (toTotals ⟨1199982835955747, 2403657442158, 18354271934054, 1184032221463851, 6080695754⟩) :=
  CleanupSegments208.append_exact piece0508 piece0509 rfl rfl rfl
#print axioms join65_00

theorem join65_01 : ChunkFacts (toRow data65.row) 1025 1024 (toTotals ⟨13667020649886, 591745824116, 2096445584945, 12162320889057, 2407733794⟩) :=
  CleanupSegments208.append_exact piece0510 piece0511 rfl rfl rfl
#print axioms join65_01

theorem join65_02 : ChunkFacts (toRow data65.row) 2049 1024 (toTotals ⟨1074740410555, 190809967988, 597072122885, 668478255658, 1010913718⟩) :=
  CleanupSegments208.append_exact piece0512 piece0513 rfl rfl rfl
#print axioms join65_02

theorem join65_03 : ChunkFacts (toRow data65.row) 3073 718 (toTotals ⟨211384436764, 93708315332, 276438849350, 28653902746, 558859622⟩) :=
  CleanupSegments208.append_exact piece0514 piece0515 rfl rfl rfl
#print axioms join65_03

theorem join65_04 : ChunkFacts (toRow data65.row) 1 2048 (toTotals ⟨1213649856605633, 2995403266274, 20450717518999, 1196194542352908, 8488429548⟩) :=
  CleanupSegments208.append_exact join65_00 join65_01 rfl rfl rfl
#print axioms join65_04

theorem join65_05 : ChunkFacts (toRow data65.row) 2049 1742 (toTotals ⟨1286124847319, 284518283320, 873510972235, 697132158404, 1569773340⟩) :=
  CleanupSegments208.append_exact join65_02 join65_03 rfl rfl rfl
#print axioms join65_05

theorem join65_06 : ChunkFacts (toRow data65.row) 1 3790 (toTotals ⟨1214935981452952, 3279921549594, 21324228491234, 1196891674511312, 10058202888⟩) :=
  CleanupSegments208.append_exact join65_04 join65_05 rfl rfl rfl
#print axioms join65_06

theorem fact65 : ChunkFacts (toRow data65.row) 1 data65.steps (toTotals data65.total) := join65_06
#print axioms fact65

theorem piece0516 : ChunkFacts (toRow data66.row) 1 512 (toTotals ⟨1173755147084335, 2042796749760, 15512560129319, 1160285383704776, 4145145818⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0516
#print axioms piece0516

theorem piece0517 : ChunkFacts (toRow data66.row) 513 512 (toTotals ⟨57620812467510, 997301457360, 3373021683696, 55245092241174, 2364383728⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0517
#print axioms piece0517

theorem piece0518 : ChunkFacts (toRow data66.row) 1025 512 (toTotals ⟨12806986445648, 520648882416, 1582539689042, 11745095639022, 1631517998⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0518
#print axioms piece0518

theorem piece0519 : ChunkFacts (toRow data66.row) 1537 512 (toTotals ⟨3724311381490, 292738681872, 803463683815, 3213586379547, 1120012404⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0519
#print axioms piece0519

theorem piece0520 : ChunkFacts (toRow data66.row) 2049 512 (toTotals ⟨1296440559370, 185468532912, 506686914730, 975222177552, 801764683⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0520
#print axioms piece0520

theorem piece0521 : ChunkFacts (toRow data66.row) 2561 512 (toTotals ⟨282632838082, 95299422192, 236012555225, 141919705049, 461529574⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0521
#print axioms piece0521

theorem piece0522 : ChunkFacts (toRow data66.row) 3073 512 (toTotals ⟨155110117146, 79597559808, 197126310400, 37581366554, 424424238⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0522
#print axioms piece0522

theorem piece0523 : ChunkFacts (toRow data66.row) 3585 512 (toTotals ⟨134496641996, 79597559808, 197126310400, 16967891404, 445544292⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0523
#print axioms piece0523

theorem piece0524 : ChunkFacts (toRow data66.row) 4097 59 (toTotals ⟨14413046604, 9172375056, 22715727175, 869694485, 39177203⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0524
#print axioms piece0524

theorem join66_00 : ChunkFacts (toRow data66.row) 1 1024 (toTotals ⟨1231375959551845, 3040098207120, 18885581813015, 1215530475945950, 6509529546⟩) :=
  CleanupSegments208.append_exact piece0516 piece0517 rfl rfl rfl
#print axioms join66_00

theorem join66_01 : ChunkFacts (toRow data66.row) 1025 1024 (toTotals ⟨16531297827138, 813387564288, 2386003372857, 14958682018569, 2751530402⟩) :=
  CleanupSegments208.append_exact piece0518 piece0519 rfl rfl rfl
#print axioms join66_01

theorem join66_02 : ChunkFacts (toRow data66.row) 2049 1024 (toTotals ⟨1579073397452, 280767955104, 742699469955, 1117141882601, 1263294257⟩) :=
  CleanupSegments208.append_exact piece0520 piece0521 rfl rfl rfl
#print axioms join66_02

theorem join66_03 : ChunkFacts (toRow data66.row) 3073 1024 (toTotals ⟨289606759142, 159195119616, 394252620800, 54549257958, 869968530⟩) :=
  CleanupSegments208.append_exact piece0522 piece0523 rfl rfl rfl
#print axioms join66_03

theorem join66_04 : ChunkFacts (toRow data66.row) 1 2048 (toTotals ⟨1247907257378983, 3853485771408, 21271585185872, 1230489157964519, 9261059948⟩) :=
  CleanupSegments208.append_exact join66_00 join66_01 rfl rfl rfl
#print axioms join66_04

theorem join66_05 : ChunkFacts (toRow data66.row) 2049 2048 (toTotals ⟨1868680156594, 439963074720, 1136952090755, 1171691140559, 2133262787⟩) :=
  CleanupSegments208.append_exact join66_02 join66_03 rfl rfl rfl
#print axioms join66_05

theorem join66_06 : ChunkFacts (toRow data66.row) 1 4096 (toTotals ⟨1249775937535577, 4293448846128, 22408537276627, 1231660849105078, 11394322735⟩) :=
  CleanupSegments208.append_exact join66_04 join66_05 rfl rfl rfl
#print axioms join66_06

theorem join66_07 : ChunkFacts (toRow data66.row) 1 4155 (toTotals ⟨1249790350582181, 4302621221184, 22431253003802, 1231661718799563, 11433499938⟩) :=
  CleanupSegments208.append_exact join66_06 piece0524 rfl rfl rfl
#print axioms join66_07

theorem fact66 : ChunkFacts (toRow data66.row) 1 data66.steps (toTotals data66.total) := join66_07
#print axioms fact66

theorem piece0525 : ChunkFacts (toRow data67.row) 1 512 (toTotals ⟨1190181459596927, 2335339656228, 15697950693923, 1176818848559232, 4308846962⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0525
#print axioms piece0525

theorem piece0526 : ChunkFacts (toRow data67.row) 513 512 (toTotals ⟨60087778808388, 1177887266592, 3537935296392, 57727730778588, 2522468138⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0526
#print axioms piece0526

theorem piece0527 : ChunkFacts (toRow data67.row) 1025 512 (toTotals ⟨14598290826929, 643960609716, 1732184711031, 13510066725614, 1787749032⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G32.checked0527
#print axioms piece0527

theorem piece0528 : ChunkFacts (toRow data67.row) 1537 512 (toTotals ⟨4068627059440, 349663450136, 849280150490, 3569010359086, 1201319307⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0528
#print axioms piece0528

theorem piece0529 : ChunkFacts (toRow data67.row) 2049 512 (toTotals ⟨1806475758442, 251855492056, 615124923145, 1443206327353, 977348927⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0529
#print axioms piece0529

theorem piece0530 : ChunkFacts (toRow data67.row) 2561 512 (toTotals ⟨404541797207, 129944858592, 286449169800, 248037485999, 561185010⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0530
#print axioms piece0530

theorem piece0531 : ChunkFacts (toRow data67.row) 3073 512 (toTotals ⟨155110117146, 89424418816, 197126310400, 47408225562, 441466158⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0531
#print axioms piece0531

theorem piece0532 : ChunkFacts (toRow data67.row) 3585 512 (toTotals ⟨134496641996, 89424418816, 197126310400, 26794750412, 465207652⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0532
#print axioms piece0532

theorem piece0533 : ChunkFacts (toRow data67.row) 4097 392 (toTotals ⟨92137988533, 68465570656, 150924831400, 9678727789, 354620066⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0533
#print axioms piece0533

theorem join67_00 : ChunkFacts (toRow data67.row) 1 1024 (toTotals ⟨1250269238405315, 3513226922820, 19235885990315, 1234546579337820, 6831315100⟩) :=
  CleanupSegments208.append_exact piece0525 piece0526 rfl rfl rfl
#print axioms join67_00

theorem join67_01 : ChunkFacts (toRow data67.row) 1025 1024 (toTotals ⟨18666917886369, 993624059852, 2581464861521, 17079077084700, 2989068339⟩) :=
  CleanupSegments208.append_exact piece0527 piece0528 rfl rfl rfl
#print axioms join67_01

theorem join67_02 : ChunkFacts (toRow data67.row) 2049 1024 (toTotals ⟨2211017555649, 381800350648, 901574092945, 1691243813352, 1538533937⟩) :=
  CleanupSegments208.append_exact piece0529 piece0530 rfl rfl rfl
#print axioms join67_02

theorem join67_03 : ChunkFacts (toRow data67.row) 3073 1024 (toTotals ⟨289606759142, 178848837632, 394252620800, 74202975974, 906673810⟩) :=
  CleanupSegments208.append_exact piece0531 piece0532 rfl rfl rfl
#print axioms join67_03

theorem join67_04 : ChunkFacts (toRow data67.row) 1 2048 (toTotals ⟨1268936156291684, 4506850982672, 21817350851836, 1251625656422520, 9820383439⟩) :=
  CleanupSegments208.append_exact join67_00 join67_01 rfl rfl rfl
#print axioms join67_04

theorem join67_05 : ChunkFacts (toRow data67.row) 2049 2048 (toTotals ⟨2500624314791, 560649188280, 1295826713745, 1765446789326, 2445207747⟩) :=
  CleanupSegments208.append_exact join67_02 join67_03 rfl rfl rfl
#print axioms join67_05

theorem join67_06 : ChunkFacts (toRow data67.row) 1 4096 (toTotals ⟨1271436780606475, 5067500170952, 23113177565581, 1253391103211846, 12265591186⟩) :=
  CleanupSegments208.append_exact join67_04 join67_05 rfl rfl rfl
#print axioms join67_06

theorem join67_07 : ChunkFacts (toRow data67.row) 1 4488 (toTotals ⟨1271528918595008, 5135965741608, 23264102396981, 1253400781939635, 12620211252⟩) :=
  CleanupSegments208.append_exact join67_06 piece0533 rfl rfl rfl
#print axioms join67_07

theorem fact67 : ChunkFacts (toRow data67.row) 1 data67.steps (toTotals data67.total) := join67_07
#print axioms fact67

theorem piece0534 : ChunkFacts (toRow data68.row) 1 512 (toTotals ⟨1214611091429633, 2680366051704, 15901836109662, 1201389621371675, 4475339548⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0534
#print axioms piece0534

theorem piece0535 : ChunkFacts (toRow data68.row) 513 512 (toTotals ⟨64939348284505, 1406382852760, 3766949896236, 62578781241029, 2674960139⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0535
#print axioms piece0535

theorem piece0536 : ChunkFacts (toRow data68.row) 1025 512 (toTotals ⟨16458575996431, 783542314384, 1889287564361, 15352830746454, 1947495374⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0536
#print axioms piece0536

theorem piece0537 : ChunkFacts (toRow data68.row) 1537 512 (toTotals ⟨4532731415351, 428214985768, 928977701765, 4031968699354, 1317139940⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0537
#print axioms piece0537

theorem piece0538 : ChunkFacts (toRow data68.row) 2049 512 (toTotals ⟨2366507841690, 324699004600, 714796771295, 1976410074995, 1152628792⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0538
#print axioms piece0538

theorem piece0539 : ChunkFacts (toRow data68.row) 2561 512 (toTotals ⟨494696569843, 163027977832, 323795365325, 333929182350, 650304908⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0539
#print axioms piece0539

theorem piece0540 : ChunkFacts (toRow data68.row) 3073 512 (toTotals ⟨225387383018, 115728540744, 229852358025, 111263565737, 514309784⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0540
#print axioms piece0540

theorem piece0541 : ChunkFacts (toRow data68.row) 3585 512 (toTotals ⟨134496641996, 99251277824, 197126310400, 36621609420, 484871012⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0541
#print axioms piece0541

theorem piece0542 : ChunkFacts (toRow data68.row) 4097 512 (toTotals ⟨118752159806, 99251277824, 197126310400, 20877127230, 511200362⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0542
#print axioms piece0542

theorem piece0543 : ChunkFacts (toRow data68.row) 4609 270 (toTotals ⟨57453584473, 52339541040, 103953327750, 5839797763, 257997658⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G33.checked0543
#print axioms piece0543

theorem join68_00 : ChunkFacts (toRow data68.row) 1 1024 (toTotals ⟨1279550439714138, 4086748904464, 19668786005898, 1263968402612704, 7150299687⟩) :=
  CleanupSegments208.append_exact piece0534 piece0535 rfl rfl rfl
#print axioms join68_00

theorem join68_01 : ChunkFacts (toRow data68.row) 1025 1024 (toTotals ⟨20991307411782, 1211757300152, 2818265266126, 19384799445808, 3264635314⟩) :=
  CleanupSegments208.append_exact piece0536 piece0537 rfl rfl rfl
#print axioms join68_01

theorem join68_02 : ChunkFacts (toRow data68.row) 2049 1024 (toTotals ⟨2861204411533, 487726982432, 1038592136620, 2310339257345, 1802933700⟩) :=
  CleanupSegments208.append_exact piece0538 piece0539 rfl rfl rfl
#print axioms join68_02

theorem join68_03 : ChunkFacts (toRow data68.row) 3073 1024 (toTotals ⟨359884025014, 214979818568, 426978668425, 147885175157, 999180796⟩) :=
  CleanupSegments208.append_exact piece0540 piece0541 rfl rfl rfl
#print axioms join68_03

theorem join68_04 : ChunkFacts (toRow data68.row) 4097 782 (toTotals ⟨176205744279, 151590818864, 301079638150, 26716924993, 769198020⟩) :=
  CleanupSegments208.append_exact piece0542 piece0543 rfl rfl rfl
#print axioms join68_04

theorem join68_05 : ChunkFacts (toRow data68.row) 1 2048 (toTotals ⟨1300541747125920, 5298506204616, 22487051272024, 1283353202058512, 10414935001⟩) :=
  CleanupSegments208.append_exact join68_00 join68_01 rfl rfl rfl
#print axioms join68_05

theorem join68_06 : ChunkFacts (toRow data68.row) 2049 2048 (toTotals ⟨3221088436547, 702706801000, 1465570805045, 2458224432502, 2802114496⟩) :=
  CleanupSegments208.append_exact join68_02 join68_03 rfl rfl rfl
#print axioms join68_06

theorem join68_07 : ChunkFacts (toRow data68.row) 1 4096 (toTotals ⟨1303762835562467, 6001213005616, 23952622077069, 1285811426491014, 13217049497⟩) :=
  CleanupSegments208.append_exact join68_05 join68_06 rfl rfl rfl
#print axioms join68_07

theorem join68_08 : ChunkFacts (toRow data68.row) 1 4878 (toTotals ⟨1303939041306746, 6152803824480, 24253701715219, 1285838143416007, 13986247517⟩) :=
  CleanupSegments208.append_exact join68_07 join68_04 rfl rfl rfl
#print axioms join68_08

theorem fact68 : ChunkFacts (toRow data68.row) 1 data68.steps (toTotals data68.total) := join68_08
#print axioms fact68

theorem piece0544 : ChunkFacts (toRow data69.row) 1 512 (toTotals ⟨1249782680801439, 3072722607251, 16207739096998, 1236647664311692, 4665641266⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0544
#print axioms piece0544

theorem piece0545 : ChunkFacts (toRow data69.row) 513 512 (toTotals ⟨68763126565064, 1640645968137, 3977747709264, 66426024823937, 2857181661⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0545
#print axioms piece0545

theorem piece0546 : ChunkFacts (toRow data69.row) 1025 512 (toTotals ⟨18391873198160, 949320664072, 2066799635837, 17274394226395, 2126984577⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0546
#print axioms piece0546

theorem piece0547 : ChunkFacts (toRow data69.row) 1537 512 (toTotals ⟨5218097136536, 523447233309, 1029904404876, 4711639964969, 1460362779⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0547
#print axioms piece0547

theorem piece0548 : ChunkFacts (toRow data69.row) 2049 512 (toTotals ⟨2866964576592, 398603896427, 798843535915, 2466724937104, 1318464959⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0548
#print axioms piece0548

theorem piece0549 : ChunkFacts (toRow data69.row) 2561 512 (toTotals ⟨713039051774, 217517144977, 396929882450, 533626314301, 785663258⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0549
#print axioms piece0549

theorem piece0550 : ChunkFacts (toRow data69.row) 3073 512 (toTotals ⟨363325089947, 164682422201, 297614527225, 230392984923, 665076480⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0550
#print axioms piece0550

theorem piece0551 : ChunkFacts (toRow data69.row) 3585 512 (toTotals ⟨134496641996, 109078137344, 197126310400, 46448468940, 504534372⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0551
#print axioms piece0551

theorem piece0552 : ChunkFacts (toRow data69.row) 4097 512 (toTotals ⟨118752159806, 109078137344, 197126310400, 30703986750, 533485162⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0552
#print axioms piece0552

theorem piece0553 : ChunkFacts (toRow data69.row) 4609 512 (toTotals ⟨106332352180, 109078137344, 197126310400, 18284179124, 562459202⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0553
#print axioms piece0553

theorem piece0554 : ChunkFacts (toRow data69.row) 5121 223 (toTotals ⟨43056784339, 47508641851, 85857748475, 4707677715, 224463014⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0554
#print axioms piece0554

theorem join69_00 : ChunkFacts (toRow data69.row) 1 1024 (toTotals ⟨1318545807366503, 4713368575388, 20185486806262, 1303073689135629, 7522822927⟩) :=
  CleanupSegments208.append_exact piece0544 piece0545 rfl rfl rfl
#print axioms join69_00

theorem join69_01 : ChunkFacts (toRow data69.row) 1025 1024 (toTotals ⟨23609970334696, 1472767897381, 3096704040713, 21986034191364, 3587347356⟩) :=
  CleanupSegments208.append_exact piece0546 piece0547 rfl rfl rfl
#print axioms join69_01

theorem join69_02 : ChunkFacts (toRow data69.row) 2049 1024 (toTotals ⟨3580003628366, 616121041404, 1195773418365, 3000351251405, 2104128217⟩) :=
  CleanupSegments208.append_exact piece0548 piece0549 rfl rfl rfl
#print axioms join69_02

theorem join69_03 : ChunkFacts (toRow data69.row) 3073 1024 (toTotals ⟨497821731943, 273760559545, 494740837625, 276841453863, 1169610852⟩) :=
  CleanupSegments208.append_exact piece0550 piece0551 rfl rfl rfl
#print axioms join69_03

theorem join69_04 : ChunkFacts (toRow data69.row) 4097 1024 (toTotals ⟨225084511986, 218156274688, 394252620800, 48988165874, 1095944364⟩) :=
  CleanupSegments208.append_exact piece0552 piece0553 rfl rfl rfl
#print axioms join69_04

theorem join69_05 : ChunkFacts (toRow data69.row) 1 2048 (toTotals ⟨1342155777701199, 6186136472769, 23282190846975, 1325059723326993, 11110170283⟩) :=
  CleanupSegments208.append_exact join69_00 join69_01 rfl rfl rfl
#print axioms join69_05

theorem join69_06 : ChunkFacts (toRow data69.row) 2049 2048 (toTotals ⟨4077825360309, 889881600949, 1690514255990, 3277192705268, 3273739069⟩) :=
  CleanupSegments208.append_exact join69_02 join69_03 rfl rfl rfl
#print axioms join69_06

theorem join69_07 : ChunkFacts (toRow data69.row) 4097 1247 (toTotals ⟨268141296325, 265664916539, 480110369275, 53695843589, 1320407378⟩) :=
  CleanupSegments208.append_exact join69_04 piece0554 rfl rfl rfl
#print axioms join69_07

theorem join69_08 : ChunkFacts (toRow data69.row) 1 4096 (toTotals ⟨1346233603061508, 7076018073718, 24972705102965, 1328336916032261, 14383909352⟩) :=
  CleanupSegments208.append_exact join69_05 join69_06 rfl rfl rfl
#print axioms join69_08

theorem join69_09 : ChunkFacts (toRow data69.row) 1 5343 (toTotals ⟨1346501744357833, 7341682990257, 25452815472240, 1328390611875850, 15704316730⟩) :=
  CleanupSegments208.append_exact join69_08 join69_07 rfl rfl rfl
#print axioms join69_09

theorem fact69 : ChunkFacts (toRow data69.row) 1 data69.steps (toTotals data69.total) := join69_09
#print axioms fact69

theorem piece0555 : ChunkFacts (toRow data70.row) 1 512 (toTotals ⟨1083730068998963, 763713367440, 14446289814257, 1070047492552146, 3732511146⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0555
#print axioms piece0555

theorem piece0556 : ChunkFacts (toRow data70.row) 513 512 (toTotals ⟨40960728056939, 306078906588, 2547209584258, 38719597379269, 1918853347⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0556
#print axioms piece0556

theorem piece0557 : ChunkFacts (toRow data70.row) 1025 512 (toTotals ⟨7133937694868, 142322404744, 1040730621254, 6235529478358, 1177224026⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0557
#print axioms piece0557

theorem piece0558 : ChunkFacts (toRow data70.row) 1537 512 (toTotals ⟨1591679996565, 79207232668, 523428426327, 1147458802906, 746510999⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0558
#print axioms piece0558

theorem piece0559 : ChunkFacts (toRow data70.row) 2049 512 (toTotals ⟨343605599701, 39240885460, 234046340751, 148800144410, 403312365⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G34.checked0559
#print axioms piece0559

theorem piece0560 : ChunkFacts (toRow data70.row) 2561 512 (toTotals ⟨183201629410, 33766946816, 190821633536, 26146942690, 360361486⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0560
#print axioms piece0560

theorem piece0561 : ChunkFacts (toRow data70.row) 3073 142 (toTotals ⟨45433371434, 9365051656, 52923187426, 1875235664, 95149857⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0561
#print axioms piece0561

theorem join70_00 : ChunkFacts (toRow data70.row) 1 1024 (toTotals ⟨1124690797055902, 1069792274028, 16993499398515, 1108767089931415, 5651364493⟩) :=
  CleanupSegments208.append_exact piece0555 piece0556 rfl rfl rfl
#print axioms join70_00

theorem join70_01 : ChunkFacts (toRow data70.row) 1025 1024 (toTotals ⟨8725617691433, 221529637412, 1564159047581, 7382988281264, 1923735025⟩) :=
  CleanupSegments208.append_exact piece0557 piece0558 rfl rfl rfl
#print axioms join70_01

theorem join70_02 : ChunkFacts (toRow data70.row) 2049 1024 (toTotals ⟨526807229111, 73007832276, 424867974287, 174947087100, 763673851⟩) :=
  CleanupSegments208.append_exact piece0559 piece0560 rfl rfl rfl
#print axioms join70_02

theorem join70_03 : ChunkFacts (toRow data70.row) 1 2048 (toTotals ⟨1133416414747335, 1291321911440, 18557658446096, 1116150078212679, 7575099518⟩) :=
  CleanupSegments208.append_exact join70_00 join70_01 rfl rfl rfl
#print axioms join70_03

theorem join70_04 : ChunkFacts (toRow data70.row) 2049 1166 (toTotals ⟨572240600545, 82372883932, 477791161713, 176822322764, 858823708⟩) :=
  CleanupSegments208.append_exact join70_02 piece0561 rfl rfl rfl
#print axioms join70_04

theorem join70_05 : ChunkFacts (toRow data70.row) 1 3214 (toTotals ⟨1133988655347880, 1373694795372, 19035449607809, 1116326900535443, 8433923226⟩) :=
  CleanupSegments208.append_exact join70_03 join70_04 rfl rfl rfl
#print axioms join70_05

theorem fact70 : ChunkFacts (toRow data70.row) 1 data70.steps (toTotals data70.total) := join70_05
#print axioms fact70

theorem piece0562 : ChunkFacts (toRow data71.row) 1 512 (toTotals ⟨1099556514937889, 1157013460344, 14716379760948, 1085997148637285, 3962274061⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0562
#print axioms piece0562

theorem piece0563 : ChunkFacts (toRow data71.row) 513 512 (toTotals ⟨45431350258027, 505372342660, 2779888254667, 43156834346020, 2115471067⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0563
#print axioms piece0563

theorem piece0564 : ChunkFacts (toRow data71.row) 1025 512 (toTotals ⟨9104078284686, 251068587692, 1217085230377, 8138061642001, 1367453507⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0564
#print axioms piece0564

theorem piece0565 : ChunkFacts (toRow data71.row) 1537 512 (toTotals ⟨2236044343382, 141072900308, 612130670041, 1764986573649, 900312167⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0565
#print axioms piece0565

theorem piece0566 : ChunkFacts (toRow data71.row) 2049 512 (toTotals ⟨564321167730, 72546175280, 304524626008, 332342717002, 519400747⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0566
#print axioms piece0566

theorem piece0567 : ChunkFacts (toRow data71.row) 2561 512 (toTotals ⟨183201629410, 50194110464, 190821633536, 42574106338, 386318350⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0567
#print axioms piece0567

theorem piece0568 : ChunkFacts (toRow data71.row) 3073 484 (toTotals ⟨147148063463, 47449120048, 180386075452, 14211108059, 369884279⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0568
#print axioms piece0568

theorem join71_00 : ChunkFacts (toRow data71.row) 1 1024 (toTotals ⟨1144987865195916, 1662385803004, 17496268015615, 1129153982983305, 6077745128⟩) :=
  CleanupSegments208.append_exact piece0562 piece0563 rfl rfl rfl
#print axioms join71_00

theorem join71_01 : ChunkFacts (toRow data71.row) 1025 1024 (toTotals ⟨11340122628068, 392141488000, 1829215900418, 9903048215650, 2267765674⟩) :=
  CleanupSegments208.append_exact piece0564 piece0565 rfl rfl rfl
#print axioms join71_01

theorem join71_02 : ChunkFacts (toRow data71.row) 2049 1024 (toTotals ⟨747522797140, 122740285744, 495346259544, 374916823340, 905719097⟩) :=
  CleanupSegments208.append_exact piece0566 piece0567 rfl rfl rfl
#print axioms join71_02

theorem join71_03 : ChunkFacts (toRow data71.row) 1 2048 (toTotals ⟨1156327987823984, 2054527291004, 19325483916033, 1139057031198955, 8345510802⟩) :=
  CleanupSegments208.append_exact join71_00 join71_01 rfl rfl rfl
#print axioms join71_03

theorem join71_04 : ChunkFacts (toRow data71.row) 2049 1508 (toTotals ⟨894670860603, 170189405792, 675732334996, 389127931399, 1275603376⟩) :=
  CleanupSegments208.append_exact join71_02 piece0568 rfl rfl rfl
#print axioms join71_04

theorem join71_05 : ChunkFacts (toRow data71.row) 1 3556 (toTotals ⟨1157222658684587, 2224716696796, 20001216251029, 1139446159130354, 9621114178⟩) :=
  CleanupSegments208.append_exact join71_03 join71_04 rfl rfl rfl
#print axioms join71_05

theorem fact71 : ChunkFacts (toRow data71.row) 1 data71.steps (toTotals data71.total) := join71_05
#print axioms fact71

theorem piece0569 : ChunkFacts (toRow data72.row) 1 512 (toTotals ⟨1144743973466961, 1542046488540, 15091361042474, 1131194658913027, 4211861595⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0569
#print axioms piece0569

theorem piece0570 : ChunkFacts (toRow data72.row) 513 512 (toTotals ⟨51505393553268, 714816891960, 3068232108640, 49151978336588, 2344209554⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0570
#print axioms piece0570

theorem piece0571 : ChunkFacts (toRow data72.row) 1025 512 (toTotals ⟨11010118899839, 369215469660, 1404406160176, 9974928209323, 1572653220⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0571
#print axioms piece0571

theorem piece0572 : ChunkFacts (toRow data72.row) 1537 512 (toTotals ⟨2905895490960, 204655077120, 695987833216, 2414562734864, 1041970134⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0572
#print axioms piece0572

theorem piece0573 : ChunkFacts (toRow data72.row) 2049 512 (toTotals ⟨1033381448647, 128032413030, 430922661203, 730491200474, 725419643⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0573
#print axioms piece0573

theorem piece0574 : ChunkFacts (toRow data72.row) 2561 512 (toTotals ⟨183201629410, 62970792960, 190821633536, 55350788834, 406507022⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0574
#print axioms piece0574

theorem piece0575 : ChunkFacts (toRow data72.row) 3073 512 (toTotals ⟨155040051482, 62970792960, 190821633536, 27189210906, 424469894⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G35.checked0575
#print axioms piece0575

theorem piece0576 : ChunkFacts (toRow data72.row) 3585 293 (toTotals ⟨79093882798, 36036020190, 109200661379, 5929241609, 240254016⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0576
#print axioms piece0576

theorem join72_00 : ChunkFacts (toRow data72.row) 1 1024 (toTotals ⟨1196249367020229, 2256863380500, 18159593151114, 1180346637249615, 6556071149⟩) :=
  CleanupSegments208.append_exact piece0569 piece0570 rfl rfl rfl
#print axioms join72_00

theorem join72_01 : ChunkFacts (toRow data72.row) 1025 1024 (toTotals ⟨13916014390799, 573870546780, 2100393993392, 12389490944187, 2614623354⟩) :=
  CleanupSegments208.append_exact piece0571 piece0572 rfl rfl rfl
#print axioms join72_01

theorem join72_02 : ChunkFacts (toRow data72.row) 2049 1024 (toTotals ⟨1216583078057, 191003205990, 621744294739, 785841989308, 1131926665⟩) :=
  CleanupSegments208.append_exact piece0573 piece0574 rfl rfl rfl
#print axioms join72_02

theorem join72_03 : ChunkFacts (toRow data72.row) 3073 805 (toTotals ⟨234133934280, 99006813150, 300022294915, 33118452515, 664723910⟩) :=
  CleanupSegments208.append_exact piece0575 piece0576 rfl rfl rfl
#print axioms join72_03

theorem join72_04 : ChunkFacts (toRow data72.row) 1 2048 (toTotals ⟨1210165381411028, 2830733927280, 20259987144506, 1192736128193802, 9170694503⟩) :=
  CleanupSegments208.append_exact join72_00 join72_01 rfl rfl rfl
#print axioms join72_04

theorem join72_05 : ChunkFacts (toRow data72.row) 2049 1829 (toTotals ⟨1450717012337, 290010019140, 921766589654, 818960441823, 1796650575⟩) :=
  CleanupSegments208.append_exact join72_02 join72_03 rfl rfl rfl
#print axioms join72_05

theorem join72_06 : ChunkFacts (toRow data72.row) 1 3877 (toTotals ⟨1211616098423365, 3120743946420, 21181753734160, 1193555088635625, 10967345078⟩) :=
  CleanupSegments208.append_exact join72_04 join72_05 rfl rfl rfl
#print axioms join72_06

theorem fact72 : ChunkFacts (toRow data72.row) 1 data72.steps (toTotals data72.total) := join72_06
#print axioms fact72

theorem piece0577 : ChunkFacts (toRow data73.row) 1 512 (toTotals ⟨1190207060085983, 1966179587520, 15456725371510, 1176716514301993, 4467561957⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0577
#print axioms piece0577

theorem piece0578 : ChunkFacts (toRow data73.row) 513 512 (toTotals ⟨59450479683054, 976136412224, 3402106741781, 57024509353497, 2577828400⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0578
#print axioms piece0578

theorem piece0579 : ChunkFacts (toRow data73.row) 1025 512 (toTotals ⟨13617824538718, 518544729440, 1612669750939, 12523699517219, 1799059438⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0579
#print axioms piece0579

theorem piece0580 : ChunkFacts (toRow data73.row) 1537 512 (toTotals ⟨3807759453558, 282869478656, 788417061960, 3302211870254, 1199028768⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0580
#print axioms piece0580

theorem piece0581 : ChunkFacts (toRow data73.row) 2049 512 (toTotals ⟨1533420335819, 195582348736, 549718645236, 1179284039319, 936021054⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0581
#print axioms piece0581

theorem piece0582 : ChunkFacts (toRow data73.row) 2561 512 (toTotals ⟨315725317885, 96015842912, 241881328447, 169859832350, 511180330⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0582
#print axioms piece0582

theorem piece0583 : ChunkFacts (toRow data73.row) 3073 512 (toTotals ⟨155040051482, 75747475456, 190821633536, 39965893402, 448328582⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0583
#print axioms piece0583

theorem piece0584 : ChunkFacts (toRow data73.row) 3585 512 (toTotals ⟨134426576332, 75747475456, 190821633536, 19352418252, 469946253⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0584
#print axioms piece0584

theorem piece0585 : ChunkFacts (toRow data73.row) 4097 166 (toTotals ⟨40018780601, 24558751808, 61867951498, 2709580911, 142748496⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0585
#print axioms piece0585

theorem join73_00 : ChunkFacts (toRow data73.row) 1 1024 (toTotals ⟨1249657539769037, 2942315999744, 18858832113291, 1233741023655490, 7045390357⟩) :=
  CleanupSegments208.append_exact piece0577 piece0578 rfl rfl rfl
#print axioms join73_00

theorem join73_01 : ChunkFacts (toRow data73.row) 1025 1024 (toTotals ⟨17425583992276, 801414208096, 2401086812899, 15825911387473, 2998088206⟩) :=
  CleanupSegments208.append_exact piece0579 piece0580 rfl rfl rfl
#print axioms join73_01

theorem join73_02 : ChunkFacts (toRow data73.row) 2049 1024 (toTotals ⟨1849145653704, 291598191648, 791599973683, 1349143871669, 1447201384⟩) :=
  CleanupSegments208.append_exact piece0581 piece0582 rfl rfl rfl
#print axioms join73_02

theorem join73_03 : ChunkFacts (toRow data73.row) 3073 1024 (toTotals ⟨289466627814, 151494950912, 381643267072, 59318311654, 918274835⟩) :=
  CleanupSegments208.append_exact piece0583 piece0584 rfl rfl rfl
#print axioms join73_03

theorem join73_04 : ChunkFacts (toRow data73.row) 1 2048 (toTotals ⟨1267083123761313, 3743730207840, 21259918926190, 1249566935042963, 10043478563⟩) :=
  CleanupSegments208.append_exact join73_00 join73_01 rfl rfl rfl
#print axioms join73_04

theorem join73_05 : ChunkFacts (toRow data73.row) 2049 2048 (toTotals ⟨2138612281518, 443093142560, 1173243240755, 1408462183323, 2365476219⟩) :=
  CleanupSegments208.append_exact join73_02 join73_03 rfl rfl rfl
#print axioms join73_05

theorem join73_06 : ChunkFacts (toRow data73.row) 1 4096 (toTotals ⟨1269221736042831, 4186823350400, 22433162166945, 1250975397226286, 12408954782⟩) :=
  CleanupSegments208.append_exact join73_04 join73_05 rfl rfl rfl
#print axioms join73_06

theorem join73_07 : ChunkFacts (toRow data73.row) 1 4262 (toTotals ⟨1269261754823432, 4211382102208, 22495030118443, 1250978106807197, 12551703278⟩) :=
  CleanupSegments208.append_exact join73_06 piece0585 rfl rfl rfl
#print axioms join73_07

theorem fact73 : ChunkFacts (toRow data73.row) 1 data73.steps (toTotals data73.total) := join73_07
#print axioms fact73

theorem piece0586 : ChunkFacts (toRow data74.row) 1 512 (toTotals ⟨1207860911641159, 2239372083609, 15628948684425, 1194471335040343, 4631016157⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0586
#print axioms piece0586

theorem piece0587 : ChunkFacts (toRow data74.row) 513 512 (toTotals ⟨61734485302427, 1143971185801, 3550622103810, 59327834384418, 2735464962⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0587
#print axioms piece0587

theorem piece0588 : ChunkFacts (toRow data74.row) 1025 512 (toTotals ⟨15309286696969, 634894890830, 1749160594706, 14195020993093, 1954527600⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0588
#print axioms piece0588

theorem piece0589 : ChunkFacts (toRow data74.row) 1537 512 (toTotals ⟨4103918779629, 339494709248, 842458344904, 3600955143973, 1289287736⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0589
#print axioms piece0589

theorem piece0590 : ChunkFacts (toRow data74.row) 2049 512 (toTotals ⟨2045967268308, 256610258748, 644462265156, 1658115261900, 1108067477⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0590
#print axioms piece0590

theorem piece0591 : ChunkFacts (toRow data74.row) 2561 512 (toTotals ⟨441370925504, 130460125087, 293313721861, 278517328730, 621892167⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G36.checked0591
#print axioms piece0591

theorem piece0592 : ChunkFacts (toRow data74.row) 3073 512 (toTotals ⟨155040051482, 84873677312, 190821633536, 49092095258, 465370502⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0592
#print axioms piece0592

theorem piece0593 : ChunkFacts (toRow data74.row) 3585 512 (toTotals ⟨134426576332, 84873677312, 190821633536, 28478620108, 489609613⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0593
#print axioms piece0593

theorem piece0594 : ChunkFacts (toRow data74.row) 4097 491 (toTotals ⟨114077451378, 81392530391, 182994964973, 12475016796, 474925495⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0594
#print axioms piece0594

theorem join74_00 : ChunkFacts (toRow data74.row) 1 1024 (toTotals ⟨1269595396943586, 3383343269410, 19179570788235, 1253799169424761, 7366481119⟩) :=
  CleanupSegments208.append_exact piece0586 piece0587 rfl rfl rfl
#print axioms join74_00

theorem join74_01 : ChunkFacts (toRow data74.row) 1025 1024 (toTotals ⟨19413205476598, 974389600078, 2591618939610, 17795976137066, 3243815336⟩) :=
  CleanupSegments208.append_exact piece0588 piece0589 rfl rfl rfl
#print axioms join74_01

theorem join74_02 : ChunkFacts (toRow data74.row) 2049 1024 (toTotals ⟨2487338193812, 387070383835, 937775987017, 1936632590630, 1729959644⟩) :=
  CleanupSegments208.append_exact piece0590 piece0591 rfl rfl rfl
#print axioms join74_02

theorem join74_03 : ChunkFacts (toRow data74.row) 3073 1024 (toTotals ⟨289466627814, 169747354624, 381643267072, 77570715366, 954980115⟩) :=
  CleanupSegments208.append_exact piece0592 piece0593 rfl rfl rfl
#print axioms join74_03

theorem join74_04 : ChunkFacts (toRow data74.row) 1 2048 (toTotals ⟨1289008602420184, 4357732869488, 21771189727845, 1271595145561827, 10610296455⟩) :=
  CleanupSegments208.append_exact join74_00 join74_01 rfl rfl rfl
#print axioms join74_04

theorem join74_05 : ChunkFacts (toRow data74.row) 2049 2048 (toTotals ⟨2776804821626, 556817738459, 1319419254089, 2014203305996, 2684939759⟩) :=
  CleanupSegments208.append_exact join74_02 join74_03 rfl rfl rfl
#print axioms join74_05

theorem join74_06 : ChunkFacts (toRow data74.row) 1 4096 (toTotals ⟨1291785407241810, 4914550607947, 23090608981934, 1273609348867823, 13295236214⟩) :=
  CleanupSegments208.append_exact join74_04 join74_05 rfl rfl rfl
#print axioms join74_06

theorem join74_07 : ChunkFacts (toRow data74.row) 1 4587 (toTotals ⟨1291899484693188, 4995943138338, 23273603946907, 1273621823884619, 13770161709⟩) :=
  CleanupSegments208.append_exact join74_06 piece0594 rfl rfl rfl
#print axioms join74_07

theorem fact74 : ChunkFacts (toRow data74.row) 1 data74.steps (toTotals data74.total) := join74_07
#print axioms fact74

theorem piece0595 : ChunkFacts (toRow data75.row) 1 512 (toTotals ⟨1231451329996062, 2560027959216, 15820271131629, 1218191086823649, 4806908267⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0595
#print axioms piece0595

theorem piece0596 : ChunkFacts (toRow data75.row) 513 512 (toTotals ⟨66753786354441, 1361713093338, 3777705305170, 64337794142609, 2900724666⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0596
#print axioms piece0596

theorem piece0597 : ChunkFacts (toRow data75.row) 1025 512 (toTotals ⟨16981952223266, 763749018240, 1885330318774, 15860370922732, 2106769960⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0597
#print axioms piece0597

theorem piece0598 : ChunkFacts (toRow data75.row) 1537 512 (toTotals ⟨4849989219640, 421897895172, 945762383566, 4326124731246, 1434186925⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0598
#print axioms piece0598

theorem piece0599 : ChunkFacts (toRow data75.row) 2049 512 (toTotals ⟨2545785770937, 323308178154, 732139588007, 2136954361084, 1284953703⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0599
#print axioms piece0599

theorem piece0600 : ChunkFacts (toRow data75.row) 2561 512 (toTotals ⟨547160609857, 161745885834, 331160922081, 377745573610, 708942657⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0600
#print axioms piece0600

theorem piece0601 : ChunkFacts (toRow data75.row) 3073 512 (toTotals ⟨248827098261, 115113133278, 233681961381, 130258270158, 563170734⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0601
#print axioms piece0601

theorem piece0602 : ChunkFacts (toRow data75.row) 3585 512 (toTotals ⟨134426576332, 93999879168, 190821633536, 37604821964, 509272973⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0602
#print axioms piece0602

theorem piece0603 : ChunkFacts (toRow data75.row) 4097 512 (toTotals ⟨118682094142, 93999879168, 190821633536, 21860339774, 536137673⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0603
#print axioms piece0603

theorem piece0604 : ChunkFacts (toRow data75.row) 4609 359 (toTotals ⟨75654174763, 65910071526, 133798762577, 7765483712, 368913454⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0604
#print axioms piece0604

theorem join75_00 : ChunkFacts (toRow data75.row) 1 1024 (toTotals ⟨1298205116350503, 3921741052554, 19597976436799, 1282528880966258, 7707632933⟩) :=
  CleanupSegments208.append_exact piece0595 piece0596 rfl rfl rfl
#print axioms join75_00

theorem join75_01 : ChunkFacts (toRow data75.row) 1025 1024 (toTotals ⟨21831941442906, 1185646913412, 2831092702340, 20186495653978, 3540956885⟩) :=
  CleanupSegments208.append_exact piece0597 piece0598 rfl rfl rfl
#print axioms join75_01

theorem join75_02 : ChunkFacts (toRow data75.row) 2049 1024 (toTotals ⟨3092946380794, 485054063988, 1063300510088, 2514699934694, 1993896360⟩) :=
  CleanupSegments208.append_exact piece0599 piece0600 rfl rfl rfl
#print axioms join75_02

theorem join75_03 : ChunkFacts (toRow data75.row) 3073 1024 (toTotals ⟨383253674593, 209113012446, 424503594917, 167863092122, 1072443707⟩) :=
  CleanupSegments208.append_exact piece0601 piece0602 rfl rfl rfl
#print axioms join75_03

theorem join75_04 : ChunkFacts (toRow data75.row) 4097 871 (toTotals ⟨194336268905, 159909950694, 324620396113, 29625823486, 905051127⟩) :=
  CleanupSegments208.append_exact piece0603 piece0604 rfl rfl rfl
#print axioms join75_04

theorem join75_05 : ChunkFacts (toRow data75.row) 1 2048 (toTotals ⟨1320037057793409, 5107387965966, 22429069139139, 1302715376620236, 11248589818⟩) :=
  CleanupSegments208.append_exact join75_00 join75_01 rfl rfl rfl
#print axioms join75_05

theorem join75_06 : ChunkFacts (toRow data75.row) 2049 2048 (toTotals ⟨3476200055387, 694167076434, 1487804105005, 2682563026816, 3066340067⟩) :=
  CleanupSegments208.append_exact join75_02 join75_03 rfl rfl rfl
#print axioms join75_06

theorem join75_07 : ChunkFacts (toRow data75.row) 1 4096 (toTotals ⟨1323513257848796, 5801555042400, 23916873244144, 1305397939647052, 14314929885⟩) :=
  CleanupSegments208.append_exact join75_05 join75_06 rfl rfl rfl
#print axioms join75_07

theorem join75_08 : ChunkFacts (toRow data75.row) 1 4967 (toTotals ⟨1323707594117701, 5961464993094, 24241493640257, 1305427565470538, 15219981012⟩) :=
  CleanupSegments208.append_exact join75_07 join75_04 rfl rfl rfl
#print axioms join75_08

theorem fact75 : ChunkFacts (toRow data75.row) 1 data75.steps (toTotals data75.total) := join75_08
#print axioms fact75

theorem piece0605 : ChunkFacts (toRow data76.row) 1 512 (toTotals ⟨1269456002848546, 2933856437882, 16131559237272, 1256258300049156, 5000328871⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0605
#print axioms piece0605

theorem piece0606 : ChunkFacts (toRow data76.row) 513 512 (toTotals ⟨70683799497617, 1584153568855, 3985215179803, 68282737886669, 3087033263⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0606
#print axioms piece0606

theorem piece0607 : ChunkFacts (toRow data76.row) 1025 512 (toTotals ⟨18752334220491, 914841132834, 2037030256346, 17630145096979, 2275814956⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G37.checked0607
#print axioms piece0607

theorem piece0608 : ChunkFacts (toRow data76.row) 1537 512 (toTotals ⟨5640520466374, 514019060104, 1053054628982, 5101484897496, 1591607510⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0608
#print axioms piece0608

theorem piece0609 : ChunkFacts (toRow data76.row) 2049 512 (toTotals ⟨2918227388111, 381284514411, 781335790403, 2518176112119, 1400422971⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0609
#print axioms piece0609

theorem piece0610 : ChunkFacts (toRow data76.row) 2561 512 (toTotals ⟨903504410012, 226796811002, 434318543476, 695982677538, 907021058⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0610
#print axioms piece0610

theorem piece0611 : ChunkFacts (toRow data76.row) 3073 512 (toTotals ⟨380128425891, 160530247219, 297040706891, 243617966219, 721191576⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0611
#print axioms piece0611

theorem piece0612 : ChunkFacts (toRow data76.row) 3585 512 (toTotals ⟨139452569903, 104536007913, 193430523057, 50558054759, 530752077⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0612
#print axioms piece0612

theorem piece0613 : ChunkFacts (toRow data76.row) 4097 512 (toTotals ⟨118682094142, 103126081024, 190821633536, 30986541630, 558422473⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0613
#print axioms piece0613

theorem piece0614 : ChunkFacts (toRow data76.row) 4609 512 (toTotals ⟨106262286516, 103126081024, 190821633536, 18566734004, 587925040⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0614
#print axioms piece0614

theorem piece0615 : ChunkFacts (toRow data76.row) 5121 294 (toTotals ⟨56352493358, 59216929338, 109573359882, 5996062814, 321773440⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0615
#print axioms piece0615

theorem join76_00 : ChunkFacts (toRow data76.row) 1 1024 (toTotals ⟨1340139802346163, 4518010006737, 20116774417075, 1324541037935825, 8087362134⟩) :=
  CleanupSegments208.append_exact piece0605 piece0606 rfl rfl rfl
#print axioms join76_00

theorem join76_01 : ChunkFacts (toRow data76.row) 1025 1024 (toTotals ⟨24392854686865, 1428860192938, 3090084885328, 22731629994475, 3867422466⟩) :=
  CleanupSegments208.append_exact piece0607 piece0608 rfl rfl rfl
#print axioms join76_01

theorem join76_02 : ChunkFacts (toRow data76.row) 2049 1024 (toTotals ⟨3821731798123, 608081325413, 1215654333879, 3214158789657, 2307444029⟩) :=
  CleanupSegments208.append_exact piece0609 piece0610 rfl rfl rfl
#print axioms join76_02

theorem join76_03 : ChunkFacts (toRow data76.row) 3073 1024 (toTotals ⟨519580995794, 265066255132, 490471229948, 294176020978, 1251943653⟩) :=
  CleanupSegments208.append_exact piece0611 piece0612 rfl rfl rfl
#print axioms join76_03

theorem join76_04 : ChunkFacts (toRow data76.row) 4097 1024 (toTotals ⟨224944380658, 206252162048, 381643267072, 49553275634, 1146347513⟩) :=
  CleanupSegments208.append_exact piece0613 piece0614 rfl rfl rfl
#print axioms join76_04

theorem join76_05 : ChunkFacts (toRow data76.row) 1 2048 (toTotals ⟨1364532657033028, 5946870199675, 23206859302403, 1347272667930300, 11954784600⟩) :=
  CleanupSegments208.append_exact join76_00 join76_01 rfl rfl rfl
#print axioms join76_05

theorem join76_06 : ChunkFacts (toRow data76.row) 2049 2048 (toTotals ⟨4341312793917, 873147580545, 1706125563827, 3508334810635, 3559387682⟩) :=
  CleanupSegments208.append_exact join76_02 join76_03 rfl rfl rfl
#print axioms join76_06

theorem join76_07 : ChunkFacts (toRow data76.row) 4097 1318 (toTotals ⟨281296874016, 265469091386, 491216626954, 55549338448, 1468120953⟩) :=
  CleanupSegments208.append_exact join76_04 piece0615 rfl rfl rfl
#print axioms join76_07

theorem join76_08 : ChunkFacts (toRow data76.row) 1 4096 (toTotals ⟨1368873969826945, 6820017780220, 24912984866230, 1350781002740935, 15514172282⟩) :=
  CleanupSegments208.append_exact join76_05 join76_06 rfl rfl rfl
#print axioms join76_08

theorem join76_09 : ChunkFacts (toRow data76.row) 1 5414 (toTotals ⟨1369155266700961, 7085486871606, 25404201493184, 1350836552079383, 16982293235⟩) :=
  CleanupSegments208.append_exact join76_08 join76_07 rfl rfl rfl
#print axioms join76_09

theorem fact76 : ChunkFacts (toRow data76.row) 1 data76.steps (toTotals data76.total) := join76_09
#print axioms fact76

theorem piece0616 : ChunkFacts (toRow data77.row) 1 512 (toTotals ⟨1101775440999203, 799981040448, 14460922615343, 1088114499424308, 4048819270⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0616
#print axioms piece0616

theorem piece0617 : ChunkFacts (toRow data77.row) 513 512 (toTotals ⟨43113477845464, 332080472832, 2616592539168, 40828965779128, 2119639290⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0617
#print axioms piece0617

theorem piece0618 : ChunkFacts (toRow data77.row) 1025 512 (toTotals ⟨7935321876442, 157581325440, 1088304163299, 7004599038583, 1324706832⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0618
#print axioms piece0618

theorem piece0619 : ChunkFacts (toRow data77.row) 1537 512 (toTotals ⟨1790898526047, 87795309888, 539275501509, 1339418334426, 838725263⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0619
#print axioms piece0619

theorem piece0620 : ChunkFacts (toRow data77.row) 2049 512 (toTotals ⟨453087977818, 45978274176, 267185420676, 231880831318, 488614075⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0620
#print axioms piece0620

theorem piece0621 : ChunkFacts (toRow data77.row) 2561 512 (toTotals ⟨183140889826, 34927116288, 185303803392, 32764202722, 386608292⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0621
#print axioms piece0621

theorem piece0622 : ChunkFacts (toRow data77.row) 3073 284 (toTotals ⟨88879729087, 19373634816, 102785703444, 5467660459, 211943609⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0622
#print axioms piece0622

theorem join77_00 : ChunkFacts (toRow data77.row) 1 1024 (toTotals ⟨1144888918844667, 1132061513280, 17077515154511, 1128943465203436, 6168458560⟩) :=
  CleanupSegments208.append_exact piece0616 piece0617 rfl rfl rfl
#print axioms join77_00

theorem join77_01 : ChunkFacts (toRow data77.row) 1025 1024 (toTotals ⟨9726220402489, 245376635328, 1627579664808, 8344017373009, 2163432095⟩) :=
  CleanupSegments208.append_exact piece0618 piece0619 rfl rfl rfl
#print axioms join77_01

theorem join77_02 : ChunkFacts (toRow data77.row) 2049 1024 (toTotals ⟨636228867644, 80905390464, 452489224068, 264645034040, 875222367⟩) :=
  CleanupSegments208.append_exact piece0620 piece0621 rfl rfl rfl
#print axioms join77_02

theorem join77_03 : ChunkFacts (toRow data77.row) 1 2048 (toTotals ⟨1154615139247156, 1377438148608, 18705094819319, 1137287482576445, 8331890655⟩) :=
  CleanupSegments208.append_exact join77_00 join77_01 rfl rfl rfl
#print axioms join77_03

theorem join77_04 : ChunkFacts (toRow data77.row) 2049 1308 (toTotals ⟨725108596731, 100279025280, 555274927512, 270112694499, 1087165976⟩) :=
  CleanupSegments208.append_exact join77_02 piece0622 rfl rfl rfl
#print axioms join77_04

theorem join77_05 : ChunkFacts (toRow data77.row) 1 3356 (toTotals ⟨1155340247843887, 1477717173888, 19260369746831, 1137557595270944, 9419056631⟩) :=
  CleanupSegments208.append_exact join77_03 join77_04 rfl rfl rfl
#print axioms join77_05

theorem fact77 : ChunkFacts (toRow data77.row) 1 data77.steps (toTotals data77.total) := join77_05
#print axioms fact77

theorem piece0623 : ChunkFacts (toRow data78.row) 1 512 (toTotals ⟨1106006689096417, 1131136416027, 14599638386802, 1092538187125642, 4265475525⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G38.checked0623
#print axioms piece0623

theorem piece0624 : ChunkFacts (toRow data78.row) 513 512 (toTotals ⟨47315124897388, 506246850738, 2828104450500, 44993267297626, 2311808269⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0624
#print axioms piece0624

theorem piece0625 : ChunkFacts (toRow data78.row) 1025 512 (toTotals ⟨9717118861084, 255778897797, 1251724196517, 8721173562364, 1515186578⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0625
#print axioms piece0625

theorem piece0626 : ChunkFacts (toRow data78.row) 1537 512 (toTotals ⟨2334881184745, 139791655674, 606954820326, 1867718020093, 972918224⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0626
#print axioms piece0626

theorem piece0627 : ChunkFacts (toRow data78.row) 2049 512 (toTotals ⟨721092002835, 80043526044, 343638215610, 457497313269, 621462306⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0627
#print axioms piece0627

theorem piece0628 : ChunkFacts (toRow data78.row) 2561 512 (toTotals ⟨183140889826, 48557210112, 185303803392, 46394296546, 409681060⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0628
#print axioms piece0628

theorem piece0629 : ChunkFacts (toRow data78.row) 3073 512 (toTotals ⟨154979311898, 48557210112, 185303803392, 18232718618, 424489943⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0629
#print axioms piece0629

theorem piece0630 : ChunkFacts (toRow data78.row) 3585 78 (toTotals ⟨21656758674, 7397387478, 28229876298, 824269854, 57543951⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0630
#print axioms piece0630

theorem join78_00 : ChunkFacts (toRow data78.row) 1 1024 (toTotals ⟨1153321813993805, 1637383266765, 17427742837302, 1137531454423268, 6577283794⟩) :=
  CleanupSegments208.append_exact piece0623 piece0624 rfl rfl rfl
#print axioms join78_00

theorem join78_01 : ChunkFacts (toRow data78.row) 1025 1024 (toTotals ⟨12052000045829, 395570553471, 1858679016843, 10588891582457, 2488104802⟩) :=
  CleanupSegments208.append_exact piece0625 piece0626 rfl rfl rfl
#print axioms join78_01

theorem join78_02 : ChunkFacts (toRow data78.row) 2049 1024 (toTotals ⟨904232892661, 128600736156, 528942019002, 503891609815, 1031143366⟩) :=
  CleanupSegments208.append_exact piece0627 piece0628 rfl rfl rfl
#print axioms join78_02

theorem join78_03 : ChunkFacts (toRow data78.row) 3073 590 (toTotals ⟨176636070572, 55954597590, 213533679690, 19056988472, 482033894⟩) :=
  CleanupSegments208.append_exact piece0629 piece0630 rfl rfl rfl
#print axioms join78_03

theorem join78_04 : ChunkFacts (toRow data78.row) 1 2048 (toTotals ⟨1165373814039634, 2032953820236, 19286421854145, 1148120346005725, 9065388596⟩) :=
  CleanupSegments208.append_exact join78_00 join78_01 rfl rfl rfl
#print axioms join78_04

theorem join78_05 : ChunkFacts (toRow data78.row) 2049 1614 (toTotals ⟨1080868963233, 184555333746, 742475698692, 522948598287, 1513177260⟩) :=
  CleanupSegments208.append_exact join78_02 join78_03 rfl rfl rfl
#print axioms join78_05

theorem join78_06 : ChunkFacts (toRow data78.row) 1 3662 (toTotals ⟨1166454683002867, 2217509153982, 20028897552837, 1148643294604012, 10578565856⟩) :=
  CleanupSegments208.append_exact join78_04 join78_05 rfl rfl rfl
#print axioms join78_06

theorem fact78 : ChunkFacts (toRow data78.row) 1 data78.steps (toTotals data78.total) := join78_06
#print axioms fact78

theorem piece0631 : ChunkFacts (toRow data79.row) 1 512 (toTotals ⟨1149374305606164, 1495668226459, 14950970554118, 1135919003278505, 4518740565⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0631
#print axioms piece0631

theorem piece0632 : ChunkFacts (toRow data79.row) 513 512 (toTotals ⟨53081363016148, 705247556430, 3097305399492, 50689305173086, 2543147141⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0632
#print axioms piece0632

theorem piece0633 : ChunkFacts (toRow data79.row) 1025 512 (toTotals ⟨11610958398030, 370343566065, 1431012615111, 10550289348984, 1726113810⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0633
#print axioms piece0633

theorem piece0634 : ChunkFacts (toRow data79.row) 1537 512 (toTotals ⟨3021150506967, 201178658057, 690196763256, 2532132401768, 1120835756⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0634
#print axioms piece0634

theorem piece0635 : ChunkFacts (toRow data79.row) 2049 512 (toTotals ⟨1188918678165, 135379179174, 465281276718, 859016580621, 841384683⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0635
#print axioms piece0635

theorem piece0636 : ChunkFacts (toRow data79.row) 2561 512 (toTotals ⟨183140889826, 60483542528, 185303803392, 58320628962, 429869732⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0636
#print axioms piece0636

theorem piece0637 : ChunkFacts (toRow data79.row) 3073 512 (toTotals ⟨154979311898, 60483542528, 185303803392, 30159051034, 448348631⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0637
#print axioms piece0637

theorem piece0638 : ChunkFacts (toRow data79.row) 3585 397 (toTotals ⟨105700178499, 46898371843, 143682831927, 8915718415, 349030430⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0638
#print axioms piece0638

theorem join79_00 : ChunkFacts (toRow data79.row) 1 1024 (toTotals ⟨1202455668622312, 2200915782889, 18048275953610, 1186608308451591, 7061887706⟩) :=
  CleanupSegments208.append_exact piece0631 piece0632 rfl rfl rfl
#print axioms join79_00

theorem join79_01 : ChunkFacts (toRow data79.row) 1025 1024 (toTotals ⟨14632108904997, 571522224122, 2121209378367, 13082421750752, 2846949566⟩) :=
  CleanupSegments208.append_exact piece0633 piece0634 rfl rfl rfl
#print axioms join79_01

theorem join79_02 : ChunkFacts (toRow data79.row) 2049 1024 (toTotals ⟨1372059567991, 195862721702, 650585080110, 917337209583, 1271254415⟩) :=
  CleanupSegments208.append_exact piece0635 piece0636 rfl rfl rfl
#print axioms join79_02

theorem join79_03 : ChunkFacts (toRow data79.row) 3073 909 (toTotals ⟨260679490397, 107381914371, 328986635319, 39074769449, 797379061⟩) :=
  CleanupSegments208.append_exact piece0637 piece0638 rfl rfl rfl
#print axioms join79_03

theorem join79_04 : ChunkFacts (toRow data79.row) 1 2048 (toTotals ⟨1217087777527309, 2772438007011, 20169485331977, 1199690730202343, 9908837272⟩) :=
  CleanupSegments208.append_exact join79_00 join79_01 rfl rfl rfl
#print axioms join79_04

theorem join79_05 : ChunkFacts (toRow data79.row) 2049 1933 (toTotals ⟨1632739058388, 303244636073, 979571715429, 956411979032, 2068633476⟩) :=
  CleanupSegments208.append_exact join79_02 join79_03 rfl rfl rfl
#print axioms join79_05

theorem join79_06 : ChunkFacts (toRow data79.row) 1 3981 (toTotals ⟨1218720516585697, 3075682643084, 21149057047406, 1200647142181375, 11977470748⟩) :=
  CleanupSegments208.append_exact join79_04 join79_05 rfl rfl rfl
#print axioms join79_06

theorem fact79 : ChunkFacts (toRow data79.row) 1 data79.steps (toTotals data79.total) := join79_06
#print axioms fact79

theorem piece0639 : ChunkFacts (toRow data80.row) 1 512 (toTotals ⟨1184499983009731, 1861765698947, 15232270912959, 1171129477795719, 4781673082⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G39.checked0639
#print axioms piece0639

theorem piece0640 : ChunkFacts (toRow data80.row) 513 512 (toTotals ⟨60512368802996, 936543198607, 3406785714414, 58042126287189, 2786896080⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0640
#print axioms piece0640

theorem piece0641 : ChunkFacts (toRow data80.row) 1025 512 (toTotals ⟨14106332642403, 503142145200, 1610070152751, 12999404634852, 1939650664⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0641
#print axioms piece0641

theorem piece0642 : ChunkFacts (toRow data80.row) 1537 512 (toTotals ⟨3974633021526, 274352230841, 795153995646, 3453831256721, 1291915376⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0642
#print axioms piece0642

theorem piece0643 : ChunkFacts (toRow data80.row) 2049 512 (toTotals ⟨1717867316577, 198042338819, 576852936333, 1339056719063, 1054315353⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0643
#print axioms piece0643

theorem piece0644 : ChunkFacts (toRow data80.row) 2561 512 (toTotals ⟨338951375691, 94339152225, 244297006425, 188993521491, 555316080⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0644
#print axioms piece0644

theorem piece0645 : ChunkFacts (toRow data80.row) 3073 512 (toTotals ⟨154979311898, 71557993984, 185303803392, 41233502490, 470503127⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0645
#print axioms piece0645

theorem piece0646 : ChunkFacts (toRow data80.row) 3585 512 (toTotals ⟨134365836748, 71557993984, 185303803392, 20620027340, 492382782⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0646
#print axioms piece0646

theorem piece0647 : ChunkFacts (toRow data80.row) 4097 235 (toTotals ⟨56171951660, 32844001145, 85051550385, 3964402420, 218480427⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0647
#print axioms piece0647

theorem join80_00 : ChunkFacts (toRow data80.row) 1 1024 (toTotals ⟨1245012351812727, 2798308897554, 18639056627373, 1229171604082908, 7568569162⟩) :=
  CleanupSegments208.append_exact piece0639 piece0640 rfl rfl rfl
#print axioms join80_00

theorem join80_01 : ChunkFacts (toRow data80.row) 1025 1024 (toTotals ⟨18080965663929, 777494376041, 2405224148397, 16453235891573, 3231566040⟩) :=
  CleanupSegments208.append_exact piece0641 piece0642 rfl rfl rfl
#print axioms join80_01

theorem join80_02 : ChunkFacts (toRow data80.row) 2049 1024 (toTotals ⟨2056818692268, 292381491044, 821149942758, 1528050240554, 1609631433⟩) :=
  CleanupSegments208.append_exact piece0643 piece0644 rfl rfl rfl
#print axioms join80_02

theorem join80_03 : ChunkFacts (toRow data80.row) 3073 1024 (toTotals ⟨289345148646, 143115987968, 370607606784, 61853529830, 962885909⟩) :=
  CleanupSegments208.append_exact piece0645 piece0646 rfl rfl rfl
#print axioms join80_03

theorem join80_04 : ChunkFacts (toRow data80.row) 1 2048 (toTotals ⟨1263093317476656, 3575803273595, 21044280775770, 1245624839974481, 10800135202⟩) :=
  CleanupSegments208.append_exact join80_00 join80_01 rfl rfl rfl
#print axioms join80_04

theorem join80_05 : ChunkFacts (toRow data80.row) 2049 2048 (toTotals ⟨2346163840914, 435497479012, 1191757549542, 1589903770384, 2572517342⟩) :=
  CleanupSegments208.append_exact join80_02 join80_03 rfl rfl rfl
#print axioms join80_05

theorem join80_06 : ChunkFacts (toRow data80.row) 1 4096 (toTotals ⟨1265439481317570, 4011300752607, 22236038325312, 1247214743744865, 13372652544⟩) :=
  CleanupSegments208.append_exact join80_04 join80_05 rfl rfl rfl
#print axioms join80_06

theorem join80_07 : ChunkFacts (toRow data80.row) 1 4331 (toTotals ⟨1265495653269230, 4044144753752, 22321089875697, 1247218708147285, 13591132971⟩) :=
  CleanupSegments208.append_exact join80_06 piece0647 rfl rfl rfl
#print axioms join80_07

theorem fact80 : ChunkFacts (toRow data80.row) 1 data80.steps (toTotals data80.total) := join80_07
#print axioms fact80

theorem piece0648 : ChunkFacts (toRow data81.row) 1 512 (toTotals ⟨1203665918643838, 2148245581485, 15405119625040, 1190409044600283, 4959044307⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0648
#print axioms piece0648

theorem piece0649 : ChunkFacts (toRow data81.row) 513 512 (toTotals ⟨63602032586026, 1117037121945, 3574130723790, 61144938984181, 2960297033⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0649
#print axioms piece0649

theorem piece0650 : ChunkFacts (toRow data81.row) 1025 512 (toTotals ⟨15780400066297, 622297318395, 1744523986635, 14658173398057, 2102640633⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0650
#print axioms piece0650

theorem piece0651 : ChunkFacts (toRow data81.row) 1537 512 (toTotals ⟨4391874824176, 337940479230, 866814450864, 3863000852542, 1410410796⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0651
#print axioms piece0651

theorem piece0652 : ChunkFacts (toRow data81.row) 2049 512 (toTotals ⟨2253775361866, 259540817070, 667757630814, 1845558548122, 1241827916⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0652
#print axioms piece0652

theorem piece0653 : ChunkFacts (toRow data81.row) 2561 512 (toTotals ⟨481816316912, 129928472370, 299508753876, 312236035406, 679203161⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0653
#print axioms piece0653

theorem piece0654 : ChunkFacts (toRow data81.row) 3073 512 (toTotals ⟨170722026241, 83931896385, 192180311721, 62473610905, 500483983⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0654
#print axioms piece0654

theorem piece0655 : ChunkFacts (toRow data81.row) 3585 512 (toTotals ⟨134365836748, 80928683520, 185303803392, 29990716876, 514012478⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G40.checked0655
#print axioms piece0655

theorem piece0656 : ChunkFacts (toRow data81.row) 4097 512 (toTotals ⟨118621354558, 80928683520, 185303803392, 14246234686, 538808370⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0656
#print axioms piece0656

theorem piece0657 : ChunkFacts (toRow data81.row) 4609 71 (toTotals ⟨15406974068, 11222532285, 25696425861, 933080492, 57734021⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0657
#print axioms piece0657

theorem join81_00 : ChunkFacts (toRow data81.row) 1 1024 (toTotals ⟨1267267951229864, 3265282703430, 18979250348830, 1251553983584464, 7919341340⟩) :=
  CleanupSegments208.append_exact piece0648 piece0649 rfl rfl rfl
#print axioms join81_00

theorem join81_01 : ChunkFacts (toRow data81.row) 1025 1024 (toTotals ⟨20172274890473, 960237797625, 2611338437499, 18521174250599, 3513051429⟩) :=
  CleanupSegments208.append_exact piece0650 piece0651 rfl rfl rfl
#print axioms join81_01

theorem join81_02 : ChunkFacts (toRow data81.row) 2049 1024 (toTotals ⟨2735591678778, 389469289440, 967266384690, 2157794583528, 1921031077⟩) :=
  CleanupSegments208.append_exact piece0652 piece0653 rfl rfl rfl
#print axioms join81_02

theorem join81_03 : ChunkFacts (toRow data81.row) 3073 1024 (toTotals ⟨305087862989, 164860579905, 377484115113, 92464327781, 1014496461⟩) :=
  CleanupSegments208.append_exact piece0654 piece0655 rfl rfl rfl
#print axioms join81_03

theorem join81_04 : ChunkFacts (toRow data81.row) 4097 583 (toTotals ⟨134028328626, 92151215805, 211000229253, 15179315178, 596542391⟩) :=
  CleanupSegments208.append_exact piece0656 piece0657 rfl rfl rfl
#print axioms join81_04

theorem join81_05 : ChunkFacts (toRow data81.row) 1 2048 (toTotals ⟨1287440226120337, 4225520501055, 21590588786329, 1270075157835063, 11432392769⟩) :=
  CleanupSegments208.append_exact join81_00 join81_01 rfl rfl rfl
#print axioms join81_05

theorem join81_06 : ChunkFacts (toRow data81.row) 2049 2048 (toTotals ⟨3040679541767, 554329869345, 1344750499803, 2250258911309, 2935527538⟩) :=
  CleanupSegments208.append_exact join81_02 join81_03 rfl rfl rfl
#print axioms join81_06

theorem join81_07 : ChunkFacts (toRow data81.row) 1 4096 (toTotals ⟨1290480905662104, 4779850370400, 22935339286132, 1272325416746372, 14367920307⟩) :=
  CleanupSegments208.append_exact join81_05 join81_06 rfl rfl rfl
#print axioms join81_07

theorem join81_08 : ChunkFacts (toRow data81.row) 1 4679 (toTotals ⟨1290614933990730, 4872001586205, 23146339515385, 1272340596061550, 14964462698⟩) :=
  CleanupSegments208.append_exact join81_07 join81_04 rfl rfl rfl
#print axioms join81_08

theorem fact81 : ChunkFacts (toRow data81.row) 1 data81.steps (toTotals data81.total) := join81_08
#print axioms fact81

theorem piece0658 : ChunkFacts (toRow data82.row) 1 512 (toTotals ⟨1229357577087496, 2455263777182, 15600638350501, 1216212202514177, 5135069904⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0658
#print axioms piece0658

theorem piece0659 : ChunkFacts (toRow data82.row) 513 512 (toTotals ⟨68577224352086, 1323543359608, 3794397391188, 66106370320506, 3129966567⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0659
#print axioms piece0659

theorem piece0660 : ChunkFacts (toRow data82.row) 1025 512 (toTotals ⟨17334120688645, 741261150319, 1865174883660, 16210206955304, 2247825167⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0660
#print axioms piece0660

theorem piece0661 : ChunkFacts (toRow data82.row) 1537 512 (toTotals ⟨5270869545338, 419110417067, 972389445792, 4717590516613, 1567329156⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0661
#print axioms piece0661

theorem piece0662 : ChunkFacts (toRow data82.row) 2049 512 (toTotals ⟨2598861583750, 312192711671, 720236247009, 2190818048412, 1368573912⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0662
#print axioms piece0662

theorem piece0663 : ChunkFacts (toRow data82.row) 2561 512 (toTotals ⟨687881037047, 169635771143, 364055579769, 493461228421, 817818645⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0663
#print axioms piece0663

theorem piece0664 : ChunkFacts (toRow data82.row) 3073 512 (toTotals ⟨269328941097, 114255194982, 236696655114, 146887480965, 612061939⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0664
#print axioms piece0664

theorem piece0665 : ChunkFacts (toRow data82.row) 3585 512 (toTotals ⟨134365836748, 89447492096, 185303803392, 38509525452, 533675838⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0665
#print axioms piece0665

theorem piece0666 : ChunkFacts (toRow data82.row) 4097 512 (toTotals ⟨118621354558, 89447492096, 185303803392, 22765043262, 561093170⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0666
#print axioms piece0666

theorem piece0667 : ChunkFacts (toRow data82.row) 4609 439 (toTotals ⟨91721068022, 76694236387, 158883534549, 9531769860, 479736281⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0667
#print axioms piece0667

theorem join82_00 : ChunkFacts (toRow data82.row) 1 1024 (toTotals ⟨1297934801439582, 3778807136790, 19395035741689, 1282318572834683, 8265036471⟩) :=
  CleanupSegments208.append_exact piece0658 piece0659 rfl rfl rfl
#print axioms join82_00

theorem join82_01 : ChunkFacts (toRow data82.row) 1025 1024 (toTotals ⟨22604990233983, 1160371567386, 2837564329452, 20927797471917, 3815154323⟩) :=
  CleanupSegments208.append_exact piece0660 piece0661 rfl rfl rfl
#print axioms join82_01

theorem join82_02 : ChunkFacts (toRow data82.row) 2049 1024 (toTotals ⟨3286742620797, 481828482814, 1084291826778, 2684279276833, 2186392557⟩) :=
  CleanupSegments208.append_exact piece0662 piece0663 rfl rfl rfl
#print axioms join82_02

theorem join82_03 : ChunkFacts (toRow data82.row) 3073 1024 (toTotals ⟨403694777845, 203702687078, 422000458506, 185397006417, 1145737777⟩) :=
  CleanupSegments208.append_exact piece0664 piece0665 rfl rfl rfl
#print axioms join82_03

theorem join82_04 : ChunkFacts (toRow data82.row) 4097 951 (toTotals ⟨210342422580, 166141728483, 344187337941, 32296813122, 1040829451⟩) :=
  CleanupSegments208.append_exact piece0666 piece0667 rfl rfl rfl
#print axioms join82_04

theorem join82_05 : ChunkFacts (toRow data82.row) 1 2048 (toTotals ⟨1320539791673565, 4939178704176, 22232600071141, 1303246370306600, 12080190794⟩) :=
  CleanupSegments208.append_exact join82_00 join82_01 rfl rfl rfl
#print axioms join82_05

theorem join82_06 : ChunkFacts (toRow data82.row) 2049 2048 (toTotals ⟨3690437398642, 685531169892, 1506292285284, 2869676283250, 3332130334⟩) :=
  CleanupSegments208.append_exact join82_02 join82_03 rfl rfl rfl
#print axioms join82_06

theorem join82_07 : ChunkFacts (toRow data82.row) 1 4096 (toTotals ⟨1324230229072207, 5624709874068, 23738892356425, 1306116046589850, 15412321128⟩) :=
  CleanupSegments208.append_exact join82_05 join82_06 rfl rfl rfl
#print axioms join82_07

theorem join82_08 : ChunkFacts (toRow data82.row) 1 5047 (toTotals ⟨1324440571494787, 5790851602551, 24083079694366, 1306148343402972, 16453150579⟩) :=
  CleanupSegments208.append_exact join82_07 join82_04 rfl rfl rfl
#print axioms join82_08

theorem fact82 : ChunkFacts (toRow data82.row) 1 data82.steps (toTotals data82.total) := join82_08
#print axioms fact82

theorem piece0668 : ChunkFacts (toRow data83.row) 1 512 (toTotals ⟨1259963196796315, 2736713909232, 15855624520868, 1246844286184679, 5284945196⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0668
#print axioms piece0668

theorem piece0669 : ChunkFacts (toRow data83.row) 513 512 (toTotals ⟨71233175965949, 1479848528412, 3930841793265, 68782182701096, 3273402776⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0669
#print axioms piece0669

theorem piece0670 : ChunkFacts (toRow data83.row) 1025 512 (toTotals ⟨18640119648992, 851321831616, 1974780935190, 17516660545418, 2378381826⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0670
#print axioms piece0670

theorem piece0671 : ChunkFacts (toRow data83.row) 1537 512 (toTotals ⟨5832989247050, 485825002848, 1049584803804, 5269229446094, 1689161367⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G41.checked0671
#print axioms piece0671

theorem piece0672 : ChunkFacts (toRow data83.row) 2049 512 (toTotals ⟨2867148593797, 353652024132, 754256867163, 2466543750766, 1455745626⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0672
#print axioms piece0672

theorem piece0673 : ChunkFacts (toRow data83.row) 2561 512 (toTotals ⟨973011327816, 217718789976, 439772051682, 750958066110, 975838339⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0673
#print axioms piece0673

theorem piece0674 : ChunkFacts (toRow data83.row) 3073 512 (toTotals ⟨373870988280, 148718102652, 286279899381, 236309191551, 740518312⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0674
#print axioms piece0674

theorem piece0675 : ChunkFacts (toRow data83.row) 3585 512 (toTotals ⟨134365836748, 96262539264, 185303803392, 45324572620, 549406526⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0675
#print axioms piece0675

theorem piece0676 : ChunkFacts (toRow data83.row) 4097 512 (toTotals ⟨118621354558, 96262539264, 185303803392, 29580090430, 578921010⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0676
#print axioms piece0676

theorem piece0677 : ChunkFacts (toRow data83.row) 4609 512 (toTotals ⟨106201546932, 96262539264, 185303803392, 17160282804, 608396493⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0677
#print axioms piece0677

theorem piece0678 : ChunkFacts (toRow data83.row) 5121 266 (toTotals ⟨51086311576, 50011397352, 96271116606, 4826592322, 300001288⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0678
#print axioms piece0678

theorem join83_00 : ChunkFacts (toRow data83.row) 1 1024 (toTotals ⟨1331196372762264, 4216562437644, 19786466314133, 1315626468885775, 8558347972⟩) :=
  CleanupSegments208.append_exact piece0668 piece0669 rfl rfl rfl
#print axioms join83_00

theorem join83_01 : ChunkFacts (toRow data83.row) 1025 1024 (toTotals ⟨24473108896042, 1337146834464, 3024365738994, 22785889991512, 4067543193⟩) :=
  CleanupSegments208.append_exact piece0670 piece0671 rfl rfl rfl
#print axioms join83_01

theorem join83_02 : ChunkFacts (toRow data83.row) 2049 1024 (toTotals ⟨3840159921613, 571370814108, 1194028918845, 3217501816876, 2431583965⟩) :=
  CleanupSegments208.append_exact piece0672 piece0673 rfl rfl rfl
#print axioms join83_02

theorem join83_03 : ChunkFacts (toRow data83.row) 3073 1024 (toTotals ⟨508236825028, 244980641916, 471583702773, 281633764171, 1289924838⟩) :=
  CleanupSegments208.append_exact piece0674 piece0675 rfl rfl rfl
#print axioms join83_03

theorem join83_04 : ChunkFacts (toRow data83.row) 4097 1024 (toTotals ⟨224822901490, 192525078528, 370607606784, 46740373234, 1187317503⟩) :=
  CleanupSegments208.append_exact piece0676 piece0677 rfl rfl rfl
#print axioms join83_04

theorem join83_05 : ChunkFacts (toRow data83.row) 1 2048 (toTotals ⟨1355669481658306, 5553709272108, 22810832053127, 1338412358877287, 12625891165⟩) :=
  CleanupSegments208.append_exact join83_00 join83_01 rfl rfl rfl
#print axioms join83_05

theorem join83_06 : ChunkFacts (toRow data83.row) 2049 2048 (toTotals ⟨4348396746641, 816351456024, 1665612621618, 3499135581047, 3721508803⟩) :=
  CleanupSegments208.append_exact join83_02 join83_03 rfl rfl rfl
#print axioms join83_06

theorem join83_07 : ChunkFacts (toRow data83.row) 4097 1290 (toTotals ⟨275909213066, 242536475880, 466878723390, 51566965556, 1487318791⟩) :=
  CleanupSegments208.append_exact join83_04 piece0678 rfl rfl rfl
#print axioms join83_07

theorem join83_08 : ChunkFacts (toRow data83.row) 1 4096 (toTotals ⟨1360017878404947, 6370060728132, 24476444674745, 1341911494458334, 16347399968⟩) :=
  CleanupSegments208.append_exact join83_05 join83_06 rfl rfl rfl
#print axioms join83_08

theorem join83_09 : ChunkFacts (toRow data83.row) 1 5386 (toTotals ⟨1360293787618013, 6612597204012, 24943323398135, 1341963061423890, 17834718759⟩) :=
  CleanupSegments208.append_exact join83_08 join83_07 rfl rfl rfl
#print axioms join83_09

theorem fact83 : ChunkFacts (toRow data83.row) 1 data83.steps (toTotals data83.total) := join83_09
#print axioms fact83

theorem piece0679 : ChunkFacts (toRow data84.row) 1 512 (toTotals ⟨938393719606816, 686027359040, 14161785712887, 924917961252969, 3995603228⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0679
#print axioms piece0679

theorem piece0680 : ChunkFacts (toRow data84.row) 513 512 (toTotals ⟨36086098197279, 287914338240, 2534754969781, 33839257565738, 2055642540⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0680
#print axioms piece0680

theorem piece0681 : ChunkFacts (toRow data84.row) 1025 512 (toTotals ⟨6636859036102, 135158746560, 1042048378774, 5729969403888, 1261309584⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0681
#print axioms piece0681

theorem piece0682 : ChunkFacts (toRow data84.row) 1537 512 (toTotals ⟨1573615523677, 75441793440, 525435098033, 1123622219084, 802843018⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0682
#print axioms piece0682

theorem piece0683 : ChunkFacts (toRow data84.row) 2049 512 (toTotals ⟨347599910752, 37315295680, 235163377552, 149751828880, 434174761⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0683
#print axioms piece0683

theorem piece0684 : ChunkFacts (toRow data84.row) 2561 512 (toTotals ⟨182998343324, 31948881920, 190456623616, 24490601628, 385922255⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0684
#print axioms piece0684

theorem piece0685 : ChunkFacts (toRow data84.row) 3073 156 (toTotals ⟨49735314416, 9734424960, 58029752508, 1439986868, 113519071⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0685
#print axioms piece0685

theorem join84_00 : ChunkFacts (toRow data84.row) 1 1024 (toTotals ⟨974479817804095, 973941697280, 16696540682668, 958757218818707, 6051245768⟩) :=
  CleanupSegments208.append_exact piece0679 piece0680 rfl rfl rfl
#print axioms join84_00

theorem join84_01 : ChunkFacts (toRow data84.row) 1025 1024 (toTotals ⟨8210474559779, 210600540000, 1567483476807, 6853591622972, 2064152602⟩) :=
  CleanupSegments208.append_exact piece0681 piece0682 rfl rfl rfl
#print axioms join84_01

theorem join84_02 : ChunkFacts (toRow data84.row) 2049 1024 (toTotals ⟨530598254076, 69264177600, 425620001168, 174242430508, 820097016⟩) :=
  CleanupSegments208.append_exact piece0683 piece0684 rfl rfl rfl
#print axioms join84_02

theorem join84_03 : ChunkFacts (toRow data84.row) 1 2048 (toTotals ⟨982690292363874, 1184542237280, 18264024159475, 965610810441679, 8115398370⟩) :=
  CleanupSegments208.append_exact join84_00 join84_01 rfl rfl rfl
#print axioms join84_03

theorem join84_04 : ChunkFacts (toRow data84.row) 2049 1180 (toTotals ⟨580333568492, 78998602560, 483649753676, 175682417376, 933616087⟩) :=
  CleanupSegments208.append_exact join84_02 piece0685 rfl rfl rfl
#print axioms join84_04

theorem join84_05 : ChunkFacts (toRow data84.row) 1 3228 (toTotals ⟨983270625932366, 1263540839840, 18747673913151, 965786492859055, 9049014457⟩) :=
  CleanupSegments208.append_exact join84_03 join84_04 rfl rfl rfl
#print axioms join84_05

theorem fact84 : ChunkFacts (toRow data84.row) 1 data84.steps (toTotals data84.total) := join84_05
#print axioms fact84

theorem piece0686 : ChunkFacts (toRow data85.row) 1 512 (toTotals ⟨939227945482805, 1018988372784, 14307194725683, 925939739129906, 4226538904⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0686
#print axioms piece0686

theorem piece0687 : ChunkFacts (toRow data85.row) 513 512 (toTotals ⟨39643552742140, 459277657632, 2745725276037, 37357105123735, 2253226297⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G42.checked0687
#print axioms piece0687

theorem piece0688 : ChunkFacts (toRow data85.row) 1025 512 (toTotals ⟨8399453882432, 230453150904, 1209371856598, 7420535176738, 1454747665⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0688
#print axioms piece0688

theorem piece0689 : ChunkFacts (toRow data85.row) 1537 512 (toTotals ⟨2074576044132, 130020093384, 610247813237, 1594348324279, 958527414⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0689
#print axioms piece0689

theorem piece0690 : ChunkFacts (toRow data85.row) 2049 512 (toTotals ⟨544022611497, 66141049592, 300014941253, 310148719836, 548687755⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0690
#print axioms piece0690

theorem piece0691 : ChunkFacts (toRow data85.row) 2561 512 (toTotals ⟨182998343324, 46325878784, 190456623616, 38867598492, 411879119⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0691
#print axioms piece0691

theorem piece0692 : ChunkFacts (toRow data85.row) 3073 477 (toTotals ⟨144944283415, 43159070664, 177437127861, 10666226218, 389189948⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0692
#print axioms piece0692

theorem join85_00 : ChunkFacts (toRow data85.row) 1 1024 (toTotals ⟨978871498224945, 1478266030416, 17052920001720, 963296844253641, 6479765201⟩) :=
  CleanupSegments208.append_exact piece0686 piece0687 rfl rfl rfl
#print axioms join85_00

theorem join85_01 : ChunkFacts (toRow data85.row) 1025 1024 (toTotals ⟨10474029926564, 360473244288, 1819619669835, 9014883501017, 2413275079⟩) :=
  CleanupSegments208.append_exact piece0688 piece0689 rfl rfl rfl
#print axioms join85_01

theorem join85_02 : ChunkFacts (toRow data85.row) 2049 1024 (toTotals ⟨727020954821, 112466928376, 490471564869, 349016318328, 960566874⟩) :=
  CleanupSegments208.append_exact piece0690 piece0691 rfl rfl rfl
#print axioms join85_02

theorem join85_03 : ChunkFacts (toRow data85.row) 1 2048 (toTotals ⟨989345528151509, 1838739274704, 18872539671555, 972311727754658, 8893040280⟩) :=
  CleanupSegments208.append_exact join85_00 join85_01 rfl rfl rfl
#print axioms join85_03

theorem join85_04 : ChunkFacts (toRow data85.row) 2049 1501 (toTotals ⟨871965238236, 155625999040, 667908692730, 359682544546, 1349756822⟩) :=
  CleanupSegments208.append_exact join85_02 piece0692 rfl rfl rfl
#print axioms join85_04

theorem join85_05 : ChunkFacts (toRow data85.row) 1 3549 (toTotals ⟨990217493389745, 1994365273744, 19540448364285, 972671410299204, 10242797102⟩) :=
  CleanupSegments208.append_exact join85_03 join85_04 rfl rfl rfl
#print axioms join85_05

theorem fact85 : ChunkFacts (toRow data85.row) 1 data85.steps (toTotals data85.total) := join85_05
#print axioms fact85

theorem piece0693 : ChunkFacts (toRow data86.row) 1 512 (toTotals ⟨975460099360127, 1355818196448, 14677435566483, 962138481990092, 4467062258⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0693
#print axioms piece0693

theorem piece0694 : ChunkFacts (toRow data86.row) 513 512 (toTotals ⟨45448756028963, 642809008224, 3025799299218, 43065765737969, 2472520151⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0694
#print axioms piece0694

theorem piece0695 : ChunkFacts (toRow data86.row) 1025 512 (toTotals ⟨10074066977941, 330783248160, 1377224518928, 9027625707173, 1650492568⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0695
#print axioms piece0695

theorem piece0696 : ChunkFacts (toRow data86.row) 1537 512 (toTotals ⟨2635066719281, 184205272320, 685760888616, 2133511102985, 1096110484⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0696
#print axioms piece0696

theorem piece0697 : ChunkFacts (toRow data86.row) 2049 512 (toTotals ⟨951219939511, 112881889440, 415098567822, 649003261129, 747612457⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0697
#print axioms piece0697

theorem piece0698 : ChunkFacts (toRow data86.row) 2561 512 (toTotals ⟨182998343324, 57507987456, 190456623616, 50049707164, 432067791⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0698
#print axioms piece0698

theorem piece0699 : ChunkFacts (toRow data86.row) 3073 512 (toTotals ⟨154800393511, 57507987456, 190456623616, 21851757351, 450800153⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0699
#print axioms piece0699

theorem piece0700 : ChunkFacts (toRow data86.row) 3585 263 (toTotals ⟨71141522520, 29540235744, 97832210959, 2849547305, 228141901⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0700
#print axioms piece0700

theorem join86_00 : ChunkFacts (toRow data86.row) 1 1024 (toTotals ⟨1020908855389090, 1998627204672, 17703234865701, 1005204247728061, 6939582409⟩) :=
  CleanupSegments208.append_exact piece0693 piece0694 rfl rfl rfl
#print axioms join86_00

theorem join86_01 : ChunkFacts (toRow data86.row) 1025 1024 (toTotals ⟨12709133697222, 514988520480, 2062985407544, 11161136810158, 2746603052⟩) :=
  CleanupSegments208.append_exact piece0695 piece0696 rfl rfl rfl
#print axioms join86_01

theorem join86_02 : ChunkFacts (toRow data86.row) 2049 1024 (toTotals ⟨1134218282835, 170389876896, 605555191438, 699052968293, 1179680248⟩) :=
  CleanupSegments208.append_exact piece0697 piece0698 rfl rfl rfl
#print axioms join86_02

theorem join86_03 : ChunkFacts (toRow data86.row) 3073 775 (toTotals ⟨225941916031, 87048223200, 288288834575, 24701304656, 678942054⟩) :=
  CleanupSegments208.append_exact piece0699 piece0700 rfl rfl rfl
#print axioms join86_03

theorem join86_04 : ChunkFacts (toRow data86.row) 1 2048 (toTotals ⟨1033617989086312, 2513615725152, 19766220273245, 1016365384538219, 9686185461⟩) :=
  CleanupSegments208.append_exact join86_00 join86_01 rfl rfl rfl
#print axioms join86_04

theorem join86_05 : ChunkFacts (toRow data86.row) 2049 1799 (toTotals ⟨1360160198866, 257438100096, 893844026013, 723754272949, 1858622302⟩) :=
  CleanupSegments208.append_exact join86_02 join86_03 rfl rfl rfl
#print axioms join86_05

theorem join86_06 : ChunkFacts (toRow data86.row) 1 3847 (toTotals ⟨1034978149285178, 2771053825248, 20660064299258, 1017089138811168, 11544807763⟩) :=
  CleanupSegments208.append_exact join86_04 join86_05 rfl rfl rfl
#print axioms join86_06

theorem fact86 : ChunkFacts (toRow data86.row) 1 data86.steps (toTotals data86.total) := join86_06
#print axioms fact86

theorem piece0701 : ChunkFacts (toRow data87.row) 1 512 (toTotals ⟨997719140556644, 1649666789904, 14896875937983, 984471931408565, 4712428879⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0701
#print axioms piece0701

theorem piece0702 : ChunkFacts (toRow data87.row) 513 512 (toTotals ⟨50307364863750, 825423076464, 3277306696561, 47855481243653, 2697784328⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0702
#print axioms piece0702

theorem piece0703 : ChunkFacts (toRow data87.row) 1025 512 (toTotals ⟨11902881072805, 442916335680, 1558621192261, 10787176216224, 1862625460⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G43.checked0703
#print axioms piece0703

theorem piece0704 : ChunkFacts (toRow data87.row) 1537 512 (toTotals ⟨3273958270380, 245438549328, 772433531785, 2746963287923, 1248873956⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0704
#print axioms piece0704

theorem piece0705 : ChunkFacts (toRow data87.row) 2049 512 (toTotals ⟨1296465042855, 160393371264, 508244382946, 948614031173, 926720999⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0705
#print axioms piece0705

theorem piece0706 : ChunkFacts (toRow data87.row) 2561 512 (toTotals ⟨270276198890, 79934604960, 226911211730, 123299592120, 511999069⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0706
#print axioms piece0706

theorem piece0707 : ChunkFacts (toRow data87.row) 3073 512 (toTotals ⟨154800393511, 67092652032, 190456623616, 31436421927, 471250457⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0707
#print axioms piece0707

theorem piece0708 : ChunkFacts (toRow data87.row) 3585 512 (toTotals ⟨134160011815, 67092652032, 190456623616, 10796040231, 493146392⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0708
#print axioms piece0708

theorem piece0709 : ChunkFacts (toRow data87.row) 4097 49 (toTotals ⟨11953560040, 6420976464, 18227294057, 147242447, 34838814⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0709
#print axioms piece0709

theorem join87_00 : ChunkFacts (toRow data87.row) 1 1024 (toTotals ⟨1048026505420394, 2475089866368, 18174182634544, 1032327412652218, 7410213207⟩) :=
  CleanupSegments208.append_exact piece0701 piece0702 rfl rfl rfl
#print axioms join87_00

theorem join87_01 : ChunkFacts (toRow data87.row) 1025 1024 (toTotals ⟨15176839343185, 688354885008, 2331054724046, 13534139504147, 3111499416⟩) :=
  CleanupSegments208.append_exact piece0703 piece0704 rfl rfl rfl
#print axioms join87_01

theorem join87_02 : ChunkFacts (toRow data87.row) 2049 1024 (toTotals ⟨1566741241745, 240327976224, 735155594676, 1071913623293, 1438720068⟩) :=
  CleanupSegments208.append_exact piece0705 piece0706 rfl rfl rfl
#print axioms join87_02

theorem join87_03 : ChunkFacts (toRow data87.row) 3073 1024 (toTotals ⟨288960405326, 134185304064, 380913247232, 42232462158, 964396849⟩) :=
  CleanupSegments208.append_exact piece0707 piece0708 rfl rfl rfl
#print axioms join87_03

theorem join87_04 : ChunkFacts (toRow data87.row) 1 2048 (toTotals ⟨1063203344763579, 3163444751376, 20505237358590, 1045861552156365, 10521712623⟩) :=
  CleanupSegments208.append_exact join87_00 join87_01 rfl rfl rfl
#print axioms join87_04

theorem join87_05 : ChunkFacts (toRow data87.row) 2049 2048 (toTotals ⟨1855701647071, 374513280288, 1116068841908, 1114146085451, 2403116917⟩) :=
  CleanupSegments208.append_exact join87_02 join87_03 rfl rfl rfl
#print axioms join87_05

theorem join87_06 : ChunkFacts (toRow data87.row) 1 4096 (toTotals ⟨1065059046410650, 3537958031664, 21621306200498, 1046975698241816, 12924829540⟩) :=
  CleanupSegments208.append_exact join87_04 join87_05 rfl rfl rfl
#print axioms join87_06

theorem join87_07 : ChunkFacts (toRow data87.row) 1 4145 (toTotals ⟨1065070999970690, 3544379008128, 21639533494555, 1046975845484263, 12959668354⟩) :=
  CleanupSegments208.append_exact join87_06 piece0709 rfl rfl rfl
#print axioms join87_07

theorem fact87 : ChunkFacts (toRow data87.row) 1 data87.steps (toTotals data87.total) := join87_07
#print axioms fact87

theorem piece0710 : ChunkFacts (toRow data88.row) 1 512 (toTotals ⟨999802448294333, 1874064005280, 14993349389927, 986683162909686, 4871935664⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0710
#print axioms piece0710

theorem piece0711 : ChunkFacts (toRow data88.row) 513 512 (toTotals ⟨53111819932135, 972518973632, 3434091620242, 50650247285525, 2851692419⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0711
#print axioms piece0711

theorem piece0712 : ChunkFacts (toRow data88.row) 1025 512 (toTotals ⟨13271718566062, 541249627816, 1689876075356, 12123092118522, 2018649545⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0712
#print axioms piece0712

theorem piece0713 : ChunkFacts (toRow data88.row) 1537 512 (toTotals ⟨3516861565690, 289321461848, 810004076679, 2996178950859, 1326848279⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0713
#print axioms piece0713

theorem piece0714 : ChunkFacts (toRow data88.row) 2049 512 (toTotals ⟨1719954549160, 213215106704, 604742737678, 1328426918186, 1106888547⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0714
#print axioms piece0714

theorem piece0715 : ChunkFacts (toRow data88.row) 2561 512 (toTotals ⟨360816014703, 105141149592, 266713670181, 199243494114, 603298857⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0715
#print axioms piece0715

theorem piece0716 : ChunkFacts (toRow data88.row) 3073 512 (toTotals ⟨154800393511, 75079872512, 190456623616, 39423642407, 488292377⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0716
#print axioms piece0716

theorem piece0717 : ChunkFacts (toRow data88.row) 3585 512 (toTotals ⟨134160011815, 75079872512, 190456623616, 18783260711, 512809752⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0717
#print axioms piece0717

theorem piece0718 : ChunkFacts (toRow data88.row) 4097 335 (toTotals ⟨79019439327, 49124525960, 124615173655, 3528791632, 332227182⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0718
#print axioms piece0718

theorem join88_00 : ChunkFacts (toRow data88.row) 1 1024 (toTotals ⟨1052914268226468, 2846582978912, 18427441010169, 1037333410195211, 7723628083⟩) :=
  CleanupSegments208.append_exact piece0710 piece0711 rfl rfl rfl
#print axioms join88_00

theorem join88_01 : ChunkFacts (toRow data88.row) 1025 1024 (toTotals ⟨16788580131752, 830571089664, 2499880152035, 15119271069381, 3345497824⟩) :=
  CleanupSegments208.append_exact piece0712 piece0713 rfl rfl rfl
#print axioms join88_01

theorem join88_02 : ChunkFacts (toRow data88.row) 2049 1024 (toTotals ⟨2080770563863, 318356256296, 871456407859, 1527670412300, 1710187404⟩) :=
  CleanupSegments208.append_exact piece0714 piece0715 rfl rfl rfl
#print axioms join88_02

theorem join88_03 : ChunkFacts (toRow data88.row) 3073 1024 (toTotals ⟨288960405326, 150159745024, 380913247232, 58206903118, 1001102129⟩) :=
  CleanupSegments208.append_exact piece0716 piece0717 rfl rfl rfl
#print axioms join88_03

theorem join88_04 : ChunkFacts (toRow data88.row) 1 2048 (toTotals ⟨1069702848358220, 3677154068576, 20927321162204, 1052452681264592, 11069125907⟩) :=
  CleanupSegments208.append_exact join88_00 join88_01 rfl rfl rfl
#print axioms join88_04

theorem join88_05 : ChunkFacts (toRow data88.row) 2049 2048 (toTotals ⟨2369730969189, 468516001320, 1252369655091, 1585877315418, 2711289533⟩) :=
  CleanupSegments208.append_exact join88_02 join88_03 rfl rfl rfl
#print axioms join88_05

theorem join88_06 : ChunkFacts (toRow data88.row) 1 4096 (toTotals ⟨1072072579327409, 4145670069896, 22179690817295, 1054038558580010, 13780415440⟩) :=
  CleanupSegments208.append_exact join88_04 join88_05 rfl rfl rfl
#print axioms join88_06

theorem join88_07 : ChunkFacts (toRow data88.row) 1 4431 (toTotals ⟨1072151598766736, 4194794595856, 22304305990950, 1054042087371642, 14112642622⟩) :=
  CleanupSegments208.append_exact join88_06 piece0718 rfl rfl rfl
#print axioms join88_07

theorem fact88 : ChunkFacts (toRow data88.row) 1 data88.steps (toTotals data88.total) := join88_07
#print axioms fact88

theorem piece0719 : ChunkFacts (toRow data89.row) 1 512 (toTotals ⟨1020559350270626, 2125187209184, 15199535245606, 1007485002234204, 5031881227⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G44.checked0719
#print axioms piece0719

theorem piece0720 : ChunkFacts (toRow data89.row) 513 512 (toTotals ⟨55320663027390, 1118809908736, 3561527036249, 52877945899877, 3003043800⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0720
#print axioms piece0720

theorem piece0721 : ChunkFacts (toRow data89.row) 1025 512 (toTotals ⟨14528342496217, 646365817344, 1809661662064, 13365046651497, 2162581330⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0721
#print axioms piece0721

theorem piece0722 : ChunkFacts (toRow data89.row) 1537 512 (toTotals ⟨4041747255394, 350439298560, 886261123262, 3505925430692, 1445586495⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0722
#print axioms piece0722

theorem piece0723 : ChunkFacts (toRow data89.row) 2049 512 (toTotals ⟨2098364724334, 268507888480, 688235604468, 1678637008346, 1275388887⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0723
#print axioms piece0723

theorem piece0724 : ChunkFacts (toRow data89.row) 2561 512 (toTotals ⟨447452448637, 133199381536, 305400171853, 275251658320, 703126003⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0724
#print axioms piece0724

theorem piece0725 : ChunkFacts (toRow data89.row) 3073 512 (toTotals ⟨189509620213, 90530152128, 207567960894, 72471811447, 537058915⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0725
#print axioms piece0725

theorem piece0726 : ChunkFacts (toRow data89.row) 3585 512 (toTotals ⟨134160011815, 83067092992, 190456623616, 26770481191, 532473112⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0726
#print axioms piece0726

theorem piece0727 : ChunkFacts (toRow data89.row) 4097 512 (toTotals ⟨118392124770, 83067092992, 190456623616, 11002594146, 559599084⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0727
#print axioms piece0727

theorem piece0728 : ChunkFacts (toRow data89.row) 4609 151 (toTotals ⟨32425447698, 24498302816, 56169824543, 753925971, 150047970⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0728
#print axioms piece0728

theorem join89_00 : ChunkFacts (toRow data89.row) 1 1024 (toTotals ⟨1075880013298016, 3243997117920, 18761062281855, 1060362948134081, 8034925027⟩) :=
  CleanupSegments208.append_exact piece0719 piece0720 rfl rfl rfl
#print axioms join89_00

theorem join89_01 : ChunkFacts (toRow data89.row) 1025 1024 (toTotals ⟨18570089751611, 996805115904, 2695922785326, 16870972082189, 3608167825⟩) :=
  CleanupSegments208.append_exact piece0721 piece0722 rfl rfl rfl
#print axioms join89_01

theorem join89_02 : ChunkFacts (toRow data89.row) 2049 1024 (toTotals ⟨2545817172971, 401707270016, 993635776321, 1953888666666, 1978514890⟩) :=
  CleanupSegments208.append_exact piece0723 piece0724 rfl rfl rfl
#print axioms join89_02

theorem join89_03 : ChunkFacts (toRow data89.row) 3073 1024 (toTotals ⟨323669632028, 173597245120, 398024584510, 99242292638, 1069532027⟩) :=
  CleanupSegments208.append_exact piece0725 piece0726 rfl rfl rfl
#print axioms join89_03

theorem join89_04 : ChunkFacts (toRow data89.row) 4097 663 (toTotals ⟨150817572468, 107565395808, 246626448159, 11756520117, 709647054⟩) :=
  CleanupSegments208.append_exact piece0727 piece0728 rfl rfl rfl
#print axioms join89_04

theorem join89_05 : ChunkFacts (toRow data89.row) 1 2048 (toTotals ⟨1094450103049627, 4240802233824, 21456985067181, 1077233920216270, 11643092852⟩) :=
  CleanupSegments208.append_exact join89_00 join89_01 rfl rfl rfl
#print axioms join89_05

theorem join89_06 : ChunkFacts (toRow data89.row) 2049 2048 (toTotals ⟨2869486804999, 575304515136, 1391660360831, 2053130959304, 3048046917⟩) :=
  CleanupSegments208.append_exact join89_02 join89_03 rfl rfl rfl
#print axioms join89_06

theorem join89_07 : ChunkFacts (toRow data89.row) 1 4096 (toTotals ⟨1097319589854626, 4816106748960, 22848645428012, 1079287051175574, 14691139769⟩) :=
  CleanupSegments208.append_exact join89_05 join89_06 rfl rfl rfl
#print axioms join89_07

theorem join89_08 : ChunkFacts (toRow data89.row) 1 4759 (toTotals ⟨1097470407427094, 4923672144768, 23095271876171, 1079298807695691, 15400786823⟩) :=
  CleanupSegments208.append_exact join89_07 join89_04 rfl rfl rfl
#print axioms join89_08

theorem fact89 : ChunkFacts (toRow data89.row) 1 data89.steps (toTotals data89.total) := join89_08
#print axioms fact89

theorem piece0729 : ChunkFacts (toRow data90.row) 1 512 (toTotals ⟨1038469101636676, 2360997413824, 15394628459642, 1025435470590858, 5184579736⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0729
#print axioms piece0729

theorem piece0730 : ChunkFacts (toRow data90.row) 513 512 (toTotals ⟨59267414623211, 1281749206528, 3754055261758, 56795108567981, 3145838547⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0730
#print axioms piece0730

theorem piece0731 : ChunkFacts (toRow data90.row) 1025 512 (toTotals ⟨15688980255773, 740290538176, 1912941360839, 14516329433110, 2287688267⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0731
#print axioms piece0731

theorem piece0732 : ChunkFacts (toRow data90.row) 1537 512 (toTotals ⟨4650135656369, 413213859520, 972395243390, 4090954272499, 1573747492⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0732
#print axioms piece0732

theorem piece0733 : ChunkFacts (toRow data90.row) 2049 512 (toTotals ⟨2379599733665, 312924322368, 741930713159, 1950593342874, 1400611751⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0733
#print axioms piece0733

theorem piece0734 : ChunkFacts (toRow data90.row) 2561 512 (toTotals ⟨577383081328, 162140575744, 351264906007, 388258751065, 800326566⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0734
#print axioms piece0734

theorem piece0735 : ChunkFacts (toRow data90.row) 3073 512 (toTotals ⟨261797832788, 114791334336, 244394534601, 132194632523, 631121331⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G45.checked0735
#print axioms piece0735

theorem piece0736 : ChunkFacts (toRow data90.row) 3585 512 (toTotals ⟨134160011815, 89456869376, 190456623616, 33160257575, 548203800⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G46.checked0736
#print axioms piece0736

theorem piece0737 : ChunkFacts (toRow data90.row) 4097 512 (toTotals ⟨118392124770, 89456869376, 190456623616, 17392370530, 577426924⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G46.checked0737
#print axioms piece0737

theorem piece0738 : ChunkFacts (toRow data90.row) 4609 451 (toTotals ⟨93904385674, 78798922048, 167765502443, 4937805279, 508419433⟩) :=
  CleanupFastSound208.check_sound CleanupChecks291012G46.checked0738
#print axioms piece0738

theorem join90_00 : ChunkFacts (toRow data90.row) 1 1024 (toTotals ⟨1097736516259887, 3642746620352, 19148683721400, 1082230579158839, 8330418283⟩) :=
  CleanupSegments208.append_exact piece0729 piece0730 rfl rfl rfl
#print axioms join90_00

theorem join90_01 : ChunkFacts (toRow data90.row) 1025 1024 (toTotals ⟨20339115912142, 1153504397696, 2885336604229, 18607283705609, 3861435759⟩) :=
  CleanupSegments208.append_exact piece0731 piece0732 rfl rfl rfl
#print axioms join90_01

theorem join90_02 : ChunkFacts (toRow data90.row) 2049 1024 (toTotals ⟨2956982814993, 475064898112, 1093195619166, 2338852093939, 2200938317⟩) :=
  CleanupSegments208.append_exact piece0733 piece0734 rfl rfl rfl
#print axioms join90_02

theorem join90_03 : ChunkFacts (toRow data90.row) 3073 1024 (toTotals ⟨395957844603, 204248203712, 434851158217, 165354890098, 1179325131⟩) :=
  CleanupSegments208.append_exact piece0735 piece0736 rfl rfl rfl
#print axioms join90_03

theorem join90_04 : ChunkFacts (toRow data90.row) 4097 963 (toTotals ⟨212296510444, 168255791424, 358222126059, 22330175809, 1085846357⟩) :=
  CleanupSegments208.append_exact piece0737 piece0738 rfl rfl rfl
#print axioms join90_04

theorem join90_05 : ChunkFacts (toRow data90.row) 1 2048 (toTotals ⟨1118075632172029, 4796251018048, 22034020325629, 1100837862864448, 12191854042⟩) :=
  CleanupSegments208.append_exact join90_00 join90_01 rfl rfl rfl
#print axioms join90_05

theorem join90_06 : ChunkFacts (toRow data90.row) 2049 2048 (toTotals ⟨3352940659596, 679313101824, 1528046777383, 2504206984037, 3380263448⟩) :=
  CleanupSegments208.append_exact join90_02 join90_03 rfl rfl rfl
#print axioms join90_06

theorem join90_07 : ChunkFacts (toRow data90.row) 1 4096 (toTotals ⟨1121428572831625, 5475564119872, 23562067103012, 1103342069848485, 15572117490⟩) :=
  CleanupSegments208.append_exact join90_05 join90_06 rfl rfl rfl
#print axioms join90_07

theorem join90_08 : ChunkFacts (toRow data90.row) 1 5059 (toTotals ⟨1121640869342069, 5643819911296, 23920289229071, 1103364400024294, 16657963847⟩) :=
  CleanupSegments208.append_exact join90_07 join90_04 rfl rfl rfl
#print axioms join90_08

theorem fact90 : ChunkFacts (toRow data90.row) 1 data90.steps (toTotals data90.total) := join90_08
#print axioms fact90

theorem all_facts {k : ℕ} (hk : k < 91) : ChunkFacts (toRow (data k).row) 1 (data k).steps (toTotals (data k).total) := by
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
  · exact fact88
  · exact fact89
  · exact fact90

#print axioms all_facts
end JSP233.CleanupFacts291012
