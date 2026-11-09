module

public import Erdos272.Arithmetic.LightValues209
public import Erdos272.Resources.LightUnweighted209
public import Erdos272.Arithmetic.CappedValues209
public import Erdos272.Resources.IntegerUniformShape209
public import Erdos272.Arithmetic.IntegerLightLog209
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace JSP233.IntegerUniformLight209
open StarCompletion APGeometry SevenFamily208
open CrossBandCredit208 CrossBandCredit208.System CrossBandCleanup208
open IntegerUniformProfiles209 IntegerUniformRows209 IntegerHighPrices209
open LightAnalytic209 ActualLightAnalytic209
local notation "Grid" => ResidualCeil208.Grid
open scoped Classical BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 65536

def residualUnits (w : Fin 11) (k : ℕ) : ℕ := ((#[#[6216613031,6214811832,6217955785,6221696603,6225203713,6233431734,6243471894,6252522180,6264005155,6272564643,6281973006,6288781337,6297975623,6305944005,6314525339,6323793179,6333833340,6344746558,6356651887,6373147222,6380315565,6387846862,6395769396,6404114464,6412916797,6422215036,6432052303,6442476869,6453542948,6465311634,6477852038,6484435750],#[6114052177,6120632992,6133607299,6151065974,6167474149,6185802090,6202172275,6219148762,6236348625,6253244798,6272583791,6299005266,6316409889,6335862114,6357745868,6376042121],#[5968811408,5975241425,5987343126,6003532677,6018664088,6037020225,6052202463,6070012395,6083703023,6099179386,6119996611,6140776191,6160666556,6178624713,6198759617,6215538703],#[5763472039,5769244745,5781326268,5796013791,5810806979,5827487054,5841206169,5857211803,5871632721,5885684983,5904501176,5926569550,5940981550,5961248424,5979607828,5994860255],#[5476165329,5500689530,5528897138,5555999265,5587057155,5618023698,5647666014,5680601921],#[5053594723,5073989595,5098418626,5120714201,5148042205,5172137865,5200420880,5226271695],#[4482157203,4498728503,4517728064,4535889410,4557436769,4577450950,4599454119,4620131795],#[3745997705,3757500709,3770978472,3783511894,3798682372,3812981160,3828075174,3842929600],#[2867583356,2874518675,2882482584,2889904425,2898848874,2907286153,2916120355,2925380163],#[1919177160,1922263057,1925847872,1929176497,1933178068,1936993697,1940994977,1945091693],#[1055708977,1056658037,1057758771,1058792704,1060022851,1061184060,1062391330,1063689335]])[w.val]!)[k]!
def lightUnits (w : Fin 11) (k : ℕ) (b : Fin 7) : ℕ := (((#[#[#[12060135436,2827827367,865757138,245142629,73692168,0,0],#[13976615580,3418832366,996715065,262356897,77215377,23292497,0],#[16841492598,3506976320,1004008721,262875478,77228543,23293142,0],#[18576370153,4368947629,1164785597,282641942,81106910,24754462,9030716],#[21467173159,4448698925,1170358883,283069329,81121435,24755183,9030716],#[24509225242,5015806388,1318566597,357317740,101483569,31698727,11100871],#[27471282395,5148462373,1327704481,358820751,101517677,31699889,11100871],#[28984622474,5887040743,1568447087,418648675,135655715,43853687,14191379],#[32766490758,6033582349,1578815070,419418911,135736954,43855852,14191379],#[35598292064,6109413634,1584045834,419804987,135777606,43858018,14191624],#[38835837719,6226532804,1591951233,420385304,135838625,43860183,14191624],#[40324783705,6785582474,1714921103,487595208,164446101,60704279,22101484],#[44332666113,6389323197,1602603874,421161314,135920061,43862349,14191869],#[46285971312,7030409150,1727532461,488655544,164629862,60712583,22102031],#[49551744734,7132978106,1733901518,489187295,164691199,60716735,22102031],#[53193587672,7292122010,1740313393,489720105,164783283,60720888,22102578],#[57272992490,7401918977,1746768515,490253978,164875461,60725042,22102578],#[61864740805,7514825131,1750012430,490521313,164967733,60729196,22102578],#[67060254663,7690312976,1756533243,491056785,165029300,60733351,22103125],#[75281009700,7811603437,1763098406,491593327,165152560,60737506,22103125],#[78712888040,7936514782,1766397759,491862000,165183401,60741662,22103125],#[82395581427,8000380067,1769708370,492130943,165245115,60741662,22103671],#[86354711609,8065214006,1773030295,492400154,165275988,60745818,22103671],#[90619181489,8131039137,1776363592,492669635,165337766,60745818,22103671],#[95221186383,8197878712,1779708320,492939386,165368670,60749975,22103671],#[98142138994,9224489037,2054361455,608358060,207134423,67701204,22103671],#[103452597082,9311938568,2058889441,608767292,207228778,67706262,22104218],#[109224549303,9491630048,2063435667,609177028,207323209,67706262,22104218],#[115513185718,9583962042,2068000245,609587269,207417719,67711321,22104218],#[122383098879,9678014459,2072583285,609998016,207512306,67716380,22104218],#[129909809552,9773836786,2077184899,610409271,207559629,67716380,22104218],#[132200335569,9871480457,2077184899,610409271,207559629,67721440,22104218]],#[#[13790816936,3370334086,981347770,258208099,75998877,22925667,0],#[18223310294,4309522218,1146625321,278235218,79828623,24364594,8888496],#[24637519443,4973903052,1299549247,351974675,99893595,31199427,10926046],#[28624365995,5789062717,1543367821,412027477,133529946,43162742,13967878],#[34094423531,6004000103,1558470225,413147474,133628347,43166938,13968115],#[39586200839,6725479101,1690004249,480092931,161862327,59747083,21753370],#[45329012424,6965636732,1702247818,481120793,162010659,59755127,21753900],#[51957315012,7169470100,1711536753,481894334,162188985,59763173,21754429],#[59579914995,7384639807,1720918270,482670152,162337864,59771221,21754429],#[67104698894,7612130744,1730393751,483448258,162457147,59775246,21754959],#[76226870561,7791494192,1736763637,483968272,162576590,59783297,21754959],#[88644232658,8043287628,1746398874,484750213,162726119,59791350,21755489],#[95854285321,9103300044,2024148647,598923452,203892201,66637356,21756018],#[106443232564,9363290065,2032955671,599717167,204075118,66642256,21756018],#[118971111658,9544573469,2037385448,600114748,204212499,66647157,21756018],#[131628704151,9732647360,2046298054,600911358,204304180,66652059,21756548]],#[#[13431641838,3290982645,958686203,252225230,74244338,22396585,0],#[17901834019,4198012067,1119780962,271758471,77984997,23802287,8683373],#[24031379128,4834410797,1268658957,343811498,97584138,30479288,10673897],#[27762437307,5631618100,1506028539,402390450,130435185,42166206,13645521],#[32903076510,5834964634,1520409006,403458673,130547872,42170210,13645747],#[38340441558,6508866590,1648152183,468773068,158121251,58366582,21251286],#[44322865809,6733902560,1659798660,469753071,158262804,58374259,21251791],#[51147680454,6973801970,1671595571,470736828,158432972,58385777,21252297],#[56957469966,7177397974,1680543728,471477121,158575035,58389617,21252297],#[63871745889,7337477016,1686557706,471971834,158688852,58397299,21252802],#[74425411038,7561537703,1695652431,472715687,158831334,58404983,21253308],#[85089855575,7798729132,1704836822,473461686,158945488,58408826,21253308],#[92965624362,8905092809,1975013367,584929424,199171203,65095815,21253813],#[102933731180,9069390838,1983399092,585686499,199345746,65105168,21253813],#[114670497203,9326892664,1987616357,586065709,199476835,65109846,21254319],#[126469070141,9415837830,1996100163,586825479,199564314,65114524,21254319]],#[#[13009572192,3176583297,926143488,243817170,71759343,21647218,0],#[17112137506,4047737910,1081193087,262663345,75380151,23006486,8392844],#[23277230465,4676967081,1225766282,332429438,94323282,29459326,10316764],#[27004910020,5426045183,1454395420,388834418,126070508,40756664,13188950],#[32073168821,5614678472,1467804901,389831847,126175777,40760404,13189162],#[37172670916,6292233476,1593976085,453102390,152836235,56415024,20540634],#[42767799796,6502322716,1604865805,454017905,152968478,56422196,20540634],#[49101562365,6772211309,1615891488,454936807,153127447,56429369,20541106],#[55862049924,6963936644,1624251505,455628220,153260151,56436544,20541578],#[62456836107,7114470724,1629868674,456090230,153366466,56443721,20541578],#[71186809567,7324858907,1638360991,456784854,153499549,56450899,20542051],#[83579585807,7547179532,1646934191,457481415,153659527,56454489,20542523],#[89811348192,8606460468,1906794908,565123004,192485865,62917116,20542523],#[100548997911,8838472018,1914611769,565829698,192689681,62925853,20542995],#[111670129452,8999842060,1922487295,566538010,192812158,62930222,20542995],#[122797236093,9166905594,1926447263,566892776,192853015,62934592,20542995]],#[#[16548288792,3844107726,1027742646,249695153,71648148,21868239,7977642],#[25817571062,5158846887,1382535866,369605478,119839929,38739466,12536453],#[35585364430,6005729184,1513667611,430567758,145279959,53624042,19524312],#[47437435239,6441253693,1533421440,432224020,145567025,53640244,19525165],#[62640707523,6843442071,1551094075,433682835,145831080,53653212,19525592],#[79741665270,7190017233,1563945765,434730371,146047777,53662942,19526019],#[94979072289,8368863733,1817548788,537589901,183167471,59813207,19526445],#[116499297043,8739474591,1831794439,538870072,183315053,59821103,19526872]],#[#[15142569791,3545229499,949684907,230945339,66263738,20224391,7378004],#[23633658942,4735965075,1276051938,341632283,110823113,35827829,11594281],#[32981989156,5557135607,1396144888,397944342,134347306,49594290,18056926],#[43333727284,5928140146,1415069186,399536378,134613256,49608148,18057291],#[57794488497,6307425784,1432286082,400961329,134880168,49619239,18058021],#[72137961387,6600887068,1443241319,401856652,135065521,49627561,18058386],#[88165219288,7768780351,1680310787,497066056,169386500,55316870,18058751],#[106453356769,8087045907,1689422955,497886374,169481138,55323624,18059116]],#[#[13482377232,3144847588,844086520,205412716,58942503,17990112,6562978],#[21221890163,4202617059,1134342878,303837554,98588032,31870687,10313437],#[29238751309,4925693730,1239999397,353822283,119513480,44116166,16062232],#[38440514105,5271363414,1256588143,355220747,119756331,44127131,16062809],#[51056673182,5632687969,1271866279,356488033,119983806,44138101,16063098],#[64238194763,5900241665,1282240632,357337494,120146772,44146881,16063675],#[78746272784,6855616123,1490060670,441828820,150637215,49205709,16063964],#[96034511643,7153989199,1499628864,442693344,150737025,49213726,16064253]],#[#[11316379935,2616935082,706865982,172356613,49456081,15094206,5506523],#[17714497515,3510360354,948686243,254697237,82712674,26739731,8653229],#[24401261109,4124204581,1038187056,296678004,100272013,37013014,13476418],#[32230218419,4403324610,1050971114,297759363,100465738,37023820,13477027],#[42890697263,4697227661,1064044136,298847951,100660148,37033087,13477434],#[53879671921,4930473770,1072518271,299544486,100809278,37040813,13477637],#[65694276973,5757791847,1245505886,370300264,126341465,41284758,13478044],#[80348026111,5966857309,1252189146,370907464,126411674,41290401,13478247]],#[#[8672875679,1998585444,542655703,132574498,38042341,11611007,4473962],#[13654840895,2695748329,728086305,195794662,63629153,20569119,7041885],#[18903448774,3175532357,795825779,227959017,77128279,28471549,10964128],#[24774261619,3396497510,806081126,228829908,77283364,28479771,10964514],#[33039888613,3621105998,815871531,229648245,77432239,28487082,10964771],#[41730697981,3786811111,822280232,230177150,77540841,28492568,10965157],#[50802248805,4427475852,954493430,284496967,97145273,31757729,10965285],#[61927128079,4613889147,960389153,285034816,97207547,31762181,10965543]],#[#[5823714270,1334349593,364371806,89218874,25601559,7813944,3960389],#[9143964721,1812616470,488221986,131632020,42818854,13842558,6207785],#[12647889569,2134213850,533389522,153235897,51904224,19160798,9581557],#[16618150762,2278724925,540461080,153839485,52008048,19166176,9581944],#[22046937414,2424544541,546749968,154367887,52106111,19170729,9582254],#[27787535322,2542548374,550909499,154713132,52182958,19174456,9582486],#[33977063230,2966064390,639239965,191174438,65343592,21371568,9582718],#[41524470636,3096486034,643210028,191538833,65385860,21375096,9582873]],#[#[3227323949,731753489,201076218,49343624,14159383,4321655,2505436],#[5069025639,1000700501,269226222,72741465,23682224,7655871,3903287],#[6996650652,1177917125,294068085,84669937,28707861,10597330,5983483],#[9233554402,1260057126,297901147,84998472,28764842,10600240,5983697],#[12232336143,1340660666,301342260,85288869,28820152,10602899,5983911],#[15458511542,1405199413,303676707,85483476,28860585,10604926,5984071],#[18773260886,1638175115,352031592,105597013,36123908,11820112,5984205],#[23038286801,1709188950,354308120,105807076,36148311,11822116,5984312]]])[w.val]!)[k]!)[b.val]!
def etaLight (w : Fin 11) (k : ℕ) : ℕ := ((#[#[248,292,302,336,346,351,357,357,364,368,373,373,381,382,386,391,396,401,408,417,421,424,428,432,436,439,443,449,454,459,465,465],#[292,336,352,357,367,374,382,390,400,409,419,431,437,447,457,468],#[292,337,352,356,366,372,382,391,398,407,419,430,437,446,456,466],#[292,336,352,357,366,373,382,391,400,408,418,431,438,447,456,467],#[429,455,476,500,526,552,570,595],#[428,454,477,499,526,549,571,593],#[428,455,476,498,525,548,570,596],#[428,454,475,498,525,548,570,595],#[431,459,483,505,532,556,578,601],#[459,499,538,561,587,610,633,657],#[485,536,589,612,638,662,683,707]])[w.val]!)[k]!
def uUnits (w : Fin 11) : ℕ := [634,641,621,602,609,560,498,417,322,216,120].getD w.val 0
def cut (w : Fin 11) (k : ℕ) : ℕ := max 1 (min ((row w k).e-1) (M w/3))
def alphaUnits (w : Fin 11) (k : ℕ) : ℕ := residualUnits w k+∑b : Fin 7,lightUnits w k b

def LightFacts (w : Fin 11) : Prop := ∀i : Fin (count w),∀b : Fin 7,
  let q:=band (row w i.val) b
  (q.E≤1 → lightUnits w i.val b=0) ∧
  (1<q.E → (q.T-q.E,q.b2,q.U+q.b2,q.E,lightUnits w i.val b)∈LightValues209.data) ∧
  q.T-q.E≤Upper w
instance (w : Fin 11) : Decidable (LightFacts w) := by unfold LightFacts;infer_instance
private abbrev LightRowFacts (w : Fin 11) (k : ℕ) : Prop := ∀b : Fin 7,
  let q:=band (row w k) b
  (q.E≤1 → lightUnits w k b=0) ∧
  (1<q.E → (q.T-q.E,q.b2,q.U+q.b2,q.E,lightUnits w k b)∈LightValues209.data) ∧
  q.T-q.E≤Upper w

private theorem light_row_00_000 : LightRowFacts 0 0 := by decide +kernel

private theorem light_row_00_001 : LightRowFacts 0 1 := by decide +kernel

private theorem light_row_00_002 : LightRowFacts 0 2 := by decide +kernel

private theorem light_row_00_003 : LightRowFacts 0 3 := by decide +kernel

private theorem light_row_00_004 : LightRowFacts 0 4 := by decide +kernel

private theorem light_row_00_005 : LightRowFacts 0 5 := by decide +kernel

private theorem light_row_00_006 : LightRowFacts 0 6 := by decide +kernel

private theorem light_row_00_007 : LightRowFacts 0 7 := by decide +kernel

private theorem light_row_00_008 : LightRowFacts 0 8 := by decide +kernel

private theorem light_row_00_009 : LightRowFacts 0 9 := by decide +kernel

private theorem light_row_00_010 : LightRowFacts 0 10 := by decide +kernel

private theorem light_row_00_011 : LightRowFacts 0 11 := by decide +kernel

private theorem light_row_00_012 : LightRowFacts 0 12 := by decide +kernel

private theorem light_row_00_013 : LightRowFacts 0 13 := by decide +kernel

private theorem light_row_00_014 : LightRowFacts 0 14 := by decide +kernel

private theorem light_row_00_015 : LightRowFacts 0 15 := by decide +kernel

private theorem light_row_00_016 : LightRowFacts 0 16 := by decide +kernel

private theorem light_row_00_017 : LightRowFacts 0 17 := by decide +kernel

private theorem light_row_00_018 : LightRowFacts 0 18 := by decide +kernel

private theorem light_row_00_019 : LightRowFacts 0 19 := by decide +kernel

private theorem light_row_00_020 : LightRowFacts 0 20 := by decide +kernel

private theorem light_row_00_021 : LightRowFacts 0 21 := by decide +kernel

private theorem light_row_00_022 : LightRowFacts 0 22 := by decide +kernel

private theorem light_row_00_023 : LightRowFacts 0 23 := by decide +kernel

private theorem light_row_00_024 : LightRowFacts 0 24 := by decide +kernel

private theorem light_row_00_025 : LightRowFacts 0 25 := by decide +kernel

private theorem light_row_00_026 : LightRowFacts 0 26 := by decide +kernel

private theorem light_row_00_027 : LightRowFacts 0 27 := by decide +kernel

private theorem light_row_00_028 : LightRowFacts 0 28 := by decide +kernel

private theorem light_row_00_029 : LightRowFacts 0 29 := by decide +kernel

private theorem light_row_00_030 : LightRowFacts 0 30 := by decide +kernel

private theorem light_row_00_031 : LightRowFacts 0 31 := by decide +kernel

private theorem light_row_01_000 : LightRowFacts 1 0 := by decide +kernel

private theorem light_row_01_001 : LightRowFacts 1 1 := by decide +kernel

private theorem light_row_01_002 : LightRowFacts 1 2 := by decide +kernel

private theorem light_row_01_003 : LightRowFacts 1 3 := by decide +kernel

private theorem light_row_01_004 : LightRowFacts 1 4 := by decide +kernel

private theorem light_row_01_005 : LightRowFacts 1 5 := by decide +kernel

private theorem light_row_01_006 : LightRowFacts 1 6 := by decide +kernel

private theorem light_row_01_007 : LightRowFacts 1 7 := by decide +kernel

private theorem light_row_01_008 : LightRowFacts 1 8 := by decide +kernel

private theorem light_row_01_009 : LightRowFacts 1 9 := by decide +kernel

private theorem light_row_01_010 : LightRowFacts 1 10 := by decide +kernel

private theorem light_row_01_011 : LightRowFacts 1 11 := by decide +kernel

private theorem light_row_01_012 : LightRowFacts 1 12 := by decide +kernel

private theorem light_row_01_013 : LightRowFacts 1 13 := by decide +kernel

private theorem light_row_01_014 : LightRowFacts 1 14 := by decide +kernel

private theorem light_row_01_015 : LightRowFacts 1 15 := by decide +kernel

private theorem light_row_02_000 : LightRowFacts 2 0 := by decide +kernel

private theorem light_row_02_001 : LightRowFacts 2 1 := by decide +kernel

private theorem light_row_02_002 : LightRowFacts 2 2 := by decide +kernel

private theorem light_row_02_003 : LightRowFacts 2 3 := by decide +kernel

private theorem light_row_02_004 : LightRowFacts 2 4 := by decide +kernel

private theorem light_row_02_005 : LightRowFacts 2 5 := by decide +kernel

private theorem light_row_02_006 : LightRowFacts 2 6 := by decide +kernel

private theorem light_row_02_007 : LightRowFacts 2 7 := by decide +kernel

private theorem light_row_02_008 : LightRowFacts 2 8 := by decide +kernel

private theorem light_row_02_009 : LightRowFacts 2 9 := by decide +kernel

private theorem light_row_02_010 : LightRowFacts 2 10 := by decide +kernel

private theorem light_row_02_011 : LightRowFacts 2 11 := by decide +kernel

private theorem light_row_02_012 : LightRowFacts 2 12 := by decide +kernel

private theorem light_row_02_013 : LightRowFacts 2 13 := by decide +kernel

private theorem light_row_02_014 : LightRowFacts 2 14 := by decide +kernel

private theorem light_row_02_015 : LightRowFacts 2 15 := by decide +kernel

private theorem light_row_03_000 : LightRowFacts 3 0 := by decide +kernel

private theorem light_row_03_001 : LightRowFacts 3 1 := by decide +kernel

private theorem light_row_03_002 : LightRowFacts 3 2 := by decide +kernel

private theorem light_row_03_003 : LightRowFacts 3 3 := by decide +kernel

private theorem light_row_03_004 : LightRowFacts 3 4 := by decide +kernel

private theorem light_row_03_005 : LightRowFacts 3 5 := by decide +kernel

private theorem light_row_03_006 : LightRowFacts 3 6 := by decide +kernel

private theorem light_row_03_007 : LightRowFacts 3 7 := by decide +kernel

private theorem light_row_03_008 : LightRowFacts 3 8 := by decide +kernel

private theorem light_row_03_009 : LightRowFacts 3 9 := by decide +kernel

private theorem light_row_03_010 : LightRowFacts 3 10 := by decide +kernel

private theorem light_row_03_011 : LightRowFacts 3 11 := by decide +kernel

private theorem light_row_03_012 : LightRowFacts 3 12 := by decide +kernel

private theorem light_row_03_013 : LightRowFacts 3 13 := by decide +kernel

private theorem light_row_03_014 : LightRowFacts 3 14 := by decide +kernel

private theorem light_row_03_015 : LightRowFacts 3 15 := by decide +kernel

private theorem light_row_04_000 : LightRowFacts 4 0 := by decide +kernel

private theorem light_row_04_001 : LightRowFacts 4 1 := by decide +kernel

private theorem light_row_04_002 : LightRowFacts 4 2 := by decide +kernel

private theorem light_row_04_003 : LightRowFacts 4 3 := by decide +kernel

private theorem light_row_04_004 : LightRowFacts 4 4 := by decide +kernel

private theorem light_row_04_005 : LightRowFacts 4 5 := by decide +kernel

private theorem light_row_04_006 : LightRowFacts 4 6 := by decide +kernel

private theorem light_row_04_007 : LightRowFacts 4 7 := by decide +kernel

private theorem light_row_05_000 : LightRowFacts 5 0 := by decide +kernel

private theorem light_row_05_001 : LightRowFacts 5 1 := by decide +kernel

private theorem light_row_05_002 : LightRowFacts 5 2 := by decide +kernel

private theorem light_row_05_003 : LightRowFacts 5 3 := by decide +kernel

private theorem light_row_05_004 : LightRowFacts 5 4 := by decide +kernel

private theorem light_row_05_005 : LightRowFacts 5 5 := by decide +kernel

private theorem light_row_05_006 : LightRowFacts 5 6 := by decide +kernel

private theorem light_row_05_007 : LightRowFacts 5 7 := by decide +kernel

private theorem light_row_06_000 : LightRowFacts 6 0 := by decide +kernel

private theorem light_row_06_001 : LightRowFacts 6 1 := by decide +kernel

private theorem light_row_06_002 : LightRowFacts 6 2 := by decide +kernel

private theorem light_row_06_003 : LightRowFacts 6 3 := by decide +kernel

private theorem light_row_06_004 : LightRowFacts 6 4 := by decide +kernel

private theorem light_row_06_005 : LightRowFacts 6 5 := by decide +kernel

private theorem light_row_06_006 : LightRowFacts 6 6 := by decide +kernel

private theorem light_row_06_007 : LightRowFacts 6 7 := by decide +kernel

private theorem light_row_07_000 : LightRowFacts 7 0 := by decide +kernel

private theorem light_row_07_001 : LightRowFacts 7 1 := by decide +kernel

private theorem light_row_07_002 : LightRowFacts 7 2 := by decide +kernel

private theorem light_row_07_003 : LightRowFacts 7 3 := by decide +kernel

private theorem light_row_07_004 : LightRowFacts 7 4 := by decide +kernel

private theorem light_row_07_005 : LightRowFacts 7 5 := by decide +kernel

private theorem light_row_07_006 : LightRowFacts 7 6 := by decide +kernel

private theorem light_row_07_007 : LightRowFacts 7 7 := by decide +kernel

private theorem light_row_08_000 : LightRowFacts 8 0 := by decide +kernel

private theorem light_row_08_001 : LightRowFacts 8 1 := by decide +kernel

private theorem light_row_08_002 : LightRowFacts 8 2 := by decide +kernel

private theorem light_row_08_003 : LightRowFacts 8 3 := by decide +kernel

private theorem light_row_08_004 : LightRowFacts 8 4 := by decide +kernel

private theorem light_row_08_005 : LightRowFacts 8 5 := by decide +kernel

private theorem light_row_08_006 : LightRowFacts 8 6 := by decide +kernel

private theorem light_row_08_007 : LightRowFacts 8 7 := by decide +kernel

private theorem light_row_09_000 : LightRowFacts 9 0 := by decide +kernel

private theorem light_row_09_001 : LightRowFacts 9 1 := by decide +kernel

private theorem light_row_09_002 : LightRowFacts 9 2 := by decide +kernel

private theorem light_row_09_003 : LightRowFacts 9 3 := by decide +kernel

private theorem light_row_09_004 : LightRowFacts 9 4 := by decide +kernel

private theorem light_row_09_005 : LightRowFacts 9 5 := by decide +kernel

private theorem light_row_09_006 : LightRowFacts 9 6 := by decide +kernel

private theorem light_row_09_007 : LightRowFacts 9 7 := by decide +kernel

private theorem light_row_10_000 : LightRowFacts 10 0 := by decide +kernel

private theorem light_row_10_001 : LightRowFacts 10 1 := by decide +kernel

private theorem light_row_10_002 : LightRowFacts 10 2 := by decide +kernel

private theorem light_row_10_003 : LightRowFacts 10 3 := by decide +kernel

private theorem light_row_10_004 : LightRowFacts 10 4 := by decide +kernel

private theorem light_row_10_005 : LightRowFacts 10 5 := by decide +kernel

private theorem light_row_10_006 : LightRowFacts 10 6 := by decide +kernel

private theorem light_row_10_007 : LightRowFacts 10 7 := by decide +kernel

theorem light_facts (w : Fin 11) : LightFacts w := by
  fin_cases w
  · exact (Fin.cases light_row_00_000 (Fin.cases light_row_00_001 (Fin.cases light_row_00_002 (Fin.cases light_row_00_003 (Fin.cases light_row_00_004 (Fin.cases light_row_00_005 (Fin.cases light_row_00_006 (Fin.cases light_row_00_007 (Fin.cases light_row_00_008 (Fin.cases light_row_00_009 (Fin.cases light_row_00_010 (Fin.cases light_row_00_011 (Fin.cases light_row_00_012 (Fin.cases light_row_00_013 (Fin.cases light_row_00_014 (Fin.cases light_row_00_015 (Fin.cases light_row_00_016 (Fin.cases light_row_00_017 (Fin.cases light_row_00_018 (Fin.cases light_row_00_019 (Fin.cases light_row_00_020 (Fin.cases light_row_00_021 (Fin.cases light_row_00_022 (Fin.cases light_row_00_023 (Fin.cases light_row_00_024 (Fin.cases light_row_00_025 (Fin.cases light_row_00_026 (Fin.cases light_row_00_027 (Fin.cases light_row_00_028 (Fin.cases light_row_00_029 (Fin.cases light_row_00_030 (Fin.cases light_row_00_031 (fun i => Fin.elim0 i)))))))))))))))))))))))))))))))))
  · exact (Fin.cases light_row_01_000 (Fin.cases light_row_01_001 (Fin.cases light_row_01_002 (Fin.cases light_row_01_003 (Fin.cases light_row_01_004 (Fin.cases light_row_01_005 (Fin.cases light_row_01_006 (Fin.cases light_row_01_007 (Fin.cases light_row_01_008 (Fin.cases light_row_01_009 (Fin.cases light_row_01_010 (Fin.cases light_row_01_011 (Fin.cases light_row_01_012 (Fin.cases light_row_01_013 (Fin.cases light_row_01_014 (Fin.cases light_row_01_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases light_row_02_000 (Fin.cases light_row_02_001 (Fin.cases light_row_02_002 (Fin.cases light_row_02_003 (Fin.cases light_row_02_004 (Fin.cases light_row_02_005 (Fin.cases light_row_02_006 (Fin.cases light_row_02_007 (Fin.cases light_row_02_008 (Fin.cases light_row_02_009 (Fin.cases light_row_02_010 (Fin.cases light_row_02_011 (Fin.cases light_row_02_012 (Fin.cases light_row_02_013 (Fin.cases light_row_02_014 (Fin.cases light_row_02_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases light_row_03_000 (Fin.cases light_row_03_001 (Fin.cases light_row_03_002 (Fin.cases light_row_03_003 (Fin.cases light_row_03_004 (Fin.cases light_row_03_005 (Fin.cases light_row_03_006 (Fin.cases light_row_03_007 (Fin.cases light_row_03_008 (Fin.cases light_row_03_009 (Fin.cases light_row_03_010 (Fin.cases light_row_03_011 (Fin.cases light_row_03_012 (Fin.cases light_row_03_013 (Fin.cases light_row_03_014 (Fin.cases light_row_03_015 (fun i => Fin.elim0 i)))))))))))))))))
  · exact (Fin.cases light_row_04_000 (Fin.cases light_row_04_001 (Fin.cases light_row_04_002 (Fin.cases light_row_04_003 (Fin.cases light_row_04_004 (Fin.cases light_row_04_005 (Fin.cases light_row_04_006 (Fin.cases light_row_04_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_05_000 (Fin.cases light_row_05_001 (Fin.cases light_row_05_002 (Fin.cases light_row_05_003 (Fin.cases light_row_05_004 (Fin.cases light_row_05_005 (Fin.cases light_row_05_006 (Fin.cases light_row_05_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_06_000 (Fin.cases light_row_06_001 (Fin.cases light_row_06_002 (Fin.cases light_row_06_003 (Fin.cases light_row_06_004 (Fin.cases light_row_06_005 (Fin.cases light_row_06_006 (Fin.cases light_row_06_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_07_000 (Fin.cases light_row_07_001 (Fin.cases light_row_07_002 (Fin.cases light_row_07_003 (Fin.cases light_row_07_004 (Fin.cases light_row_07_005 (Fin.cases light_row_07_006 (Fin.cases light_row_07_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_08_000 (Fin.cases light_row_08_001 (Fin.cases light_row_08_002 (Fin.cases light_row_08_003 (Fin.cases light_row_08_004 (Fin.cases light_row_08_005 (Fin.cases light_row_08_006 (Fin.cases light_row_08_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_09_000 (Fin.cases light_row_09_001 (Fin.cases light_row_09_002 (Fin.cases light_row_09_003 (Fin.cases light_row_09_004 (Fin.cases light_row_09_005 (Fin.cases light_row_09_006 (Fin.cases light_row_09_007 (fun i => Fin.elim0 i)))))))))
  · exact (Fin.cases light_row_10_000 (Fin.cases light_row_10_001 (Fin.cases light_row_10_002 (Fin.cases light_row_10_003 (Fin.cases light_row_10_004 (Fin.cases light_row_10_005 (Fin.cases light_row_10_006 (Fin.cases light_row_10_007 (fun i => Fin.elim0 i)))))))))

def ResidualFacts (w : Fin 11) : Prop := ∀i : Fin (count w),
  (M w,(row w i.val).e,cut w i.val,residualUnits w i.val)∈CappedValues209.data
instance (w : Fin 11) : Decidable (ResidualFacts w) := by unfold ResidualFacts;infer_instance
theorem residual_facts (w : Fin 11) : ResidualFacts w := by fin_cases w <;> decide +kernel

def LinearRat (w : Fin 11) (k : ℕ) : ℚ := ∑b : Fin 7,
  let q:=band (row w k) b
  if q.E≤1 then 0 else ((q.U+q.b2 : ℕ) : ℚ)*
    (1/((q.T-q.E : ℕ) : ℚ)+(IntegerLightLog209.LogCap w : ℕ)/(q.b2 : ℚ))
def LinearFacts (w : Fin 11) : Prop := ∀i : Fin (count w),LinearRat w i.val≤(etaLight w i.val : ℚ)
instance (w : Fin 11) : Decidable (LinearFacts w) := by unfold LinearFacts;infer_instance
theorem linear_facts (w : Fin 11) : LinearFacts w := by fin_cases w <;> decide +kernel

def WeightedMain (w : Fin 11) : ℚ :=
  (∑i∈Finset.range (count w),(phi w (i+1)-phi w i)*(alphaUnits w i : ℚ)/(Grid : ℚ))/phi w (count w)
theorem main_numeric (w : Fin 11) : WeightedMain w≤(uUnits w : ℚ)/10000 := by
  fin_cases w <;> decide +kernel
theorem u_cast (w : Fin 11) : IntegerLowPrices209.U w=(uUnits w : ℝ)/10000 := by
  fin_cases w <;> norm_num [IntegerLowPrices209.U,uUnits]

theorem main_budget (w : Fin 11) :
  (∑i∈Finset.range (count w),(psi w (i+1)-psi w i)*(alphaUnits w i : ℝ)/(Grid : ℝ))/psi w (count w)≤
    IntegerLowPrices209.U w := by
  rw [u_cast]
  have hh := (Rat.cast_le (K := ℝ)).mpr (main_numeric w)
  simpa only [WeightedMain,psi,Rat.cast_div,Rat.cast_sum,Rat.cast_mul,Rat.cast_sub,
    Rat.cast_natCast,Rat.cast_ofNat] using hh

theorem main_row (w : Fin 11) (i : Fin (count w)) :
  NearCapped209.Price (M w) (row w i.val).e (cut w i.val)+
    (∑b : Fin 7,if (band (row w i.val) b).E≤1 then 0 else
      Alpha ((band (row w i.val) b).T-(band (row w i.val) b).E : ℕ)
        (band (row w i.val) b).b2 ((band (row w i.val) b).U+(band (row w i.val) b).b2 : ℕ)
        (band (row w i.val) b).E 128)≤(alphaUnits w i.val : ℝ)/(Grid : ℝ) := by
  have hr := CappedValues209.bound (residual_facts w i)
  have hl : (∑b : Fin 7,if (band (row w i.val) b).E≤1 then 0 else
      Alpha ((band (row w i.val) b).T-(band (row w i.val) b).E : ℕ)
        (band (row w i.val) b).b2 ((band (row w i.val) b).U+(band (row w i.val) b).b2 : ℕ)
        (band (row w i.val) b).E 128)≤
      ∑b : Fin 7,(lightUnits w i.val b : ℝ)/(Grid : ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    by_cases he : (band (row w i.val) b).E≤1
    · simp only [if_pos he];positivity
    · simp only [if_neg he]
      exact LightValues209.bound ((light_facts w i b).2.1 (by omega))
  have hh := add_le_add hr hl
  simpa only [alphaUnits,Nat.cast_add,Nat.cast_sum,add_div,Finset.sum_div] using hh

theorem cut_valid (w : Fin 11) (i : Fin (count w)) :
    1≤cut w i.val ∧ cut w i.val<(row w i.val).e ∧ 3*cut w i.val<2*M w := by
  have hM := (data_range w).1
  have hf := IntegerUniformRows209.facts (W_mem w) (row_mem w i)
  have hE := hf.2.1
  have heM : (row w i.val).e<M w := by rw [←(IntegerUniformProfiles209.facts w).2.1];exact hf.2.2.1
  unfold cut
  omega

def MainLight (w : Fin 11) (k : ℕ) : ℝ := ∑b : Fin 7,
  let q:=band (row w k) b
  if q.E≤1 then 0 else Alpha (q.T-q.E : ℕ) q.b2 (q.U+q.b2 : ℕ) q.E 128
def LinearReal (w : Fin 11) (k : ℕ) : ℝ := ∑b : Fin 7,
  let q:=band (row w k) b
  if q.E≤1 then 0 else ((q.U+q.b2 : ℕ) : ℝ)*
    (1/((q.T-q.E : ℕ) : ℝ)+(IntegerLightLog209.LogCap w : ℕ)/(q.b2 : ℝ))

theorem linear_cast (w : Fin 11) (k : ℕ) : (LinearRat w k : ℝ)=LinearReal w k := by
  unfold LinearRat LinearReal
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro b hb
  dsimp only
  by_cases he : (band (row w k) b).E≤1
  · simp only [if_pos he,Rat.cast_zero]
  · simp only [if_neg he,Rat.cast_mul,Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]

theorem linear_row (w : Fin 11) (i : Fin (count w)) : LinearReal w i.val≤etaLight w i.val := by
  rw [←linear_cast]
  have hh := (Rat.cast_le (K := ℝ)).mpr (linear_facts w i)
  simpa only [Rat.cast_natCast] using hh

theorem actual_light (w : Fin 11) (i : Fin (count w)) (s : System) (v : Valid s)
    (hhi : s.N≤Upper w) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D,∀b : Fin 7,
      s.T d b=(band (row w i.val) b).T ∧ s.E d b=(band (row w i.val) b).E ∧
      s.U d b=(band (row w i.val) b).U ∧ s.B d b=CleanupEval208.block (band (row w i.val) b) d) :
    (∑d∈Finset.Icc 1 s.D,∑b : Fin 7,EffectiveLight s d b)≤
      MainLight w i.val*(s.N : ℝ)^2+(etaLight w i.val : ℝ)*s.N := by
  let T:=fun b : Fin 7=>(band (row w i.val) b).T
  let E:=fun b : Fin 7=>(band (row w i.val) b).E
  let B:=fun b : Fin 7=>(band (row w i.val) b).b2
  let V:=fun b : Fin 7=>(band (row w i.val) b).U+(band (row w i.val) b).b2
  have hf : ∀d∈Finset.Icc 1 s.D,∀b : Fin 7,
      s.T d b=T b ∧ s.E d b=E b ∧ s.B d b=B b ∧ s.U d b+s.B d b-3≤V b := by
    intro d hd b
    obtain ⟨ht,he,hu,hb⟩ := hfields d hd b
    have hbb : s.B d b=B b := by simpa only [IntegerUniformShape209.block_constant] using hb
    refine ⟨ht,he,hbb,?_⟩
    rw [hu,hbb]
    dsimp only [V,B]
    omega
  have hp := LightUnweighted209.actual_total s v T E B V (Upper w) 128
    (fun b=>(IntegerUniformShape209.physical_domain w i b).1)
    (fun b=>(IntegerUniformShape209.physical_domain w i b).2.2.2)
    (fun b=>(IntegerUniformShape209.physical_domain w i b).2.2.1)
    hhi (fun b=>(light_facts w i b).2.2) (by decide) hDN hf
  have hl : (∑b : Fin 7,if E b≤1 then 0 else (V b : ℝ)*LogFactor (T b-E b : ℕ) (B b) (Upper w))≤
      LinearReal w i.val := by
    unfold LinearReal
    apply Finset.sum_le_sum
    intro b hb
    dsimp only [T,E,B,V]
    by_cases he : (band (row w i.val) b).E≤1
    · simp only [if_pos he]
      exact le_rfl
    · simp only [if_neg he,LogFactor]
      apply mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) (V b))
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_right (IntegerLightLog209.actual_log_cap w i b) (Nat.cast_nonneg (B b)))
  have hl' := mul_le_mul_of_nonneg_right (hl.trans (linear_row w i)) (Nat.cast_nonneg (α := ℝ) s.N)
  change (∑d∈Finset.Icc 1 s.D,∑b : Fin 7,EffectiveLight s d b)≤
    MainLight w i.val*(s.N : ℝ)^2+(∑b : Fin 7,if E b≤1 then 0 else (V b : ℝ)*LogFactor (T b-E b : ℕ) (B b) (Upper w))*s.N at hp
  linarith only [hp,hl']

theorem actual_residual_light (w : Fin 11) (i : Fin (count w)) (s : System) (v : Valid s)
    (hhi : s.N≤Upper w) (hDN : s.D≤s.N)
    (hfields : ∀d∈Finset.Icc 1 s.D,∀b : Fin 7,
      s.T d b=(band (row w i.val) b).T ∧ s.E d b=(band (row w i.val) b).E ∧
      s.U d b=(band (row w i.val) b).U ∧ s.B d b=CleanupEval208.block (band (row w i.val) b) d) :
    (s.N : ℝ)^2*NearCapped209.Price (M w) (row w i.val).e (cut w i.val)+
      (∑d∈Finset.Icc 1 s.D,∑b : Fin 7,EffectiveLight s d b)≤
      (alphaUnits w i.val : ℝ)/(Grid : ℝ)*(s.N : ℝ)^2+(etaLight w i.val : ℝ)*s.N := by
  have hl := actual_light w i s v hhi hDN hfields
  have hm : NearCapped209.Price (M w) (row w i.val).e (cut w i.val)+MainLight w i.val≤
      (alphaUnits w i.val : ℝ)/(Grid : ℝ) := main_row w i
  have hmp := mul_le_mul_of_nonneg_right hm (sq_nonneg (s.N : ℝ))
  nlinarith only [hl,hmp]

#print axioms light_facts
#print axioms residual_facts
#print axioms linear_facts
#print axioms main_numeric
#print axioms main_budget
#print axioms main_row
#print axioms cut_valid
#print axioms actual_light
#print axioms actual_residual_light
end
end JSP233.IntegerUniformLight209
