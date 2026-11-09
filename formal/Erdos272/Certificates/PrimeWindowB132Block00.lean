module

public import Erdos272.Certificates.CoefficientSum132
public import Erdos272.Arithmetic.ScaleLogs132
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimeWindowB132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_000 : List Coeff := [(upperCut grid ⟨91971530415,91971544878,533899035291,533899045159,3080708568161,3080708861803,16614524457352,92289⟩ ⟨91969503663,91969518124,533888901937,533888911803,3080615370761,3080615664387,16613517811682,92279⟩ 1 0),(upperCut grid ⟨74054953064,74054959303,364508624979,364508626623,1669732895744,1669733023483,5343460835487,12440⟩ ⟨74048872189,74048878427,364459992761,364459994404,1669372750076,1669372877784,5341488380791,12432⟩ 6 (17917594687/5000000000:ℝ)),(upperCut grid ⟨68946697155,68946702736,322057318428,322057319414,1366087834428,1366087936524,3821935551744,6957⟩ ⟨68936560307,68936565887,321976264730,321976265715,1365528995951,1365529098001,3819389123680,6949⟩ 10 (5756462731/1250000000:ℝ)),(upperCut grid ⟨65581974923,65581980222,295708652954,295708653658,1188797628337,1188797715835,3059214636516,4744⟩ ⟨65567780457,65567785755,295595177777,295595178480,1188053435714,1188053523151,3056201662204,4736⟩ 14 (26390573289/5000000000:ℝ)),(upperCut grid ⟨64892046235,64892051487,290269261721,290269262378,1153306079603,1153306164185,2917165189957,4373⟩ ⟨64876837107,64876842358,290147681174,290147681830,1152517118555,1152517203072,2914046465253,4365⟩ 15 (5416100401/1000000000:ℝ)),(upperCut grid ⟨61527323960,61527329024,265233764826,265233765295,994999550921,994999622416,2325404125056,2971⟩ ⟨61506024698,61506029761,265063552061,265063552529,993952277322,993952348730,2321714000216,2963⟩ 21 (3044522437/500000000:ℝ)),(upperCut grid ⟨56419067817,56419072691,229259712485,229259712766,782656101118,782656154564,1635299555096,1640⟩ ⟨56383543801,56383548674,228976024542,228976024822,781055560188,781055613494,1630535624416,1632⟩ 35 (35553480607/5000000000:ℝ)),(upperCut grid ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ 210 (26735537647/2500000000:ℝ)),(upperCut grid ⟨61070225899,61070230942,261753720388,261753720836,973664720003,973664789719,2250786356388,2811⟩ ⟨61047929346,61047934388,261709176959,261709177406,973392692271,973392761964,2249842498030,2809⟩ 22 (1236416981/200000000:ℝ)),(upperCut grid ⟨57037821845,57037826737,233608704975,233608705274,807343864398,807343919986,1709614860925,1767⟩ ⟨57004432833,57004437724,233008704975,233008705273,803921595088,803921650381,1699222556065,1749⟩ 33 (17482537803/2500000000:ℝ)),(upperCut grid ⟨51929565673,51929570439,200025529657,200025529836,624065880903,624065920156,1193964057628,971⟩ ⟨51873855223,51873859988,199025529657,199025529835,618872924336,618872963112,1180547649754,953⟩ 55 (40073331843/5000000000:ℝ)),(upperCut grid ⟨48598121236,48598125942,179128440048,179128440176,518895522940,518895552243,934871165058,649⟩ ⟨48520299832,48520304537,178818362529,178818362656,517388604453,517388633609,931349361430,645⟩ 77 (678719597/78125000:ℝ)),(upperCut grid ⟨59401709584,59401714557,250022838945,250022839324,902980800051,902980863823,2012080664511,2325⟩ ⟨59375359108,59375364080,249707049472,249707049850,901104956591,901105020205,2005924794387,2313⟩ 26 (3258096537/500000000:ℝ)),(upperCut grid ⟨55373339790,55373344636,222142684037,222142684290,742858341234,742858391194,1518721722316,1449⟩ ⟨55333892008,55333896853,221985203723,221985203975,741986320135,741986370018,1516211899092,1445⟩ 39 (36635616451/5000000000:ℝ)),(upperCut grid ⟨50238802386,50238807121,189155560523,189155560674,568478852751,568478886812,1053741940622,790⟩ ⟨50172795546,50172800280,188629244734,188629244884,565834705257,565834739068,1047253083774,782⟩ 65 (2608992043/312500000:ℝ)),(upperCut grid ⟨46913476035,46913480703,169133049731,169133049839,471133525575,471133550169,825841400504,530⟩ ⟨46821309485,46821314151,168949563493,168949563600,470272727850,470272752357,823925747932,528⟩ 91 (45108595053/5000000000:ℝ))]

theorem uppersBlock_000_sum : sumCoeff uppersBlock_000 = ⟨(498035609990204126539/4509004500000000000:ℝ),(-14223721306015286028060761345749/22545022500000000000000000000:ℝ),(188081741926337307/25025000000000:ℝ),(-8791819394:ℝ)⟩ := by
  norm_num [uppersBlock_000,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_000_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [1,6,10,14,15,21,35,210,22,33,55,77,26,39,65,91] uppersBlock_000 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_000
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1) hN1 (by decide) state_9869 state_9867 (by decide) (by decide) (Nat.le_trans (by decide : 9867^2*1^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9869^2*1^2)) (by norm_num))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6) hN1 (by decide) state_1645 state_1644 (by decide) (by decide) (Nat.le_trans (by decide : 1644^2*6^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤1645^2*6^2)) (by simpa using scale_6.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=10) hN1 (by decide) state_987 state_986 (by decide) (by decide) (Nat.le_trans (by decide : 986^2*10^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤987^2*10^2)) (by simpa using scale_10.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=14) hN1 (by decide) state_705 state_704 (by decide) (by decide) (Nat.le_trans (by decide : 704^2*14^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤705^2*14^2)) (by simpa using scale_14.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=15) hN1 (by decide) state_658 state_657 (by decide) (by decide) (Nat.le_trans (by decide : 657^2*15^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤658^2*15^2)) (by simpa using scale_15.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=21) hN1 (by decide) state_470 state_469 (by decide) (by decide) (Nat.le_trans (by decide : 469^2*21^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤470^2*21^2)) (by simpa using scale_21.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=35) hN1 (by decide) state_282 state_281 (by decide) (by decide) (Nat.le_trans (by decide : 281^2*35^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤282^2*35^2)) (by simpa using scale_35.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=210) hN1 (by decide) state_47 state_46 (by decide) (by decide) (Nat.le_trans (by decide : 46^2*210^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤47^2*210^2)) (by simpa using scale_210.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=22) hN1 (by decide) state_449 state_448 (by decide) (by decide) (Nat.le_trans (by decide : 448^2*22^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤449^2*22^2)) (by simpa using scale_22.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=33) hN1 (by decide) state_300 state_299 (by decide) (by decide) (Nat.le_trans (by decide : 299^2*33^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤300^2*33^2)) (by simpa using scale_33.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=55) hN1 (by decide) state_180 state_179 (by decide) (by decide) (Nat.le_trans (by decide : 179^2*55^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤180^2*55^2)) (by simpa using scale_55.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=77) hN1 (by decide) state_129 state_128 (by decide) (by decide) (Nat.le_trans (by decide : 128^2*77^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤129^2*77^2)) (by simpa using scale_77.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=26) hN1 (by decide) state_380 state_379 (by decide) (by decide) (Nat.le_trans (by decide : 379^2*26^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤380^2*26^2)) (by simpa using scale_26.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=39) hN1 (by decide) state_254 state_253 (by decide) (by decide) (Nat.le_trans (by decide : 253^2*39^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤254^2*39^2)) (by simpa using scale_39.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=65) hN1 (by decide) state_152 state_151 (by decide) (by decide) (Nat.le_trans (by decide : 151^2*65^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤152^2*65^2)) (by simpa using scale_65.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=91) hN1 (by decide) state_109 state_108 (by decide) (by decide) (Nat.le_trans (by decide : 108^2*91^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤109^2*91^2)) (by simpa using scale_91.1))
  exact .nil

def uppersBlock_001 : List Coeff := [(upperCut grid ⟨56733229775,56733234658,231383571663,231383571953,794677558537,794677613029,1671293103105,1701⟩ ⟨56698806334,56698811216,231246114619,231246114908,793897720328,793897774751,1668948261577,1697⟩ 34 (17631802617/2500000000:ℝ)),(upperCut grid ⟨52678578746,52678583527,204396349867,204396350060,646943422370,646943463724,1253828183158,1053⟩ ⟨52626899045,52626903825,204190164300,204190164492,645857266108,645857307362,1250956350522,1049⟩ 51 (7863651263/1000000000:ℝ)),(upperCut grid ⟨47621736552,47621741237,173370173472,173370173588,491173788028,491173814613,870936854622,578⟩ ⟨47535899116,47535903799,172857352960,172857353075,488731647692,488731674036,865389852654,572⟩ 85 (5553314069/625000000:ℝ)),(upperCut grid ⟨44188403345,44188407916,153332427300,153332427382,399135787934,399135805192,671500527938,379⟩ ⟨44067189743,44067194308,153091463445,153091463526,398071007131,398071024278,669305242738,377⟩ 119 (47791234917/5000000000:ℝ)),(upperCut grid ⟨55606813428,55606818280,223811849172,223811849431,752124601295,752124652071,1545512227976,1492⟩ ⟨55568277735,55568282586,223350310711,223350310969,749558132983,749558183534,1538070143900,1480⟩ 38 (2273491349/312500000:ℝ)),(upperCut grid ⟨51590550158,51590554918,197552051053,197552051226,611250572724,611250610794,1160974711394,927⟩ ⟨51532913111,51532917870,197092280939,197092281111,608878593407,608878631257,1154909927042,919⟩ 57 (8086102533/1000000000:ℝ)),(upperCut grid ⟨46443906211,46443910866,166512273244,166512273347,458891271660,458891295026,798752925528,502⟩ ⟨46347287103,46347291756,165743042475,165743042577,455318663490,455318686497,790908280120,494⟩ 95 (22769384451/2500000000:ℝ)),(upperCut grid ⟨43174878437,43174882948,148148614833,148148614907,376481102162,376481117057,625402799082,338⟩ ⟨43040648239,43040652741,147348614833,147348614906,373027111888,373027126421,618474595848,332⟩ 133 (48903491267/5000000000:ℝ)),(upperCut grid ⟨53706377426,53706382230,210907955065,210907955279,681578200703,681578245200,1346879940253,1186⟩ ⟨53659757295,53659762098,210721908554,210721908767,680579012286,680579056693,1344151962893,1182⟩ 46 (38286413949/5000000000:ℝ)),(upperCut grid ⟨49698130178,49698134905,186199162876,186199163019,553688914818,553688947472,1017676155074,746⟩ ⟨49628443486,49628448211,185157496210,185157496352,548512026258,548512058419,1005176155064,731⟩ 69 (4234106503/500000000:ℝ)),(upperCut grid ⟨44543470220,44543474808,155696703242,155696703327,409627974424,409627992768,693245521454,399⟩ ⟨44426509825,44426514408,155231586963,155231587047,407556185112,407556203242,688932210522,395⟩ 115 (47449321267/5000000000:ℝ)),(upperCut grid ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ ⟨41108736068,41108740368,137163519127,137163519187,330103876624,330103886643,534673444552,263⟩ 161 (3175877727/312500000:ℝ)),(upperCut grid ⟨51416632732,51416637489,196627836794,196627836964,606487199678,606487237305,1148814398086,911⟩ ⟨51357981538,51357986294,196276959602,196276959771,604683107302,604683144761,1144226083408,905⟩ 58 (40604430087/5000000000:ℝ)),(upperCut grid ⟨47361981691,47361986370,171992285495,171992285608,484622483213,484622509150,856088973272,562⟩ ⟨47273875395,47273880072,171290531110,171290531222,481298835376,481298860983,848596286776,554⟩ 87 (2791192573/312500000:ℝ)),(upperCut grid ⟨42341062386,42341066831,143442887743,143442887811,356341168031,356341180810,585406339530,304⟩ ⟨42195074400,42195078831,142863177599,142863177666,353886613690,353886626211,580590905406,300⟩ 145 (9953467481/1000000000:ℝ)),(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ 203 (5313205977/500000000:ℝ))]

theorem uppersBlock_001_sum : sumCoeff uppersBlock_001 = ⟨(547963152448516173535309/3411489599353500000000000:ℝ),(-1976914950224802584885939667212357/1137163199784500000000000000000000:ℝ),(1908460161119452527/18851087500000000:ℝ),(-11250568:ℝ)⟩ := by
  norm_num [uppersBlock_001,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_001_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [34,51,85,119,38,57,95,133,46,69,115,161,58,87,145,203] uppersBlock_001 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_001
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=34) hN1 (by decide) state_291 state_290 (by decide) (by decide) (Nat.le_trans (by decide : 290^2*34^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤291^2*34^2)) (by simpa using scale_34.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=51) hN1 (by decide) state_194 state_193 (by decide) (by decide) (Nat.le_trans (by decide : 193^2*51^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤194^2*51^2)) (by simpa using scale_51.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=85) hN1 (by decide) state_117 state_116 (by decide) (by decide) (Nat.le_trans (by decide : 116^2*85^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤117^2*85^2)) (by simpa using scale_85.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=119) hN1 (by decide) state_83 state_82 (by decide) (by decide) (Nat.le_trans (by decide : 82^2*119^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤83^2*119^2)) (by simpa using scale_119.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=38) hN1 (by decide) state_260 state_259 (by decide) (by decide) (Nat.le_trans (by decide : 259^2*38^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤260^2*38^2)) (by simpa using scale_38.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=57) hN1 (by decide) state_174 state_173 (by decide) (by decide) (Nat.le_trans (by decide : 173^2*57^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤174^2*57^2)) (by simpa using scale_57.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=95) hN1 (by decide) state_104 state_103 (by decide) (by decide) (Nat.le_trans (by decide : 103^2*95^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤104^2*95^2)) (by simpa using scale_95.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=133) hN1 (by decide) state_75 state_74 (by decide) (by decide) (Nat.le_trans (by decide : 74^2*133^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤75^2*133^2)) (by simpa using scale_133.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=46) hN1 (by decide) state_215 state_214 (by decide) (by decide) (Nat.le_trans (by decide : 214^2*46^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤215^2*46^2)) (by simpa using scale_46.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=69) hN1 (by decide) state_144 state_143 (by decide) (by decide) (Nat.le_trans (by decide : 143^2*69^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤144^2*69^2)) (by simpa using scale_69.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=115) hN1 (by decide) state_86 state_85 (by decide) (by decide) (Nat.le_trans (by decide : 85^2*115^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤86^2*115^2)) (by simpa using scale_115.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=161) hN1 (by decide) state_62 state_61 (by decide) (by decide) (Nat.le_trans (by decide : 61^2*161^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤62^2*161^2)) (by simpa using scale_161.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=58) hN1 (by decide) state_171 state_170 (by decide) (by decide) (Nat.le_trans (by decide : 170^2*58^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤171^2*58^2)) (by simpa using scale_58.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=87) hN1 (by decide) state_114 state_113 (by decide) (by decide) (Nat.le_trans (by decide : 113^2*87^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤114^2*87^2)) (by simpa using scale_87.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=145) hN1 (by decide) state_69 state_68 (by decide) (by decide) (Nat.le_trans (by decide : 68^2*145^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤69^2*145^2)) (by simpa using scale_145.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=203) hN1 (by decide) state_49 state_48 (by decide) (by decide) (Nat.le_trans (by decide : 48^2*203^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤49^2*203^2)) (by simpa using scale_203.1))
  exact .nil

def uppersBlock_002 : List Coeff := [(upperCut grid ⟨50751735325,50751740071,192476618607,192476618766,585261558761,585261594405,1095297245648,842⟩ ⟨50689039195,50689043940,191726618607,191726618765,581455178612,581455213899,1085810412656,830⟩ 62 (41271343831/5000000000:ℝ)),(upperCut grid ⟨46728285560,46728290223,167838452382,167838452488,465070360130,465070384117,812378742544,516⟩ ⟨46634388158,46634392818,167651536495,167651536600,464196934232,464196958131,810445269564,514⟩ 93 (1416437341/156250000:ℝ)),(upperCut grid ⟨41588828222,41588832586,139854811369,139854811432,341261164236,341261175429,556062739098,280⟩ ⟨41431344664,41431349008,138761061369,138761061431,336712386150,336712396864,547312739098,273⟩ 155 (50434251149/5000000000:ℝ)),(upperCut grid ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 217 (26899486757/2500000000:ℝ)),(upperCut grid ⟨48978395189,48978399902,181404846668,181404846801,530006967311,530006997691,961003610276,679⟩ ⟨48903488472,48903493184,181106339206,181106339338,528544925664,528544955902,957548136572,675⟩ 74 (8608129941/1000000000:ℝ)),(upperCut grid ⟨44886360946,44886365548,157290283366,157290283454,416760253599,416760272678,708181996012,413⟩ ⟨44773365396,44773369994,157065564265,157065564352,415751571331,415751590306,706062000250,411⟩ 111 (23547650393/2500000000:ℝ)),(upperCut grid ⟨39889838028,39889842101,130949413513,130949413566,304882684455,304882691851,487382560016,227⟩ ⟨39702916725,39702920753,129467932032,129467932084,298973078822,298973085613,476495938936,219⟩ 185 (52203557023/5000000000:ℝ)),(upperCut grid ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ 259 (13892069847/1250000000:ℝ)),(upperCut grid ⟨47957902656,47957907349,175626558192,175626558312,501969757989,501969785638,895619154696,605⟩ ⟨47874914629,47874919320,175378624308,175378624427,500780719081,500780746612,892891881966,602⟩ 82 (1762687629/200000000:ℝ)),(upperCut grid ⟨43944488821,43944493379,152603658567,152603658647,395921388120,395921405043,664887981694,373⟩ ⟨43820263625,43820268176,151986374617,151986374696,393208765354,393208781994,659332426134,368⟩ 123 (24060920903/2500000000:ℝ)),(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ 205 (53230098043/5000000000:ℝ)),(upperCut grid ⟨35553479773,35553481184,109288272403,109288272437,222931141910,222931142438,343468973600,131⟩ ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ 287 (7074352551/625000000:ℝ)),(upperCut grid ⟨47449318490,47449323171,172340111581,172340111695,486272894290,486272920391,859818992508,566⟩ ⟨47361981691,47361986370,171992285495,171992285608,484622483213,484622509150,856088973272,562⟩ 86 (11135867759/1250000000:ℝ)),(upperCut grid ⟨43438051510,43438056038,149457569036,149457569112,382156624110,382156639598,636843694162,348⟩ ⟨43307330699,43307335219,148938088517,148938088592,379900101954,379900117206,632285271102,344⟩ 129 (48598122117/5000000000:ℝ)),(upperCut grid ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 215 (26853189177/2500000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 301 (57071100719/5000000000:ℝ))]

theorem uppersBlock_002_sum : sumCoeff uppersBlock_002 = ⟨(18572564567900652510780961/450827145868790250000000000:ℝ),(-7526592479010444658643839191275323/15708262922257500000000000000000000:ℝ),(19782915818090811503/530817262500000000:ℝ),(-2789198:ℝ)⟩ := by
  norm_num [uppersBlock_002,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_002_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [62,93,155,217,74,111,185,259,82,123,205,287,86,129,215,301] uppersBlock_002 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_002
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=62) hN1 (by decide) state_160 state_159 (by decide) (by decide) (Nat.le_trans (by decide : 159^2*62^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤160^2*62^2)) (by simpa using scale_62.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=93) hN1 (by decide) state_107 state_106 (by decide) (by decide) (Nat.le_trans (by decide : 106^2*93^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤107^2*93^2)) (by simpa using scale_93.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=155) hN1 (by decide) state_64 state_63 (by decide) (by decide) (Nat.le_trans (by decide : 63^2*155^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤64^2*155^2)) (by simpa using scale_155.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=217) hN1 (by decide) state_46 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*217^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤46^2*217^2)) (by simpa using scale_217.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=74) hN1 (by decide) state_134 state_133 (by decide) (by decide) (Nat.le_trans (by decide : 133^2*74^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤134^2*74^2)) (by simpa using scale_74.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=111) hN1 (by decide) state_89 state_88 (by decide) (by decide) (Nat.le_trans (by decide : 88^2*111^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤89^2*111^2)) (by simpa using scale_111.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=185) hN1 (by decide) state_54 state_53 (by decide) (by decide) (Nat.le_trans (by decide : 53^2*185^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤54^2*185^2)) (by simpa using scale_185.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=259) hN1 (by decide) state_39 state_38 (by decide) (by decide) (Nat.le_trans (by decide : 38^2*259^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤39^2*259^2)) (by simpa using scale_259.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=82) hN1 (by decide) state_121 state_120 (by decide) (by decide) (Nat.le_trans (by decide : 120^2*82^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤121^2*82^2)) (by simpa using scale_82.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=123) hN1 (by decide) state_81 state_80 (by decide) (by decide) (Nat.le_trans (by decide : 80^2*123^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤81^2*123^2)) (by simpa using scale_123.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=205) hN1 (by decide) state_49 state_48 (by decide) (by decide) (Nat.le_trans (by decide : 48^2*205^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤49^2*205^2)) (by simpa using scale_205.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=287) hN1 (by decide) state_35 state_34 (by decide) (by decide) (Nat.le_trans (by decide : 34^2*287^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤35^2*287^2)) (by simpa using scale_287.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=86) hN1 (by decide) state_115 state_114 (by decide) (by decide) (Nat.le_trans (by decide : 114^2*86^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤115^2*86^2)) (by simpa using scale_86.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=129) hN1 (by decide) state_77 state_76 (by decide) (by decide) (Nat.le_trans (by decide : 76^2*129^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤77^2*129^2)) (by simpa using scale_129.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=215) hN1 (by decide) state_46 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*215^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤46^2*215^2)) (by simpa using scale_215.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=301) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*301^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤33^2*301^2)) (by simpa using scale_301.1))
  exact .nil

def uppersBlock_003 : List Coeff := [(upperCut grid ⟨46539600720,46539605377,167274178005,167274178109,462437146000,462437169722,806560126112,510⟩ ⟨46443906211,46443910866,166512273244,166512273347,458891271660,458891295026,798752925528,502⟩ 94 (1135823641/125000000:ℝ)),(upperCut grid ⟨42484949753,42484954211,144585744885,144585744954,361196590859,361196604149,594968168410,312⟩ ⟨42341062386,42341066831,143442887743,143442887811,356341168031,356341180810,585406339530,304⟩ 141 (49487596721/5000000000:ℝ)),(upperCut grid ⟨37376694343,37376697419,118799652328,118799652369,257736950748,257736953609,402767790241,168⟩ ⟨37135718922,37135721840,116894890424,116894890464,250617580397,250617582672,390423522241,160⟩ 235 (27297926479/2500000000:ℝ)),(upperCut grid ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ 329 (57960575323/5000000000:ℝ)),(upperCut grid ⟨45432945059,45432949683,160570990491,160570990584,431574608944,431574629542,739553170202,443⟩ ⟨45325992170,45325996790,160145458577,160145458669,429641292133,429641312534,735427485214,439⟩ 106 (2914649283/312500000:ℝ)),(upperCut grid ⟨41431344664,41431349008,138761061369,138761061431,336712386150,336712396864,547312739098,273⟩ ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ 159 (50689039609/5000000000:ℝ)),(upperCut grid ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ ⟨36109177902,36109179951,112328812943,112328812979,233841786448,233841787526,361756953351,142⟩ 265 (27898647923/2500000000:ℝ)),(upperCut grid ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ 371 (59162018211/5000000000:ℝ)),(upperCut grid ⟨44308165252,44308169829,154760998728,154760998811,405465525827,405465543740,684593601362,391⟩ ⟨44188403345,44188407916,153332427300,153332427382,399135787934,399135805192,671500527938,379⟩ 118 (47706843699/5000000000:ℝ)),(upperCut grid ⟨40253514422,40253518574,133105257668,133105257723,313547610470,313547618760,503466608596,239⟩ ⟨40073329390,40073333504,131676686240,131676686294,307797108410,307797116106,492776158916,231⟩ 177 (2588074739/250000000:ℝ)),(upperCut grid ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ 295 (56869751017/5000000000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 413 (30117236691/2500000000:ℝ)),(upperCut grid ⟨43944488821,43944493379,152603658567,152603658647,395921388120,395921405043,664887981694,373⟩ ⟨43820263625,43820268176,151986374617,151986374696,393208765354,393208781994,659332426134,368⟩ 122 (48040207871/5000000000:ℝ)),(upperCut grid ⟨39889838028,39889842101,130949413513,130949413566,304882684455,304882691851,487382560016,227⟩ ⟨39702916725,39702920753,129467932032,129467932084,298973078822,298973085613,476495938936,219⟩ 183 (6511857369/625000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 305 (57203115189/5000000000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 427 (30283918777/2500000000:ℝ))]

theorem uppersBlock_003_sum : sumCoeff uppersBlock_003 = ⟨(299126738601362504473418363/17722286053704760500000000000:ℝ),(-18168511882762547466049116814345039321/88611430268523802500000000000000000000:ℝ),(6484684404189925751/336191587500000000:ℝ),(-1094313:ℝ)⟩ := by
  norm_num [uppersBlock_003,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_003_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [94,141,235,329,106,159,265,371,118,177,295,413,122,183,305,427] uppersBlock_003 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_003
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=94) hN1 (by decide) state_105 state_104 (by decide) (by decide) (Nat.le_trans (by decide : 104^2*94^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤105^2*94^2)) (by simpa using scale_94.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=141) hN1 (by decide) state_70 state_69 (by decide) (by decide) (Nat.le_trans (by decide : 69^2*141^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤70^2*141^2)) (by simpa using scale_141.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=235) hN1 (by decide) state_42 state_41 (by decide) (by decide) (Nat.le_trans (by decide : 41^2*235^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤42^2*235^2)) (by simpa using scale_235.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=329) hN1 (by decide) state_30 state_29 (by decide) (by decide) (Nat.le_trans (by decide : 29^2*329^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤30^2*329^2)) (by simpa using scale_329.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=106) hN1 (by decide) state_94 state_93 (by decide) (by decide) (Nat.le_trans (by decide : 93^2*106^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤94^2*106^2)) (by simpa using scale_106.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=159) hN1 (by decide) state_63 state_62 (by decide) (by decide) (Nat.le_trans (by decide : 62^2*159^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤63^2*159^2)) (by simpa using scale_159.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=265) hN1 (by decide) state_38 state_37 (by decide) (by decide) (Nat.le_trans (by decide : 37^2*265^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤38^2*265^2)) (by simpa using scale_265.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=371) hN1 (by decide) state_27 state_26 (by decide) (by decide) (Nat.le_trans (by decide : 26^2*371^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤27^2*371^2)) (by simpa using scale_371.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=118) hN1 (by decide) state_84 state_83 (by decide) (by decide) (Nat.le_trans (by decide : 83^2*118^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤84^2*118^2)) (by simpa using scale_118.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=177) hN1 (by decide) state_56 state_55 (by decide) (by decide) (Nat.le_trans (by decide : 55^2*177^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤56^2*177^2)) (by simpa using scale_177.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=295) hN1 (by decide) state_34 state_33 (by decide) (by decide) (Nat.le_trans (by decide : 33^2*295^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤34^2*295^2)) (by simpa using scale_295.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=413) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*413^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤24^2*413^2)) (by simpa using scale_413.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=122) hN1 (by decide) state_81 state_80 (by decide) (by decide) (Nat.le_trans (by decide : 80^2*122^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤81^2*122^2)) (by simpa using scale_122.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=183) hN1 (by decide) state_54 state_53 (by decide) (by decide) (Nat.le_trans (by decide : 53^2*183^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤54^2*183^2)) (by simpa using scale_183.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=305) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*305^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤33^2*305^2)) (by simpa using scale_305.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=427) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*427^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤24^2*427^2)) (by simpa using scale_427.1))
  exact .nil

end
end JSP233.PrimeWindowB132.Blocks
