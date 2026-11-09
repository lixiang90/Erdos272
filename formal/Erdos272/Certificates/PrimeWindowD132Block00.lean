module

public import Erdos272.Certificates.CoefficientSum132
public import Erdos272.Arithmetic.ScaleLogs132
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimeWindowD132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_000 : List Coeff := [(upperCut grid ⟨91993797619,91993812104,534143963192,534143973082,3082961491779,3082961785797,16638870411472,92531⟩ ⟨91979633318,91979647789,533982092347,533982102223,3081472488030,3081472781801,16622777141020,92371⟩ 1 0),(upperCut grid ⟨74079239655,74079245898,364666436214,364666437862,1670901809379,1670901937220,5349866373603,12466⟩ ⟨74061030244,74061036484,364532926315,364532927960,1669912873946,1669913001701,5344446763207,12444⟩ 6 (17917594687/5000000000:ℝ)),(upperCut grid ⟨68977046191,68977051775,322461645052,322461646041,1368876473572,1368876575897,3834652887068,6997⟩ ⟨68946697155,68946702736,322057318428,322057319414,1366087834428,1366087936524,3821935551744,6957⟩ 10 (5756462731/1250000000:ℝ)),(upperCut grid ⟨65610303553,65610308854,295821887263,295821887969,1189540481887,1189540569447,3062224411208,4752⟩ ⟨65581974923,65581980222,295708652954,295708653658,1188797628337,1188797715835,3059214636516,4744⟩ 14 (26390573289/5000000000:ℝ)),(upperCut grid ⟨64922395271,64922400525,290663247097,290663247756,1155863881023,1155863965814,2927286266697,4399⟩ ⟨64892046235,64892051487,290269261721,290269262378,1153306079603,1153306164185,2917165189957,4373⟩ 15 (5416100401/1000000000:ℝ)),(upperCut grid ⟨61548577953,61548583018,265318690516,265318690986,995522256466,995522328005,2327247227768,2975⟩ ⟨61527323960,61527329024,265233764826,265233765295,994999550921,994999622416,2325404125056,2971⟩ 21 (3044522437/500000000:ℝ)),(upperCut grid ⟨56454466084,56454470959,229330383863,229330384145,783055072609,783055126091,1636488431694,1642⟩ ⟨56419067817,56419072691,229259712485,229259712766,782656101118,782656154564,1635299555096,1640⟩ 35 (35553480607/5000000000:ℝ)),(upperCut grid ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ 210 (26735537647/2500000000:ℝ)),(upperCut grid ⟨61092472849,61092477893,262153720388,262153720837,976108418916,976108488835,2259271637766,2829⟩ ⟨61047929346,61047934388,261709176959,261709177406,973392692271,973392761964,2249842498030,2809⟩ 22 (1236416981/200000000:ℝ)),(upperCut grid ⟨57037821845,57037826737,233608704975,233608705274,807343864398,807343919986,1709614860925,1767⟩ ⟨57004432833,57004437724,233008704975,233008705273,803921595088,803921650381,1699222556065,1749⟩ 33 (17482537803/2500000000:ℝ)),(upperCut grid ⟨51929565673,51929570439,200025529657,200025529836,624065880903,624065920156,1193964057628,971⟩ ⟨51873855223,51873859988,199025529657,199025529835,618872924336,618872963112,1180547649754,953⟩ 55 (40073331843/5000000000:ℝ)),(upperCut grid ⟨48598121236,48598125942,179128440048,179128440176,518895522940,518895552243,934871165058,649⟩ ⟨48520299832,48520304537,178818362529,178818362656,517388604453,517388633609,931349361430,645⟩ 77 (678719597/78125000:ℝ)),(upperCut grid ⟨59427990808,59427995782,250127825821,250127826201,903604715964,903604779790,2014129926591,2329⟩ ⟨59375359108,59375364080,249707049472,249707049850,901104956591,901105020205,2005924794387,2313⟩ 26 (3258096537/500000000:ℝ)),(upperCut grid ⟨55373339790,55373344636,222142684037,222142684290,742858341234,742858391194,1518721722316,1449⟩ ⟨55333892008,55333896853,221985203723,221985203975,741986320135,741986370018,1516211899092,1445⟩ 39 (36635616451/5000000000:ℝ)),(upperCut grid ⟨50304376391,50304381127,189547717385,189547717537,570451573393,570451607641,1058592653126,796⟩ ⟨50172795546,50172800280,188629244734,188629244884,565834705257,565834739068,1047253083774,782⟩ 65 (2608992043/312500000:ℝ)),(upperCut grid ⟨46913476035,46913480703,169133049731,169133049839,471133525575,471133550169,825841400504,530⟩ ⟨46821309485,46821314151,168949563493,168949563600,470272727850,470272752357,823925747932,528⟩ 91 (45108595053/5000000000:ℝ))]

theorem uppersBlock_000_sum : sumCoeff uppersBlock_000 = ⟨(5662129807251303301/51238687500000000:ℝ),(-431343269978027683017946054973/683182500000000000000000000:ℝ),(113019042615200749/15015000000000:ℝ),(-8809437094:ℝ)⟩ := by
  norm_num [uppersBlock_000,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_000_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [1,6,10,14,15,21,35,210,22,33,55,77,26,39,65,91] uppersBlock_000 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_000
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1) hN1 (by decide) state_9891 state_9877 (by decide) (by decide) (Nat.le_trans (by decide : 9877^2*1^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤9891^2*1^2)) (by norm_num))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6) hN1 (by decide) state_1649 state_1646 (by decide) (by decide) (Nat.le_trans (by decide : 1646^2*6^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤1649^2*6^2)) (by simpa using scale_6.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=10) hN1 (by decide) state_990 state_987 (by decide) (by decide) (Nat.le_trans (by decide : 987^2*10^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤990^2*10^2)) (by simpa using scale_10.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=14) hN1 (by decide) state_707 state_705 (by decide) (by decide) (Nat.le_trans (by decide : 705^2*14^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤707^2*14^2)) (by simpa using scale_14.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=15) hN1 (by decide) state_660 state_658 (by decide) (by decide) (Nat.le_trans (by decide : 658^2*15^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤660^2*15^2)) (by simpa using scale_15.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=21) hN1 (by decide) state_471 state_470 (by decide) (by decide) (Nat.le_trans (by decide : 470^2*21^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤471^2*21^2)) (by simpa using scale_21.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=35) hN1 (by decide) state_283 state_282 (by decide) (by decide) (Nat.le_trans (by decide : 282^2*35^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤283^2*35^2)) (by simpa using scale_35.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=210) hN1 (by decide) state_48 state_47 (by decide) (by decide) (Nat.le_trans (by decide : 47^2*210^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤48^2*210^2)) (by simpa using scale_210.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=22) hN1 (by decide) state_450 state_448 (by decide) (by decide) (Nat.le_trans (by decide : 448^2*22^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤450^2*22^2)) (by simpa using scale_22.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=33) hN1 (by decide) state_300 state_299 (by decide) (by decide) (Nat.le_trans (by decide : 299^2*33^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤300^2*33^2)) (by simpa using scale_33.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=55) hN1 (by decide) state_180 state_179 (by decide) (by decide) (Nat.le_trans (by decide : 179^2*55^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤180^2*55^2)) (by simpa using scale_55.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=77) hN1 (by decide) state_129 state_128 (by decide) (by decide) (Nat.le_trans (by decide : 128^2*77^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤129^2*77^2)) (by simpa using scale_77.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=26) hN1 (by decide) state_381 state_379 (by decide) (by decide) (Nat.le_trans (by decide : 379^2*26^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤381^2*26^2)) (by simpa using scale_26.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=39) hN1 (by decide) state_254 state_253 (by decide) (by decide) (Nat.le_trans (by decide : 253^2*39^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤254^2*39^2)) (by simpa using scale_39.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=65) hN1 (by decide) state_153 state_151 (by decide) (by decide) (Nat.le_trans (by decide : 151^2*65^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤153^2*65^2)) (by simpa using scale_65.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=91) hN1 (by decide) state_109 state_108 (by decide) (by decide) (Nat.le_trans (by decide : 108^2*91^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤109^2*91^2)) (by simpa using scale_91.1))
  exact .nil

def uppersBlock_001 : List Coeff := [(upperCut grid ⟨56733229775,56733234658,231383571663,231383571953,794677558537,794677613029,1671293103105,1701⟩ ⟨56698806334,56698811216,231246114619,231246114908,793897720328,793897774751,1668948261577,1697⟩ 34 (17631802617/2500000000:ℝ)),(upperCut grid ⟨52678578746,52678583527,204396349867,204396350060,646943422370,646943463724,1253828183158,1053⟩ ⟨52626899045,52626903825,204190164300,204190164492,645857266108,645857307362,1250956350522,1049⟩ 51 (7863651263/1000000000:ℝ)),(upperCut grid ⟨47621736552,47621741237,173370173472,173370173588,491173788028,491173814613,870936854622,578⟩ ⟨47535899116,47535903799,172857352960,172857353075,488731647692,488731674036,865389852654,572⟩ 85 (5553314069/625000000:ℝ)),(upperCut grid ⟨44308165252,44308169829,154760998728,154760998811,405465525827,405465543740,684593601362,391⟩ ⟨44188403345,44188407916,153332427300,153332427382,399135787934,399135805192,671500527938,379⟩ 119 (47791234917/5000000000:ℝ)),(upperCut grid ⟨55645201191,55645206044,224041734229,224041734489,753403801322,753403852210,1549226134742,1498⟩ ⟨55568277735,55568282586,223350310711,223350310969,749558132983,749558183534,1538070143900,1480⟩ 38 (2273491349/312500000:ℝ)),(upperCut grid ⟨51590550158,51590554918,197552051053,197552051226,611250572724,611250610794,1160974711394,927⟩ ⟨51532913111,51532917870,197092280939,197092281111,608878593407,608878631257,1154909927042,919⟩ 57 (8086102533/1000000000:ℝ)),(upperCut grid ⟨46539600720,46539605377,167274178005,167274178109,462437146000,462437169722,806560126112,510⟩ ⟨46347287103,46347291756,165743042475,165743042577,455318663490,455318686497,790908280120,494⟩ 95 (22769384451/2500000000:ℝ)),(upperCut grid ⟨43174878437,43174882948,148148614833,148148614907,376481102162,376481117057,625402799082,338⟩ ⟨43040648239,43040652741,147348614833,147348614906,373027111888,373027126421,618474595848,332⟩ 133 (48903491267/5000000000:ℝ)),(upperCut grid ⟨53752781221,53752786026,211648695805,211648696020,685559888200,685559933054,1357766561341,1202⟩ ⟨53659757295,53659762098,210721908554,210721908767,680579012286,680579056693,1344151962893,1182⟩ 46 (38286413949/5000000000:ℝ)),(upperCut grid ⟨49698130178,49698134905,186199162876,186199163019,553688914818,553688947472,1017676155074,746⟩ ⟨49628443486,49628448211,185157496210,185157496352,548512026258,548512058419,1005176155064,731⟩ 69 (4234106503/500000000:ℝ)),(upperCut grid ⟨44659078441,44659083034,156156473356,156156473442,411681265386,411681283942,697533971594,403⟩ ⟨44426509825,44426514408,155231586963,155231587047,407556185112,407556203242,688932210522,395⟩ 115 (47449321267/5000000000:ℝ)),(upperCut grid ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ ⟨41108736068,41108740368,137163519127,137163519187,330103876624,330103886643,534673444552,263⟩ 161 (3175877727/312500000:ℝ)),(upperCut grid ⟨51416632732,51416637489,196627836794,196627836964,606487199678,606487237305,1148814398086,911⟩ ⟨51357981538,51357986294,196276959602,196276959771,604683107302,604683144761,1144226083408,905⟩ 58 (40604430087/5000000000:ℝ)),(upperCut grid ⟨47361981691,47361986370,171992285495,171992285608,484622483213,484622509150,856088973272,562⟩ ⟨47273875395,47273880072,171290531110,171290531222,481298835376,481298860983,848596286776,554⟩ 87 (2791192573/312500000:ℝ)),(upperCut grid ⟨42341062386,42341066831,143442887743,143442887811,356341168031,356341180810,585406339530,304⟩ ⟨42195074400,42195078831,142863177599,142863177666,353886613690,353886626211,580590905406,300⟩ 145 (9953467481/1000000000:ℝ)),(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ 203 (5313205977/500000000:ℝ))]

theorem uppersBlock_001_sum : sumCoeff uppersBlock_001 = ⟨(7835153937809634963787/48735565705050000000000:ℝ),(-9895435519256052207198730721056509/5685815998922500000000000000000000:ℝ),(56256241058405581/554443750000000:ℝ),(-11252080:ℝ)⟩ := by
  norm_num [uppersBlock_001,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_001_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [34,51,85,119,38,57,95,133,46,69,115,161,58,87,145,203] uppersBlock_001 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_001
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=34) hN1 (by decide) state_291 state_290 (by decide) (by decide) (Nat.le_trans (by decide : 290^2*34^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤291^2*34^2)) (by simpa using scale_34.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=51) hN1 (by decide) state_194 state_193 (by decide) (by decide) (Nat.le_trans (by decide : 193^2*51^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤194^2*51^2)) (by simpa using scale_51.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=85) hN1 (by decide) state_117 state_116 (by decide) (by decide) (Nat.le_trans (by decide : 116^2*85^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤117^2*85^2)) (by simpa using scale_85.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=119) hN1 (by decide) state_84 state_83 (by decide) (by decide) (Nat.le_trans (by decide : 83^2*119^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤84^2*119^2)) (by simpa using scale_119.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=38) hN1 (by decide) state_261 state_259 (by decide) (by decide) (Nat.le_trans (by decide : 259^2*38^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤261^2*38^2)) (by simpa using scale_38.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=57) hN1 (by decide) state_174 state_173 (by decide) (by decide) (Nat.le_trans (by decide : 173^2*57^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤174^2*57^2)) (by simpa using scale_57.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=95) hN1 (by decide) state_105 state_103 (by decide) (by decide) (Nat.le_trans (by decide : 103^2*95^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤105^2*95^2)) (by simpa using scale_95.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=133) hN1 (by decide) state_75 state_74 (by decide) (by decide) (Nat.le_trans (by decide : 74^2*133^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤75^2*133^2)) (by simpa using scale_133.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=46) hN1 (by decide) state_216 state_214 (by decide) (by decide) (Nat.le_trans (by decide : 214^2*46^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤216^2*46^2)) (by simpa using scale_46.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=69) hN1 (by decide) state_144 state_143 (by decide) (by decide) (Nat.le_trans (by decide : 143^2*69^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤144^2*69^2)) (by simpa using scale_69.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=115) hN1 (by decide) state_87 state_85 (by decide) (by decide) (Nat.le_trans (by decide : 85^2*115^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤87^2*115^2)) (by simpa using scale_115.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=161) hN1 (by decide) state_62 state_61 (by decide) (by decide) (Nat.le_trans (by decide : 61^2*161^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤62^2*161^2)) (by simpa using scale_161.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=58) hN1 (by decide) state_171 state_170 (by decide) (by decide) (Nat.le_trans (by decide : 170^2*58^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤171^2*58^2)) (by simpa using scale_58.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=87) hN1 (by decide) state_114 state_113 (by decide) (by decide) (Nat.le_trans (by decide : 113^2*87^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤114^2*87^2)) (by simpa using scale_87.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=145) hN1 (by decide) state_69 state_68 (by decide) (by decide) (Nat.le_trans (by decide : 68^2*145^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤69^2*145^2)) (by simpa using scale_145.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=203) hN1 (by decide) state_49 state_48 (by decide) (by decide) (Nat.le_trans (by decide : 48^2*203^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤49^2*203^2)) (by simpa using scale_203.1))
  exact .nil

def uppersBlock_002 : List Coeff := [(upperCut grid ⟨50751735325,50751740071,192476618607,192476618766,585261558761,585261594405,1095297245648,842⟩ ⟨50689039195,50689043940,191726618607,191726618765,581455178612,581455213899,1085810412656,830⟩ 62 (41271343831/5000000000:ℝ)),(upperCut grid ⟨46728285560,46728290223,167838452382,167838452488,465070360130,465070384117,812378742544,516⟩ ⟨46634388158,46634392818,167651536495,167651536600,464196934232,464196958131,810445269564,514⟩ 93 (1416437341/156250000:ℝ)),(upperCut grid ⟨41588828222,41588832586,139854811369,139854811432,341261164236,341261175429,556062739098,280⟩ ⟨41431344664,41431349008,138761061369,138761061431,336712386150,336712396864,547312739098,273⟩ 155 (50434251149/5000000000:ℝ)),(upperCut grid ⟨38286411839,38286415391,122831303520,122831303565,273051407293,273051411532,429705052145,186⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 217 (26899486757/2500000000:ℝ)),(upperCut grid ⟨48978395189,48978399902,181404846668,181404846801,530006967311,530006997691,961003610276,679⟩ ⟨48903488472,48903493184,181106339206,181106339338,528544925664,528544955902,957548136572,675⟩ 74 (8608129941/1000000000:ℝ)),(upperCut grid ⟨44998093949,44998098556,158623616699,158623616788,422759999458,422760019153,720831106660,425⟩ ⟨44773365396,44773369994,157065564265,157065564352,415751571331,415751590306,706062000250,411⟩ 111 (23547650393/2500000000:ℝ)),(upperCut grid ⟨39889838028,39889842101,130949413513,130949413566,304882684455,304882691851,487382560016,227⟩ ⟨39702916725,39702920753,129467932032,129467932084,298973078822,298973085613,476495938936,219⟩ 185 (52203557023/5000000000:ℝ)),(upperCut grid ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ 259 (13892069847/1250000000:ℝ)),(upperCut grid ⟨47957902656,47957907349,175626558192,175626558312,501969757989,501969785638,895619154696,605⟩ ⟨47874914629,47874919320,175378624308,175378624427,500780719081,500780746612,892891881966,602⟩ 82 (1762687629/200000000:ℝ)),(upperCut grid ⟨43944488821,43944493379,152603658567,152603658647,395921388120,395921405043,664887981694,373⟩ ⟨43820263625,43820268176,151986374617,151986374696,393208765354,393208781994,659332426134,368⟩ 123 (24060920903/2500000000:ℝ)),(upperCut grid ⟨38918200708,38918204505,125952413664,125952413712,285137516504,285137521909,451341822992,201⟩ ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ 205 (53230098043/5000000000:ℝ)),(upperCut grid ⟨35553479773,35553481184,109288272403,109288272437,222931141910,222931142438,343468973600,131⟩ ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ 287 (7074352551/625000000:ℝ)),(upperCut grid ⟨47535899116,47535903799,172857352960,172857353075,488731647692,488731674036,865389852654,572⟩ ⟨47361981691,47361986370,171992285495,171992285608,484622483213,484622509150,856088973272,562⟩ 86 (11135867759/1250000000:ℝ)),(upperCut grid ⟨43438051510,43438056038,149457569036,149457569112,382156624110,382156639598,636843694162,348⟩ ⟨43307330699,43307335219,148938088517,148938088592,379900101954,379900117206,632285271102,344⟩ 129 (48598122117/5000000000:ℝ)),(upperCut grid ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ 215 (26853189177/2500000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 301 (57071100719/5000000000:ℝ))]

theorem uppersBlock_002_sum : sumCoeff uppersBlock_002 = ⟨(18589457717209827156583781/450827145868790250000000000:ℝ),(-7534656537865347492887530003603951/15708262922257500000000000000000000:ℝ),(4955936688946279277/132704315625000000:ℝ),(-2789198:ℝ)⟩ := by
  norm_num [uppersBlock_002,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_002_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [62,93,155,217,74,111,185,259,82,123,205,287,86,129,215,301] uppersBlock_002 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_002
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=62) hN1 (by decide) state_160 state_159 (by decide) (by decide) (Nat.le_trans (by decide : 159^2*62^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤160^2*62^2)) (by simpa using scale_62.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=93) hN1 (by decide) state_107 state_106 (by decide) (by decide) (Nat.le_trans (by decide : 106^2*93^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤107^2*93^2)) (by simpa using scale_93.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=155) hN1 (by decide) state_64 state_63 (by decide) (by decide) (Nat.le_trans (by decide : 63^2*155^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤64^2*155^2)) (by simpa using scale_155.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=217) hN1 (by decide) state_46 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*217^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤46^2*217^2)) (by simpa using scale_217.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=74) hN1 (by decide) state_134 state_133 (by decide) (by decide) (Nat.le_trans (by decide : 133^2*74^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤134^2*74^2)) (by simpa using scale_74.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=111) hN1 (by decide) state_90 state_88 (by decide) (by decide) (Nat.le_trans (by decide : 88^2*111^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤90^2*111^2)) (by simpa using scale_111.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=185) hN1 (by decide) state_54 state_53 (by decide) (by decide) (Nat.le_trans (by decide : 53^2*185^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤54^2*185^2)) (by simpa using scale_185.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=259) hN1 (by decide) state_39 state_38 (by decide) (by decide) (Nat.le_trans (by decide : 38^2*259^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤39^2*259^2)) (by simpa using scale_259.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=82) hN1 (by decide) state_121 state_120 (by decide) (by decide) (Nat.le_trans (by decide : 120^2*82^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤121^2*82^2)) (by simpa using scale_82.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=123) hN1 (by decide) state_81 state_80 (by decide) (by decide) (Nat.le_trans (by decide : 80^2*123^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤81^2*123^2)) (by simpa using scale_123.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=205) hN1 (by decide) state_49 state_48 (by decide) (by decide) (Nat.le_trans (by decide : 48^2*205^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤49^2*205^2)) (by simpa using scale_205.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=287) hN1 (by decide) state_35 state_34 (by decide) (by decide) (Nat.le_trans (by decide : 34^2*287^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤35^2*287^2)) (by simpa using scale_287.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=86) hN1 (by decide) state_116 state_114 (by decide) (by decide) (Nat.le_trans (by decide : 114^2*86^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤116^2*86^2)) (by simpa using scale_86.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=129) hN1 (by decide) state_77 state_76 (by decide) (by decide) (Nat.le_trans (by decide : 76^2*129^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤77^2*129^2)) (by simpa using scale_129.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=215) hN1 (by decide) state_47 state_45 (by decide) (by decide) (Nat.le_trans (by decide : 45^2*215^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤47^2*215^2)) (by simpa using scale_215.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=301) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*301^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤33^2*301^2)) (by simpa using scale_301.1))
  exact .nil

def uppersBlock_003 : List Coeff := [(upperCut grid ⟨46634388158,46634392818,167651536495,167651536600,464196934232,464196958131,810445269564,514⟩ ⟨46539600720,46539605377,167274178005,167274178109,462437146000,462437169722,806560126112,510⟩ 94 (1135823641/125000000:ℝ)),(upperCut grid ⟨42626796096,42626800566,144867435025,144867435095,362397345678,362397359095,597341731728,314⟩ ⟨42484949753,42484954211,144585744885,144585744954,361196590859,361196604149,594968168410,312⟩ 141 (49487596721/5000000000:ℝ)),(upperCut grid ⟨37611999233,37612002449,119264768607,119264768649,259486346061,259486349072,405817761649,170⟩ ⟨37376694343,37376697419,118799652328,118799652369,257736950748,257736953609,402767790241,168⟩ 235 (27297926479/2500000000:ℝ)),(upperCut grid ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ 329 (57960575323/5000000000:ℝ)),(upperCut grid ⟨45432945059,45432949683,160570990491,160570990584,431574608944,431574629542,739553170202,443⟩ ⟨45325992170,45325996790,160145458577,160145458669,429641292133,429641312534,735427485214,439⟩ 106 (2914649283/312500000:ℝ)),(upperCut grid ⟨41431344664,41431349008,138761061369,138761061431,336712386150,336712396864,547312739098,273⟩ ⟨41271341263,41271345586,137808680417,137808680478,332766543802,332766554101,539753449636,267⟩ 159 (50689039609/5000000000:ℝ)),(upperCut grid ⟨36375860217,36375862526,113381444521,113381444558,237670824365,237670825687,368245810199,146⟩ ⟨36109177902,36109179951,112328812943,112328812979,233841786448,233841787526,361756953351,142⟩ 265 (27898647923/2500000000:ℝ)),(upperCut grid ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ 371 (59162018211/5000000000:ℝ)),(upperCut grid ⟨44308165252,44308169829,154760998728,154760998811,405465525827,405465543740,684593601362,391⟩ ⟨44188403345,44188407916,153332427300,153332427382,399135787934,399135805192,671500527938,379⟩ 118 (47706843699/5000000000:ℝ)),(upperCut grid ⟨40253514422,40253518574,133105257668,133105257723,313547610470,313547618760,503466608596,239⟩ ⟨40073329390,40073333504,131676686240,131676686294,307797108410,307797116106,492776158916,231⟩ 177 (2588074739/250000000:ℝ)),(upperCut grid ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ 295 (56869751017/5000000000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 413 (30117236691/2500000000:ℝ)),(upperCut grid ⟨44067189743,44067194308,153091463445,153091463526,398071007131,398071024278,669305242738,377⟩ ⟨43820263625,43820268176,151986374617,151986374696,393208765354,393208781994,659332426134,368⟩ 122 (48040207871/5000000000:ℝ)),(upperCut grid ⟨40073329390,40073333504,131676686240,131676686294,307797108410,307797116106,492776158916,231⟩ ⟨39702916725,39702920753,129467932032,129467932084,298973078822,298973085613,476495938936,219⟩ 183 (6511857369/625000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 305 (57203115189/5000000000:ℝ)),(upperCut grid ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ 427 (30283918777/2500000000:ℝ))]

theorem uppersBlock_003_sum : sumCoeff uppersBlock_003 = ⟨(99857483409063355830796831/5907428684568253500000000000:ℝ),(-2022177517838387367741083879160389267/9845714474280422500000000000000000000:ℝ),(2168184093982946213/112063862500000000:ℝ),(-1111673:ℝ)⟩ := by
  norm_num [uppersBlock_003,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_003_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [94,141,235,329,106,159,265,371,118,177,295,413,122,183,305,427] uppersBlock_003 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_003
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=94) hN1 (by decide) state_106 state_105 (by decide) (by decide) (Nat.le_trans (by decide : 105^2*94^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤106^2*94^2)) (by simpa using scale_94.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=141) hN1 (by decide) state_71 state_70 (by decide) (by decide) (Nat.le_trans (by decide : 70^2*141^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤71^2*141^2)) (by simpa using scale_141.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=235) hN1 (by decide) state_43 state_42 (by decide) (by decide) (Nat.le_trans (by decide : 42^2*235^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤43^2*235^2)) (by simpa using scale_235.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=329) hN1 (by decide) state_31 state_30 (by decide) (by decide) (Nat.le_trans (by decide : 30^2*329^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤31^2*329^2)) (by simpa using scale_329.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=106) hN1 (by decide) state_94 state_93 (by decide) (by decide) (Nat.le_trans (by decide : 93^2*106^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤94^2*106^2)) (by simpa using scale_106.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=159) hN1 (by decide) state_63 state_62 (by decide) (by decide) (Nat.le_trans (by decide : 62^2*159^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤63^2*159^2)) (by simpa using scale_159.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=265) hN1 (by decide) state_38 state_37 (by decide) (by decide) (Nat.le_trans (by decide : 37^2*265^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤38^2*265^2)) (by simpa using scale_265.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=371) hN1 (by decide) state_27 state_26 (by decide) (by decide) (Nat.le_trans (by decide : 26^2*371^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤27^2*371^2)) (by simpa using scale_371.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=118) hN1 (by decide) state_84 state_83 (by decide) (by decide) (Nat.le_trans (by decide : 83^2*118^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤84^2*118^2)) (by simpa using scale_118.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=177) hN1 (by decide) state_56 state_55 (by decide) (by decide) (Nat.le_trans (by decide : 55^2*177^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤56^2*177^2)) (by simpa using scale_177.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=295) hN1 (by decide) state_34 state_33 (by decide) (by decide) (Nat.le_trans (by decide : 33^2*295^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤34^2*295^2)) (by simpa using scale_295.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=413) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*413^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤24^2*413^2)) (by simpa using scale_413.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=122) hN1 (by decide) state_82 state_80 (by decide) (by decide) (Nat.le_trans (by decide : 80^2*122^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤82^2*122^2)) (by simpa using scale_122.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=183) hN1 (by decide) state_55 state_53 (by decide) (by decide) (Nat.le_trans (by decide : 53^2*183^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤55^2*183^2)) (by simpa using scale_183.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=305) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*305^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤33^2*305^2)) (by simpa using scale_305.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=427) hN1 (by decide) state_24 state_23 (by decide) (by decide) (Nat.le_trans (by decide : 23^2*427^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤24^2*427^2)) (by simpa using scale_427.1))
  exact .nil

end
end JSP233.PrimeWindowD132.Blocks
