module

public import Erdos272.Certificates.CoefficientSum132
public import Erdos272.Arithmetic.ScaleLogs132
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimeWindowA132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_008 : List Coeff := [(upperCut grid ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ 298 (56970932041/5000000000:ℝ)),(upperCut grid ⟨31354942146,31354942172,90184206839,90184206861,158883394201,158883394321,241154625696,76⟩ ⟨30910424521,30910424546,89314641622,89314641643,156156877493,156156877610,236984337414,74⟩ 447 (30512791561/2500000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 745 (66133839359/5000000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1043 (17374640431/1250000000:ℝ)),(upperCut grid ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ 302 (57104267349/5000000000:ℝ)),(upperCut grid ⟨30910424521,30910424546,89314641622,89314641643,156156877493,156156877610,236984337414,74⟩ ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ 453 (6115891843/500000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 755 (66267174667/5000000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1057 (8703987129/625000000:ℝ)),(upperCut grid ⟨34657359011,34657359046,105756823461,105756823492,210481036767,210481036943,322884689912,119⟩ ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ 314 (57493927031/5000000000:ℝ)),(upperCut grid ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ 471 (961696533/78125000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 785 (66656834349/5000000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1099 (35010778357/2500000000:ℝ)),(upperCut grid ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ 326 (28934485491/2500000000:ℝ)),(upperCut grid ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ 489 (61923622063/5000000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 815 (670318783/50000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1141 (14079320133/1000000000:ℝ))]

theorem uppersBlock_008_sum : sumCoeff uppersBlock_008 = ⟨(49365133622053605988034271947/36549340354083846980250000000000:ℝ),(-744941064525013355632035713606818547163/40610378171204274422500000000000000000000:ℝ),(90010266769326448933/30228025222500000000:ℝ),(-80514:ℝ)⟩ := by
  norm_num [uppersBlock_008,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_008_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [298,447,745,1043,302,453,755,1057,314,471,785,1099,326,489,815,1141] uppersBlock_008 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_008
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=298) hN1 (by decide) state_34 state_33 (by decide) (by decide) (Nat.le_trans (by decide : 33^2*298^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤34^2*298^2)) (by simpa using scale_298.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=447) hN1 (by decide) state_23 state_22 (by decide) (by decide) (Nat.le_trans (by decide : 22^2*447^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤23^2*447^2)) (by simpa using scale_447.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=745) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*745^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤14^2*745^2)) (by simpa using scale_745.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1043) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1043^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤10^2*1043^2)) (by simpa using scale_1043.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=302) hN1 (by decide) state_33 state_32 (by decide) (by decide) (Nat.le_trans (by decide : 32^2*302^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤33^2*302^2)) (by simpa using scale_302.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=453) hN1 (by decide) state_22 state_21 (by decide) (by decide) (Nat.le_trans (by decide : 21^2*453^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤22^2*453^2)) (by simpa using scale_453.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=755) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*755^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤14^2*755^2)) (by simpa using scale_755.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1057) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1057^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤10^2*1057^2)) (by simpa using scale_1057.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=314) hN1 (by decide) state_32 state_31 (by decide) (by decide) (Nat.le_trans (by decide : 31^2*314^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤32^2*314^2)) (by simpa using scale_314.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=471) hN1 (by decide) state_21 state_20 (by decide) (by decide) (Nat.le_trans (by decide : 20^2*471^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤21^2*471^2)) (by simpa using scale_471.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=785) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*785^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤13^2*785^2)) (by simpa using scale_785.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1099) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1099^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤9^2*1099^2)) (by simpa using scale_1099.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=326) hN1 (by decide) state_31 state_30 (by decide) (by decide) (Nat.le_trans (by decide : 30^2*326^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤31^2*326^2)) (by simpa using scale_326.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=489) hN1 (by decide) state_21 state_20 (by decide) (by decide) (Nat.le_trans (by decide : 20^2*489^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤21^2*489^2)) (by simpa using scale_489.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=815) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*815^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤13^2*815^2)) (by simpa using scale_815.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1141) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1141^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤9^2*1141^2)) (by simpa using scale_1141.1))
  exact .nil

def uppersBlock_009 : List Coeff := [(upperCut grid ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ 334 (7263925887/625000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 501 (62166058177/5000000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 835 (33637157207/2500000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1169 (70639036779/5000000000:ℝ)),(upperCut grid ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ 346 (29232192457/2500000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 519 (12503807199/1000000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 865 (8453411529/625000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1211 (70992014597/5000000000:ℝ)),(upperCut grid ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ 358 (29402663513/2500000000:ℝ)),(upperCut grid ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ 537 (62859978107/5000000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 895 (8496029293/625000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1253 (71332956709/5000000000:ℝ)),(upperCut grid ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ 362 (58916439279/5000000000:ℝ)),(upperCut grid ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ 543 (1574277259/125000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 905 (68079346597/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1267 (35722034481/2500000000:ℝ))]

theorem uppersBlock_009_sum : sumCoeff uppersBlock_009 = ⟨(27720921195973987162090019743/27599353815882274051500000000000:ℝ),(-533616425797305390990704720363697540059/38639095342235183672100000000000000000000:ℝ),(36781187548745638661/15356898194531250000:ℝ),(-57352:ℝ)⟩ := by
  norm_num [uppersBlock_009,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_009_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [334,501,835,1169,346,519,865,1211,358,537,895,1253,362,543,905,1267] uppersBlock_009 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_009
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=334) hN1 (by decide) state_30 state_29 (by decide) (by decide) (Nat.le_trans (by decide : 29^2*334^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤30^2*334^2)) (by simpa using scale_334.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=501) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*501^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤20^2*501^2)) (by simpa using scale_501.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=835) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*835^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤12^2*835^2)) (by simpa using scale_835.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1169) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1169^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤9^2*1169^2)) (by simpa using scale_1169.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=346) hN1 (by decide) state_29 state_28 (by decide) (by decide) (Nat.le_trans (by decide : 28^2*346^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤29^2*346^2)) (by simpa using scale_346.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=519) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*519^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤20^2*519^2)) (by simpa using scale_519.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=865) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*865^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤12^2*865^2)) (by simpa using scale_865.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1211) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1211^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤9^2*1211^2)) (by simpa using scale_1211.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=358) hN1 (by decide) state_28 state_27 (by decide) (by decide) (Nat.le_trans (by decide : 27^2*358^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤28^2*358^2)) (by simpa using scale_358.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=537) hN1 (by decide) state_19 state_18 (by decide) (by decide) (Nat.le_trans (by decide : 18^2*537^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤19^2*537^2)) (by simpa using scale_537.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=895) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*895^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤12^2*895^2)) (by simpa using scale_895.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1253) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1253^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1253^2)) (by simpa using scale_1253.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=362) hN1 (by decide) state_28 state_27 (by decide) (by decide) (Nat.le_trans (by decide : 27^2*362^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤28^2*362^2)) (by simpa using scale_362.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=543) hN1 (by decide) state_19 state_18 (by decide) (by decide) (Nat.le_trans (by decide : 18^2*543^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤19^2*543^2)) (by simpa using scale_543.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=905) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*905^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤11^2*905^2)) (by simpa using scale_905.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1267) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1267^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1267^2)) (by simpa using scale_1267.1))
  exact .nil

def uppersBlock_010 : List Coeff := [(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 382 (59454203241/5000000000:ℝ)),(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 573 (31754427161/2500000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 955 (68617110559/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1337 (17995458231/1250000000:ℝ)),(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 386 (1861199089/156250000:ℝ)),(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 579 (63613021929/5000000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 965 (34360639083/2500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1351 (72086000531/5000000000:ℝ)),(upperCut grid ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ 394 (14940876561/1250000000:ℝ)),(upperCut grid ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ 591 (2552726293/200000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 985 (34463206781/2500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1379 (72291135927/5000000000:ℝ)),(upperCut grid ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ 398 (59864517203/5000000000:ℝ)),(upperCut grid ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ 597 (15979792071/1250000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 995 (69027424521/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1393 (36196073443/2500000000:ℝ))]

theorem uppersBlock_010_sum : sumCoeff uppersBlock_010 = ⟨(117591977444306930678137726463/153499617190927245493500000000000:ℝ),(-12257403170199244637497710823480596330319/1151247128931954341201250000000000000000000:ℝ),(61892296572016791159/31612441634375000000:ℝ),(-43911:ℝ)⟩ := by
  norm_num [uppersBlock_010,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_010_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [382,573,955,1337,386,579,965,1351,394,591,985,1379,398,597,995,1393] uppersBlock_010 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_010
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=382) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*382^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤26^2*382^2)) (by simpa using scale_382.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=573) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*573^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤18^2*573^2)) (by simpa using scale_573.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=955) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*955^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤11^2*955^2)) (by simpa using scale_955.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1337) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1337^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1337^2)) (by simpa using scale_1337.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=386) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*386^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤26^2*386^2)) (by simpa using scale_386.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=579) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*579^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤18^2*579^2)) (by simpa using scale_579.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=965) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*965^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤11^2*965^2)) (by simpa using scale_965.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1351) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1351^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1351^2)) (by simpa using scale_1351.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=394) hN1 (by decide) state_26 state_25 (by decide) (by decide) (Nat.le_trans (by decide : 25^2*394^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤26^2*394^2)) (by simpa using scale_394.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=591) hN1 (by decide) state_17 state_16 (by decide) (by decide) (Nat.le_trans (by decide : 16^2*591^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤17^2*591^2)) (by simpa using scale_591.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=985) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*985^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤11^2*985^2)) (by simpa using scale_985.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1379) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1379^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1379^2)) (by simpa using scale_1379.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=398) hN1 (by decide) state_25 state_24 (by decide) (by decide) (Nat.le_trans (by decide : 24^2*398^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤25^2*398^2)) (by simpa using scale_398.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=597) hN1 (by decide) state_17 state_16 (by decide) (by decide) (Nat.le_trans (by decide : 16^2*597^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤17^2*597^2)) (by simpa using scale_597.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=995) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*995^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤10^2*995^2)) (by simpa using scale_995.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1393) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1393^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤8^2*1393^2)) (by simpa using scale_1393.1))
  exact .nil

def uppersBlock_011 : List Coeff := [(upperCut grid ⟨42484949753,42484954211,144585744885,144585744954,361196590859,361196604149,594968168410,312⟩ ⟨42341062386,42341066831,143442887743,143442887811,356341168031,356341180810,585406339530,304⟩ 143 (49628446289/5000000000:ℝ)),(upperCut grid ⟨39702916725,39702920753,129467932032,129467932084,298973078822,298973085613,476495938936,219⟩ ⟨39512434805,39512438783,129090573542,129090573593,297474855550,297474862188,473748727656,217⟩ 187 (52311086153/5000000000:ℝ)),(upperCut grid ⟨38712007880,38712011604,125340168767,125340168814,282754769522,282754774694,447056108705,198⟩ ⟨38501473837,38501477479,123256835434,123256835480,274689767881,274689772276,432622351975,188⟩ 209 (53423342503/5000000000:ℝ)),(upperCut grid ⟨36888792903,36888795643,116407085546,116407085585,248806081913,248806084045,387300047003,158⟩ ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ 253 (13833473717/1250000000:ℝ)),(upperCut grid ⟨34339872028,34339872062,103881823461,103881823491,203982781953,203982782121,312278088194,113⟩ ⟨34011973800,34011973833,103236662171,103236662200,201767306339,201767306504,308685982152,111⟩ 319 (28825955503/2500000000:ℝ)),(upperCut grid ⟨33672958284,33672958316,100569995505,100569995533,192697446659,192697446815,294080047280,103⟩ ⟨33322045086,33322045117,99880340333,99880340360,190375173674,190375173827,290366140516,101⟩ 341 (233275299/20000000:ℝ)),(upperCut grid ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ 407 (938877041/78125000:ℝ)),(upperCut grid ⟨30910424521,30910424546,89314641622,89314641643,156156877493,156156877610,236984337414,74⟩ ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ 451 (15278667911/1250000000:ℝ)),(upperCut grid ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ 473 (12318190391/1000000000:ℝ)),(upperCut grid ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ 517 (62480426559/5000000000:ℝ)),(upperCut grid ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ 583 (63681869447/5000000000:ℝ)),(upperCut grid ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ 649 (32377162309/2500000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 671 (6508768879/500000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 737 (66025876273/5000000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 781 (33302874409/2500000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 803 (33441772223/2500000000:ℝ))]

theorem uppersBlock_011_sum : sumCoeff uppersBlock_011 = ⟨(752162751018283540139517784965550808359723184621667179537743/188084680466762170865481809262031449961266399529974245000000000:ℝ),(-7175867650816152996848232712302670356119685338041574680655608834381/140027308268881902073765492303477851370805836457693750000000000000000:ℝ),(381879372226783110155116692782705123/60609643748882476414615064687500000:ℝ),(-249808:ℝ)⟩ := by
  norm_num [uppersBlock_011,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_011_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [143,187,209,253,319,341,407,451,473,517,583,649,671,737,781,803] uppersBlock_011 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_011
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=143) hN1 (by decide) state_70 state_69 (by decide) (by decide) (Nat.le_trans (by decide : 69^2*143^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤70^2*143^2)) (by simpa using scale_143.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=187) hN1 (by decide) state_53 state_52 (by decide) (by decide) (Nat.le_trans (by decide : 52^2*187^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤53^2*187^2)) (by simpa using scale_187.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=209) hN1 (by decide) state_48 state_47 (by decide) (by decide) (Nat.le_trans (by decide : 47^2*209^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤48^2*209^2)) (by simpa using scale_209.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=253) hN1 (by decide) state_40 state_39 (by decide) (by decide) (Nat.le_trans (by decide : 39^2*253^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤40^2*253^2)) (by simpa using scale_253.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=319) hN1 (by decide) state_31 state_30 (by decide) (by decide) (Nat.le_trans (by decide : 30^2*319^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤31^2*319^2)) (by simpa using scale_319.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=341) hN1 (by decide) state_29 state_28 (by decide) (by decide) (Nat.le_trans (by decide : 28^2*341^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤29^2*341^2)) (by simpa using scale_341.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=407) hN1 (by decide) state_25 state_24 (by decide) (by decide) (Nat.le_trans (by decide : 24^2*407^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤25^2*407^2)) (by simpa using scale_407.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=451) hN1 (by decide) state_22 state_21 (by decide) (by decide) (Nat.le_trans (by decide : 21^2*451^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤22^2*451^2)) (by simpa using scale_451.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=473) hN1 (by decide) state_21 state_20 (by decide) (by decide) (Nat.le_trans (by decide : 20^2*473^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤21^2*473^2)) (by simpa using scale_473.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=517) hN1 (by decide) state_20 state_19 (by decide) (by decide) (Nat.le_trans (by decide : 19^2*517^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤20^2*517^2)) (by simpa using scale_517.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=583) hN1 (by decide) state_17 state_16 (by decide) (by decide) (Nat.le_trans (by decide : 16^2*583^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤17^2*583^2)) (by simpa using scale_583.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=649) hN1 (by decide) state_16 state_15 (by decide) (by decide) (Nat.le_trans (by decide : 15^2*649^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤16^2*649^2)) (by simpa using scale_649.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=671) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*671^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤15^2*671^2)) (by simpa using scale_671.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=737) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*737^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤14^2*737^2)) (by simpa using scale_737.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=781) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*781^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤13^2*781^2)) (by simpa using scale_781.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=803) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*803^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤13^2*803^2)) (by simpa using scale_803.1))
  exact .nil

end
end JSP233.PrimeWindowA132.Blocks
