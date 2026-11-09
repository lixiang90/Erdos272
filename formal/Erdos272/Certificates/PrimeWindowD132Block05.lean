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

def uppersBlock_020 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2603 (39322098113/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2641 (39394563149/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2831 (79483850019/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2869 (79617185327/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2983 (80006845009/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3097 (251193403/15625000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3173 (40312162537/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3287 (20244325723/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3401 (20329561251/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3439 (81429357257/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3629 (81967121219/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3667 (41035644413/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3743 (41138212111/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3781 (82377435181/5000000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 667 (6502790043/500000000:ℝ)),(upperCut grid ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ 713 (32847407087/2500000000:ℝ))]

theorem uppersBlock_020_sum : sumCoeff uppersBlock_020 = ⟨(2382720524426339854014080582096563298823966008335401416513493341029590047212551/33951757099783827627217512226147792302528863189163265130672259474328140961000000000:ℝ),(-9498272573384199039802034103152722859421766555356979036554624050153275204419883500926063/9226020951028214029135193539714073995252408475316104655073983552806560043750000000000000000:ℝ),(49374373676327901631955245445280305490635727/182087925993893521987743747242289102531250000:ℝ),(-3304:ℝ)⟩ := by
  norm_num [uppersBlock_020,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_020_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2603,2641,2831,2869,2983,3097,3173,3287,3401,3439,3629,3667,3743,3781,667,713] uppersBlock_020 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_020
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2603) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2603^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2603^2)) (by simpa using scale_2603.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2641) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2641^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2641^2)) (by simpa using scale_2641.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2831) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2831^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2831^2)) (by simpa using scale_2831.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2869) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2869^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2869^2)) (by simpa using scale_2869.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2983) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2983^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2983^2)) (by simpa using scale_2983.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3097) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3097^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3097^2)) (by simpa using scale_3097.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3173) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3173^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3173^2)) (by simpa using scale_3173.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3287) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3287^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3287^2)) (by simpa using scale_3287.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3401) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3401^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3401^2)) (by simpa using scale_3401.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3439) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3439^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3439^2)) (by simpa using scale_3439.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3629) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3629^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3629^2)) (by simpa using scale_3629.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3667) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3667^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3667^2)) (by simpa using scale_3667.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3743) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3743^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3743^2)) (by simpa using scale_3743.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3781) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3781^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3781^2)) (by simpa using scale_3781.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=667) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*667^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤15^2*667^2)) (by simpa using scale_667.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=713) hN1 (by decide) state_14 state_13 (by decide) (by decide) (Nat.le_trans (by decide : 13^2*713^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤14^2*713^2)) (by simpa using scale_713.1))
  exact .nil

def uppersBlock_021 : List Coeff := [(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 851 (4216507503/312500000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 943 (17122665267/1250000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 989 (68966941379/5000000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1081 (69856415983/5000000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1219 (71057858871/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1357 (36065157021/2500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1403 (36231839107/2500000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1541 (73401865697/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1633 (36990869121/2500000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1679 (7425953387/500000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1817 (75049417953/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1909 (75543345491/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2047 (19060325773/1250000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2231 (77102049161/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2323 (38753072269/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2369 (77702229249/5000000000:ℝ))]

theorem uppersBlock_021_sum : sumCoeff uppersBlock_021 = ⟨(68506193225241196181416302858311039170511221921842772711213238509/713726952083811790989123977530538949130810753074777499416385000000000:ℝ),(-55085818583816687138093039654329291592822490410795175544382620408468160988427/37827528460442024922423570809118564303932969912963207469068405000000000000000000:ℝ),(763721267769006195525069094870190803763/1719091521988295187771917959244375000000:ℝ),(-4488:ℝ)⟩ := by
  norm_num [uppersBlock_021,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_021_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [851,943,989,1081,1219,1357,1403,1541,1633,1679,1817,1909,2047,2231,2323,2369] uppersBlock_021 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_021
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=851) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*851^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤12^2*851^2)) (by simpa using scale_851.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=943) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*943^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤11^2*943^2)) (by simpa using scale_943.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=989) hN1 (by decide) state_11 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*989^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤11^2*989^2)) (by simpa using scale_989.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1081) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1081^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤10^2*1081^2)) (by simpa using scale_1081.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1219) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1219^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤9^2*1219^2)) (by simpa using scale_1219.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1357) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1357^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤8^2*1357^2)) (by simpa using scale_1357.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1403) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1403^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤8^2*1403^2)) (by simpa using scale_1403.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1541) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1541^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤7^2*1541^2)) (by simpa using scale_1541.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1633) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1633^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤7^2*1633^2)) (by simpa using scale_1633.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1679) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1679^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1679^2)) (by simpa using scale_1679.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1817) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1817^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1817^2)) (by simpa using scale_1817.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1909) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1909^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1909^2)) (by simpa using scale_1909.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2047) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2047^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2047^2)) (by simpa using scale_2047.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2231) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2231^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2231^2)) (by simpa using scale_2231.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2323) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2323^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2323^2)) (by simpa using scale_2323.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2369) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2369^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2369^2)) (by simpa using scale_2369.1))
  exact .nil

def uppersBlock_022 : List Coeff := [(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2461 (39041613853/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2507 (78268418181/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2599 (78628817541/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2921 (19949202551/1250000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3013 (80106912569/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3151 (80554748591/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3197 (80699678663/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3427 (5087150149/312500000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3473 (20381934423/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3611 (40958698687/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3749 (3291697653/200000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3841 (82534877439/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3979 (82887855257/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4117 (83228797369/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4163 (41669954811/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4393 (5242354599/312500000:ℝ))]

theorem uppersBlock_022_sum : sumCoeff uppersBlock_022 = ⟨(91155348336776682511207742820408688102129919152074155270907302243650007909/9543550181632187084805053932572598555842516003240119020891252760029453603515625:ℝ),(-1934235615093198039762190215226657634988081985678725428646467870609850494073171711980641/12215744232489199468550469033692926151478420484147352346740803532837700612500000000000000000:ℝ),(105673877861677526678799484041421694910014631/1235705478284024576238116615885219071250000000:ℝ),(-295:ℝ)⟩ := by
  norm_num [uppersBlock_022,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_022_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2461,2507,2599,2921,3013,3151,3197,3427,3473,3611,3749,3841,3979,4117,4163,4393] uppersBlock_022 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_022
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2461) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2461^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2461^2)) (by simpa using scale_2461.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2507) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2507^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2507^2)) (by simpa using scale_2507.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2599) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2599^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2599^2)) (by simpa using scale_2599.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2921) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2921^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*2921^2)) (by simpa using scale_2921.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3013) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3013^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3013^2)) (by simpa using scale_3013.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3151) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3151^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3151^2)) (by simpa using scale_3151.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3197) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3197^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤4^2*3197^2)) (by simpa using scale_3197.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3427) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3427^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3427^2)) (by simpa using scale_3427.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3473) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3473^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3473^2)) (by simpa using scale_3473.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3611) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3611^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3611^2)) (by simpa using scale_3611.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3749) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3749^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3749^2)) (by simpa using scale_3749.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3841) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3841^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3841^2)) (by simpa using scale_3841.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3979) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3979^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*3979^2)) (by simpa using scale_3979.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4117) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4117^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4117^2)) (by simpa using scale_4117.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4163) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4163^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4163^2)) (by simpa using scale_4163.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4393) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4393^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4393^2)) (by simpa using scale_4393.1))
  exact .nil

def uppersBlock_023 : List Coeff := [(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4439 (83981841191/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4531 (84186976587/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4577 (42143993773/2500000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 899 (8501603789/625000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1073 (34891068093/2500000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1189 (35404338603/2500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1247 (71284957517/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1363 (72174432121/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1537 (73375875009/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1711 (3722416509/250000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1769 (4673855897/312500000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1943 (15143976367/1000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2059 (3814987719/250000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2117 (9572193751/625000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2291 (77367434091/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2407 (77861361629/5000000000:ℝ))]

theorem uppersBlock_023_sum : sumCoeff uppersBlock_023 = ⟨(7241432721652974410845184729687436037209669086469971664871272642010539/108495043644443420130244180048652048427102676419125593628511513302500000000:ℝ),(-1107978040745817718873594979152433107781641145000459673399364619823611781052455447/1084950436444434201302441800486520484271026764191255936285115133025000000000000000000:ℝ),(42960324843530895140075984749107966773109/130201192657533995399211468152118125000000:ℝ),(-2949:ℝ)⟩ := by
  norm_num [uppersBlock_023,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_023_bound {N:ℕ} (hlo:97568046≤N) (hhi:N≤97818046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [4439,4531,4577,899,1073,1189,1247,1363,1537,1711,1769,1943,2059,2117,2291,2407] uppersBlock_023 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_023
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4439) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4439^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4439^2)) (by simpa using scale_4439.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4531) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4531^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4531^2)) (by simpa using scale_4531.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4577) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4577^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤3^2*4577^2)) (by simpa using scale_4577.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=899) hN1 (by decide) state_12 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*899^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤12^2*899^2)) (by simpa using scale_899.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1073) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1073^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤10^2*1073^2)) (by simpa using scale_1073.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1189) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1189^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤9^2*1189^2)) (by simpa using scale_1189.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1247) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1247^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤8^2*1247^2)) (by simpa using scale_1247.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1363) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1363^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤8^2*1363^2)) (by simpa using scale_1363.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1537) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1537^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤7^2*1537^2)) (by simpa using scale_1537.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1711) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1711^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1711^2)) (by simpa using scale_1711.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1769) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1769^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1769^2)) (by simpa using scale_1769.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1943) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1943^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤6^2*1943^2)) (by simpa using scale_1943.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2059) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2059^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2059^2)) (by simpa using scale_2059.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2117) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2117^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2117^2)) (by simpa using scale_2117.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2291) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2291^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2291^2)) (by simpa using scale_2291.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2407) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2407^2≤97568046) hlo) (Nat.le_trans hhi (by decide : 97818046≤5^2*2407^2)) (by simpa using scale_2407.1))
  exact .nil

end
end JSP233.PrimeWindowD132.Blocks
