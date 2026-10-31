import Erdos272.Certificates.CoefficientSum132
import Erdos272.Arithmetic.ScaleLogs132
namespace JSP233.PrimeWindowA132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_032 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2623 (78720735301/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2881 (2489341337/156250000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3053 (80238795329/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3139 (80516590957/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3397 (508165469/31250000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3569 (40900201289/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3827 (82498360179/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4171 (10419888281/625000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4343 (670105613/40000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4429 (1311863849/78125000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4601 (84340284793/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4687 (21131368817/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4859 (21221468657/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5461 (86053867291/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5633 (10795496207/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5891 (43405902839/2500000000:ℝ))]

theorem uppersBlock_032_sum : sumCoeff uppersBlock_032 = ⟨(83665907831182858458944053251341654135129262020334128874045019117948499/12980704409560399833193582022690221988960537779869701678611883368805000000000:ℝ),(-1754429086120794145260384952834929712558580415536983577227464281493604368914162093/16225880511950499791491977528362777486200672224837127098264854211006250000000000000000:ℝ),(295375297074953685624780624770777714941/4619422143251947215109833841153437500000:ℝ),(-184:ℝ)⟩ := by
  norm_num [uppersBlock_032,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_032_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2623,2881,3053,3139,3397,3569,3827,4171,4343,4429,4601,4687,4859,5461,5633,5891] uppersBlock_032 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_032
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2623) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2623^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*2623^2)) (by simpa using scale_2623.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2881) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2881^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*2881^2)) (by simpa using scale_2881.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3053) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3053^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*3053^2)) (by simpa using scale_3053.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3139) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3139^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*3139^2)) (by simpa using scale_3139.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3397) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3397^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3397^2)) (by simpa using scale_3397.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3569) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3569^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3569^2)) (by simpa using scale_3569.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3827) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3827^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3827^2)) (by simpa using scale_3827.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4171) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4171^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4171^2)) (by simpa using scale_4171.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4343) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4343^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4343^2)) (by simpa using scale_4343.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4429) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4429^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4429^2)) (by simpa using scale_4429.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4601) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4601^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4601^2)) (by simpa using scale_4601.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4687) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4687^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4687^2)) (by simpa using scale_4687.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4859) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4859^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4859^2)) (by simpa using scale_4859.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5461) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5461^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5461^2)) (by simpa using scale_5461.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5633) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5633^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5633^2)) (by simpa using scale_5633.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5891) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5891^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5891^2)) (by simpa using scale_5891.1))
  exact .nil

def uppersBlock_033 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5977 (347826943/20000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6407 (87651459471/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6493 (87784794779/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6751 (88174454461/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7009 (22137374603/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7181 (44395967263/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7439 (11143114043/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7697 (11185731807/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7783 (89596966709/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8213 (90134730671/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8299 (45119449139/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8471 (45222016837/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8557 (90545044633/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2491 (39102195281/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2773 (79276845733/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2867 (15922041981/1000000000:ℝ))]

theorem uppersBlock_033_sum : sumCoeff uppersBlock_033 = ⟨(1657222622722461231369250493777743031262187080475108111121116388180267757732321/435438606687820934363620987138861147384814276289239220270550036025439170592250000000:ℝ),(-173679663420516610068811253073780651318173819438011199998488529581917316745899264541996781/2721491291798880839772631169617882171155089226807745126690937725158994816201562500000000000000:ℝ),(103522250101103742983744199340048999657698911/2608395719498328363148039418808542596062500000:ℝ),(-88:ℝ)⟩ := by
  norm_num [uppersBlock_033,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_033_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5977,6407,6493,6751,7009,7181,7439,7697,7783,8213,8299,8471,8557,2491,2773,2867] uppersBlock_033 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_033
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5977) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5977^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5977^2)) (by simpa using scale_5977.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6407) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6407^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6407^2)) (by simpa using scale_6407.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6493) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6493^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6493^2)) (by simpa using scale_6493.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6751) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6751^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6751^2)) (by simpa using scale_6751.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7009) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7009^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7009^2)) (by simpa using scale_7009.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7181) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7181^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7181^2)) (by simpa using scale_7181.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7439) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7439^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7439^2)) (by simpa using scale_7439.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7697) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7697^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7697^2)) (by simpa using scale_7697.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7783) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7783^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7783^2)) (by simpa using scale_7783.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8213) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8213^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8213^2)) (by simpa using scale_8213.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8299) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8299^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8299^2)) (by simpa using scale_8299.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8471) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8471^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8471^2)) (by simpa using scale_8471.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8557) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8557^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8557^2)) (by simpa using scale_8557.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2491) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2491^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*2491^2)) (by simpa using scale_2491.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2773) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2773^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*2773^2)) (by simpa using scale_2773.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2867) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2867^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*2867^2)) (by simpa using scale_2867.1))
  exact .nil

def uppersBlock_034 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3149 (20137099347/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3337 (81128269933/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3431 (81406065561/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3713 (20548987411/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3901 (41344938591/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4183 (83387834783/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4559 (21062145213/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4747 (84652676229/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4841 (4242438047/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5029 (85229759397/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5123 (5338434367/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5311 (5360959327/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5969 (17388668379/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6157 (4362672213/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6439 (43850640141/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6533 (43923105177/2500000000:ℝ))]

theorem uppersBlock_034_sum : sumCoeff uppersBlock_034 = ⟨(17089123100732357155044877521276833949946729441681816001290726457006339/4026215347726258590182591307206730381934646646397918382392282024350250000000:ℝ),(-226199582002738620807436087929102353749296290348581811398324690085604026716643/3136463408112815179937828202672574459315909452821511889561481073437500000000000000:ℝ),(58528088139759166203951877653054149742799/1254089458613527203979438562250796562500000:ℝ),(-104:ℝ)⟩ := by
  norm_num [uppersBlock_034,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_034_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [3149,3337,3431,3713,3901,4183,4559,4747,4841,5029,5123,5311,5969,6157,6439,6533] uppersBlock_034 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_034
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3149) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3149^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*3149^2)) (by simpa using scale_3149.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3337) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3337^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3337^2)) (by simpa using scale_3337.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3431) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3431^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3431^2)) (by simpa using scale_3431.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3713) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3713^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3713^2)) (by simpa using scale_3713.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3901) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3901^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3901^2)) (by simpa using scale_3901.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4183) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4183^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4183^2)) (by simpa using scale_4183.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4559) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4559^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4559^2)) (by simpa using scale_4559.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4747) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4747^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4747^2)) (by simpa using scale_4747.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4841) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4841^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4841^2)) (by simpa using scale_4841.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5029) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5029^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5029^2)) (by simpa using scale_5029.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5123) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5123^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5123^2)) (by simpa using scale_5123.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5311) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5311^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5311^2)) (by simpa using scale_5311.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5969) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5969^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5969^2)) (by simpa using scale_5969.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6157) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6157^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6157^2)) (by simpa using scale_6157.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6439) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6439^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6439^2)) (by simpa using scale_6439.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6533) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6533^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6533^2)) (by simpa using scale_6533.1))
  exact .nil

def uppersBlock_035 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7003 (3541637363/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7097 (88674269383/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7379 (17812785813/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7661 (11179871627/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7849 (8968140913/500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8131 (22508596737/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8413 (4518766453/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8507 (90486441313/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8977 (3640968211/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9071 (45564186441/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9259 (45666754139/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9353 (91434519237/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3127 (80478288621/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3233 (80811652793/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3551 (20437460069/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3763 (82329712821/5000000000:ℝ))]

theorem uppersBlock_035_sum : sumCoeff uppersBlock_035 = ⟨(7950940448015139448297259795248755707888561042156831912080172072588605850853939/2758206152201594491823856693924126671723841093621901211972331397895106815222500000000:ℝ),(-679525227637955845441259778930640120307832616169260433538073090929320386401606149865503227/13791030761007972459119283469620633358619205468109506059861656989475534076112500000000000000000:ℝ),(45146159286100761752004497781387426554935137/1297488125068339888687387434673774168632812500:ℝ),(-80:ℝ)⟩ := by
  norm_num [uppersBlock_035,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_035_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [7003,7097,7379,7661,7849,8131,8413,8507,8977,9071,9259,9353,3127,3233,3551,3763] uppersBlock_035 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_035
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7003) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7003^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7003^2)) (by simpa using scale_7003.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7097) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7097^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7097^2)) (by simpa using scale_7097.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7379) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7379^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7379^2)) (by simpa using scale_7379.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7661) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7661^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7661^2)) (by simpa using scale_7661.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7849) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7849^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7849^2)) (by simpa using scale_7849.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8131) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8131^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8131^2)) (by simpa using scale_8131.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8413) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8413^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8413^2)) (by simpa using scale_8413.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8507) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8507^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8507^2)) (by simpa using scale_8507.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8977) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8977^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8977^2)) (by simpa using scale_8977.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9071) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9071^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9071^2)) (by simpa using scale_9071.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9259) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9259^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9259^2)) (by simpa using scale_9259.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9353) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9353^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9353^2)) (by simpa using scale_9353.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3127) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3127^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*3127^2)) (by simpa using scale_3127.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3233) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3233^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤4^2*3233^2)) (by simpa using scale_3233.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3551) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3551^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3551^2)) (by simpa using scale_3551.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3763) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3763^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3763^2)) (by simpa using scale_3763.1))
  exact .nil

end
end JSP233.PrimeWindowA132.Blocks
