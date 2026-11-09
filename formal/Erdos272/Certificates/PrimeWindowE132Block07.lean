module

public import Erdos272.Certificates.CoefficientSum132
public import Erdos272.Arithmetic.ScaleLogs132
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimeWindowE132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_028 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2479 (78156101453/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2627 (39367986999/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2701 (39506884813/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2923 (79803653709/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3071 (80297581247/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3293 (2531110589/156250000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3589 (81856284917/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3737 (41130190147/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3811 (16491293001/1000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3959 (41418731731/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4033 (83022653937/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4181 (83383053297/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4699 (2113776149/125000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4847 (3394445933/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5069 (85308984347/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5143 (85453914419/5000000000:ℝ))]

theorem uppersBlock_028_sum : sumCoeff uppersBlock_028 = ⟨(50559973975501125035162833571762453258728080240157091091470849498608357/6237990958620697159302815187376656737062620256811623206762148134150625000000:ℝ),(-125534291910263455751839882020398578852922621506625686345525883553711915838193297/931043426659805546164599281698008468218301530867406448770469870768750000000000000000:ℝ),(84879148147302891211561156676679478371/1132181094297787100996467567911367187500:ℝ),(-224:ℝ)⟩ := by
  norm_num [uppersBlock_028,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_028_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2479,2627,2701,2923,3071,3293,3589,3737,3811,3959,4033,4181,4699,4847,5069,5143] uppersBlock_028 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_028
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2479) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2479^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2479^2)) (by simpa using scale_2479.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2627) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2627^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2627^2)) (by simpa using scale_2627.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2701) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2701^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2701^2)) (by simpa using scale_2701.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2923) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2923^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2923^2)) (by simpa using scale_2923.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3071) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3071^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3071^2)) (by simpa using scale_3071.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3293) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3293^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3293^2)) (by simpa using scale_3293.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3589) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3589^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3589^2)) (by simpa using scale_3589.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3737) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3737^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3737^2)) (by simpa using scale_3737.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3811) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3811^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3811^2)) (by simpa using scale_3811.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3959) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3959^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3959^2)) (by simpa using scale_3959.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4033) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4033^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4033^2)) (by simpa using scale_4033.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4181) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4181^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4181^2)) (by simpa using scale_4181.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4699) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4699^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4699^2)) (by simpa using scale_4699.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4847) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4847^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4847^2)) (by simpa using scale_4847.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5069) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5069^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5069^2)) (by simpa using scale_5069.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5143) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5143^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5143^2)) (by simpa using scale_5143.1))
  exact .nil

def uppersBlock_029 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5513 (4307431907/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5587 (10785246681/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5809 (8667163313/500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6031 (87046677081/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6179 (17457822639/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6401 (87642091013/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6623 (140772853/8000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6697 (44047072689/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7067 (4431595467/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7141 (88736076947/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7289 (88941212343/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7363 (44521111651/2500000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1763 (14949543631/1000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1927 (75637192759/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2173 (76838635647/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2419 (38955545409/2500000000:ℝ))]

theorem uppersBlock_029_sum : sumCoeff uppersBlock_029 = ⟨(30467426284653286108919507888126260662573153274692290254631951154752274376071/3241457763846242974750816565245540792000799605457254813710202349157233267500000000:ℝ),(-105836274635415872468720280962770110705167783976659712994871515042740339025460771876552729/696913419226942239571425561527791270280171915173309784947693505068805152512500000000000000000:ℝ),(9070096323595137188742369187711648466698971/126128345912762664098442759961257514375000000:ℝ),(-340:ℝ)⟩ := by
  norm_num [uppersBlock_029,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_029_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5513,5587,5809,6031,6179,6401,6623,6697,7067,7141,7289,7363,1763,1927,2173,2419] uppersBlock_029 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_029
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5513) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5513^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5513^2)) (by simpa using scale_5513.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5587) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5587^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5587^2)) (by simpa using scale_5587.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5809) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5809^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5809^2)) (by simpa using scale_5809.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6031) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6031^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6031^2)) (by simpa using scale_6031.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6179) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6179^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6179^2)) (by simpa using scale_6179.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6401) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6401^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6401^2)) (by simpa using scale_6401.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6623) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6623^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6623^2)) (by simpa using scale_6623.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6697) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6697^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6697^2)) (by simpa using scale_6697.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7067) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7067^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7067^2)) (by simpa using scale_7067.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7141) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7141^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7141^2)) (by simpa using scale_7141.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7289) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7289^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7289^2)) (by simpa using scale_7289.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7363) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7363^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7363^2)) (by simpa using scale_7363.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1763) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1763^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1763^2)) (by simpa using scale_1763.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1927) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1927^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1927^2)) (by simpa using scale_1927.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2173) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2173^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2173^2)) (by simpa using scale_2173.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2419) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2419^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2419^2)) (by simpa using scale_2419.1))
  exact .nil

def uppersBlock_030 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2501 (7824445499/500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2747 (79182642473/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2911 (39881257509/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2993 (40020155323/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3239 (80830194729/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3403 (81324122267/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3649 (20505519967/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3977 (82882825937/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4141 (41643460657/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4223 (3339320241/200000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4387 (41932002241/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4469 (84049194957/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4633 (84409594317/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5207 (4278879349/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5371 (17177537869/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5617 (86335525367/5000000000:ℝ))]

theorem uppersBlock_030_sum : sumCoeff uppersBlock_030 = ⟨(21338307901481430929554445484165353079133870550570702972604650954975607/2950319647440647933964090235281539097274562467274333223600131955511250000000:ℝ),(-3562317076886374350406029244187430108138326378937455083555538631335973676498890443/29503196474406479339640902352815390972745624672743332236001319555112500000000000000000:ℝ),(303534417728327746057709386338902714941/4404565299379763623709376453192812500000:ℝ),(-200:ℝ)⟩ := by
  norm_num [uppersBlock_030,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_030_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2501,2747,2911,2993,3239,3403,3649,3977,4141,4223,4387,4469,4633,5207,5371,5617] uppersBlock_030 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_030
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2501) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2501^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2501^2)) (by simpa using scale_2501.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2747) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2747^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2747^2)) (by simpa using scale_2747.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2911) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2911^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2911^2)) (by simpa using scale_2911.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2993) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2993^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2993^2)) (by simpa using scale_2993.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3239) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3239^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3239^2)) (by simpa using scale_3239.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3403) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3403^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3403^2)) (by simpa using scale_3403.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3649) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3649^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3649^2)) (by simpa using scale_3649.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3977) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3977^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3977^2)) (by simpa using scale_3977.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4141) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4141^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4141^2)) (by simpa using scale_4141.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4223) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4223^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4223^2)) (by simpa using scale_4223.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4387) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4387^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4387^2)) (by simpa using scale_4387.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4469) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4469^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4469^2)) (by simpa using scale_4469.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4633) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4633^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4633^2)) (by simpa using scale_4633.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5207) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5207^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5207^2)) (by simpa using scale_5207.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5371) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5371^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5371^2)) (by simpa using scale_5371.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5617) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5617^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5617^2)) (by simpa using scale_5617.1))
  exact .nil

def uppersBlock_031 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5699 (86480455439/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6109 (2179379479/125000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6191 (21827128617/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6437 (1753963483/100000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6683 (88073218101/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6847 (17663130843/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7093 (88668632033/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7339 (17801914829/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7421 (44560343199/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7831 (2241461259/125000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7913 (89762617967/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8077 (89967753363/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8159 (45034382161/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2021 (7611347307/500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2279 (38657457979/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2537 (78387371129/5000000000:ℝ))]

theorem uppersBlock_031_sum : sumCoeff uppersBlock_031 = ⟨(10786372180724679728884231198102255159136357015828381760488582753185084740636179/1967138666600986268920308732546158529303608703150258342582087101743518532022500000000:ℝ),(-884749733536194968727243699133879977412203220188011717940310838790896016771595454209624553/9835693333004931344601543662730792646518043515751291712910435508717592660112500000000000000000:ℝ),(21153594175492068829438911291280637742706127/438296002046850257742088590865369862453125000:ℝ),(-166:ℝ)⟩ := by
  norm_num [uppersBlock_031,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_031_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5699,6109,6191,6437,6683,6847,7093,7339,7421,7831,7913,8077,8159,2021,2279,2537] uppersBlock_031 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_031
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5699) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5699^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5699^2)) (by simpa using scale_5699.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6109) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6109^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6109^2)) (by simpa using scale_6109.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6191) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6191^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6191^2)) (by simpa using scale_6191.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6437) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6437^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6437^2)) (by simpa using scale_6437.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6683) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6683^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6683^2)) (by simpa using scale_6683.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6847) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6847^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6847^2)) (by simpa using scale_6847.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7093) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7093^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7093^2)) (by simpa using scale_7093.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7339) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7339^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7339^2)) (by simpa using scale_7339.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7421) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7421^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7421^2)) (by simpa using scale_7421.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7831) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7831^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7831^2)) (by simpa using scale_7831.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7913) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7913^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*7913^2)) (by simpa using scale_7913.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8077) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8077^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*8077^2)) (by simpa using scale_8077.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8159) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8159^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*8159^2)) (by simpa using scale_8159.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2021) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2021^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2021^2)) (by simpa using scale_2021.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2279) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2279^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2279^2)) (by simpa using scale_2279.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2537) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2537^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2537^2)) (by simpa using scale_2537.1))
  exact .nil

end
end JSP233.PrimeWindowE132.Blocks
