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

def uppersBlock_036 : List Coeff := [(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3869 (82607508449/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4187 (20849348133/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4399 (8389132007/500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4717 (84589277671/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5141 (4272501187/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5353 (85854119117/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5459 (21512550957/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5671 (17286240457/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5777 (2165409819/125000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5989 (2174419803/125000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6731 (88144784783/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6943 (22113721787/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7261 (8890272317/500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7367 (44523826621/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7897 (89742376963/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8003 (89875712271/5000000000:ℝ))]

theorem uppersBlock_036_sum : sumCoeff uppersBlock_036 = ⟨(275345072493286212521555721095814033605027989724420650540781722766679803/114528389028826689599249740781723651504025501548727813714766924131912250000000:ℝ),(-119506992459457324123406902826819931417726547142571183018453396499759774535945319941/2863209725720667239981243519543091287600637538718195342869173103297806250000000000000000:ℝ),(1325393242931795960932205594305606291221/41803881755870538875623090027470033203125:ℝ),(-48:ℝ)⟩ := by
  norm_num [uppersBlock_036,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_036_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [3869,4187,4399,4717,5141,5353,5459,5671,5777,5989,6731,6943,7261,7367,7897,8003] uppersBlock_036 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_036
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3869) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3869^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3869^2)) (by simpa using scale_3869.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4187) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4187^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4187^2)) (by simpa using scale_4187.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4399) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4399^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4399^2)) (by simpa using scale_4399.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4717) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4717^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4717^2)) (by simpa using scale_4717.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5141) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5141^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5141^2)) (by simpa using scale_5141.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5353) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5353^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5353^2)) (by simpa using scale_5353.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5459) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5459^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5459^2)) (by simpa using scale_5459.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5671) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5671^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5671^2)) (by simpa using scale_5671.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5777) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5777^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5777^2)) (by simpa using scale_5777.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5989) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5989^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5989^2)) (by simpa using scale_5989.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6731) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6731^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6731^2)) (by simpa using scale_6731.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6943) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6943^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6943^2)) (by simpa using scale_6943.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7261) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7261^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7261^2)) (by simpa using scale_7261.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7367) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7367^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7367^2)) (by simpa using scale_7367.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7897) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7897^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7897^2)) (by simpa using scale_7897.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8003) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8003^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8003^2)) (by simpa using scale_8003.1))
  exact .nil

def uppersBlock_037 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8321 (90265371953/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8639 (2832512997/156250000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8851 (45441426009/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9169 (22808957459/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9487 (22894192987/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9593 (91687884201/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3599 (20471026991/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3953 (82822295447/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4189 (10425270999/625000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4307 (4183998181/250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4661 (84469847703/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4897 (84963775241/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5251 (42830866421/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5723 (86522478911/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5959 (5432910893/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6077 (87122658999/5000000000:ℝ))]

theorem uppersBlock_037_sum : sumCoeff uppersBlock_037 = ⟨(5671502255541857692014128836000259859490643079377017539043562862464252944041/2182636352645289712882322623756455161405674016454872394316203506213883302500000000:ℝ),(-490078242793334239019186820315690772803691654224649636177552012425202989753750373278603/10913181763226448564411613118782275807028370082274361971581017531069416512500000000000000000:ℝ),(4885246922904817748257666493703863779762359/145995918200823879582839436859867677968750000:ℝ),(-64:ℝ)⟩ := by
  norm_num [uppersBlock_037,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_037_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [8321,8639,8851,9169,9487,9593,3599,3953,4189,4307,4661,4897,5251,5723,5959,6077] uppersBlock_037 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_037
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8321) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8321^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8321^2)) (by simpa using scale_8321.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8639) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8639^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8639^2)) (by simpa using scale_8639.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8851) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8851^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8851^2)) (by simpa using scale_8851.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9169) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9169^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9169^2)) (by simpa using scale_9169.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9487) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9487^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9487^2)) (by simpa using scale_9487.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9593) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9593^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9593^2)) (by simpa using scale_9593.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3599) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3599^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3599^2)) (by simpa using scale_3599.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3953) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3953^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*3953^2)) (by simpa using scale_3953.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4189) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4189^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4189^2)) (by simpa using scale_4189.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4307) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4307^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4307^2)) (by simpa using scale_4307.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4661) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4661^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4661^2)) (by simpa using scale_4661.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4897) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4897^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4897^2)) (by simpa using scale_4897.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5251) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5251^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5251^2)) (by simpa using scale_5251.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5723) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5723^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5723^2)) (by simpa using scale_5723.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5959) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5959^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5959^2)) (by simpa using scale_5959.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6077) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6077^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6077^2)) (by simpa using scale_6077.1))
  exact .nil

def uppersBlock_038 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6313 (5468978591/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6431 (87688847931/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6667 (88049247291/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7493 (44608619977/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7729 (89527342319/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8083 (89975178341/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8201 (90120108413/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8791 (45407416067/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8909 (45474083721/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9263 (22834456781/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9617 (3668514843/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9853 (91955307189/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4087 (83155659619/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4331 (20933883041/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4453 (5250832987/312500000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4819 (135685139/8000000:ℝ))]

theorem uppersBlock_038_sum : sumCoeff uppersBlock_038 = ⟨(36954212306953101953853563679575722045846507985915035204311181597894964935753/19641380343351693453149736652253286426653264255896079929204471838943272761250000000:ℝ),(-930804419219430188438529785088073996756947847183040546297019509810433758762088020853/28212267083240007832734468044029426065287653340844699697219867622728056250000000000000000:ℝ),(17067829609421020588575787009130745690652191/619371221345557645499176904464525632343750000:ℝ),(-48:ℝ)⟩ := by
  norm_num [uppersBlock_038,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_038_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [6313,6431,6667,7493,7729,8083,8201,8791,8909,9263,9617,9853,4087,4331,4453,4819] uppersBlock_038 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_038
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6313) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6313^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6313^2)) (by simpa using scale_6313.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6431) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6431^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6431^2)) (by simpa using scale_6431.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6667) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6667^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6667^2)) (by simpa using scale_6667.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7493) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7493^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7493^2)) (by simpa using scale_7493.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7729) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7729^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7729^2)) (by simpa using scale_7729.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8083) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8083^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8083^2)) (by simpa using scale_8083.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8201) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8201^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8201^2)) (by simpa using scale_8201.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8791) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8791^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8791^2)) (by simpa using scale_8791.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8909) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8909^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8909^2)) (by simpa using scale_8909.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9263) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9263^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9263^2)) (by simpa using scale_9263.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9617) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9617^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9617^2)) (by simpa using scale_9617.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9853) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9853^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9853^2)) (by simpa using scale_9853.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4087) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4087^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4087^2)) (by simpa using scale_4087.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4331) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4331^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4331^2)) (by simpa using scale_4331.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4453) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4453^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4453^2)) (by simpa using scale_4453.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4819) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4819^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4819^2)) (by simpa using scale_4819.1))
  exact .nil

def uppersBlock_039 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5063 (85297139413/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5429 (42997548507/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5917 (86855843083/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6161 (4362996923/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6283 (87456023171/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6527 (21959255407/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6649 (88022212103/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6893 (88382611463/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7747 (44775302063/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7991 (89860706491/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8357 (90308542513/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8479 (18090694517/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9089 (45574098153/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9211 (45640765807/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9577 (358090591/19531250:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4757 (84673719647/5000000000:ℝ))]

theorem uppersBlock_039_sum : sumCoeff uppersBlock_039 = ⟨(76247588326386706757560366331893634765127480284804793973746374531955334205539/50888164122451410585598182641926203034573846304929435701933281212834184645000000000:ℝ),(-3377346699578111310497154754279863687900505185244595649407775266658071608888793729585571/127220410306128526463995456604815507586434615762323589254833203032085461612500000000000000000:ℝ),(23553002780508222288272153386526898856674089/996950076742375858171278473291163569687500000:ℝ),(-24:ℝ)⟩ := by
  norm_num [uppersBlock_039,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_039_bound {N:ℕ} (hlo:97365000≤N) (hhi:N≤97370944) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5063,5429,5917,6161,6283,6527,6649,6893,7747,7991,8357,8479,9089,9211,9577,4757] uppersBlock_039 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_039
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5063) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5063^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5063^2)) (by simpa using scale_5063.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5429) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5429^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5429^2)) (by simpa using scale_5429.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5917) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5917^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*5917^2)) (by simpa using scale_5917.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6161) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6161^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6161^2)) (by simpa using scale_6161.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6283) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6283^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6283^2)) (by simpa using scale_6283.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6527) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6527^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6527^2)) (by simpa using scale_6527.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6649) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6649^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6649^2)) (by simpa using scale_6649.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6893) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6893^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*6893^2)) (by simpa using scale_6893.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7747) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7747^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7747^2)) (by simpa using scale_7747.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7991) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7991^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*7991^2)) (by simpa using scale_7991.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8357) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8357^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8357^2)) (by simpa using scale_8357.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8479) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8479^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*8479^2)) (by simpa using scale_8479.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9089) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9089^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9089^2)) (by simpa using scale_9089.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9211) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9211^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9211^2)) (by simpa using scale_9211.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9577) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9577^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤2^2*9577^2)) (by simpa using scale_9577.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4757) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4757^2≤97365000) hlo) (Nat.le_trans hhi (by decide : 97370944≤3^2*4757^2)) (by simpa using scale_4757.1))
  exact .nil

end
end JSP233.PrimeWindowA132.Blocks
