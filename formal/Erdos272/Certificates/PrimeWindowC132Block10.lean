module

public import Erdos272.Certificates.CoefficientSum132
public import Erdos272.Arithmetic.ScaleLogs132
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section
namespace JSP233.PrimeWindowC132.Blocks
open PrefixState131 PrefixTable131 PrefixTable132 ScaleLogs132 PairWindow131 ScaleWindow132 SimplexMoment57 PrefixLog131
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 200000

def uppersBlock_040 : List Coeff := [(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4891 (3398060611/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5293 (42870699679/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5561 (5389707931/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5963 (86933284497/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6499 (43897015283/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6767 (88198125943/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6901 (44197105327/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7169 (88775209111/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7303 (44480199793/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7571 (44660399473/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8509 (90488791609/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8777 (45399446987/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9179 (22811682499/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9313 (22847915017/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5183 (4276569391/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5609 (86321271903/5000000000:ℝ))]

theorem uppersBlock_040_sum : sumCoeff uppersBlock_040 = ⟨(57341439583555303207873667404982020444284803241846477780848721054811/36452832482809041106225362672763516359752346277934978563986256445000000000:ℝ),(-101377254818851427135325893200031728407705321530873965553385653042417903760447/3645283248280904110622536267276351635975234627793497856398625644500000000000000000:ℝ),(647465766440495831762526676231143501201/26682754438585685191051884303208437500000:ℝ),(-24:ℝ)⟩ := by
  norm_num [uppersBlock_040,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_040_bound {N:ℕ} (hlo:97397160≤N) (hhi:N≤97568046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [4891,5293,5561,5963,6499,6767,6901,7169,7303,7571,8509,8777,9179,9313,5183,5609] uppersBlock_040 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_040
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4891) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4891^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤3^2*4891^2)) (by simpa using scale_4891.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5293) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5293^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5293^2)) (by simpa using scale_5293.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5561) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5561^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5561^2)) (by simpa using scale_5561.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5963) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5963^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5963^2)) (by simpa using scale_5963.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6499) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6499^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6499^2)) (by simpa using scale_6499.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6767) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6767^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6767^2)) (by simpa using scale_6767.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6901) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6901^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6901^2)) (by simpa using scale_6901.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7169) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7169^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7169^2)) (by simpa using scale_7169.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7303) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7303^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7303^2)) (by simpa using scale_7303.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7571) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7571^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7571^2)) (by simpa using scale_7571.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8509) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8509^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8509^2)) (by simpa using scale_8509.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8777) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8777^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8777^2)) (by simpa using scale_8777.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9179) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9179^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9179^2)) (by simpa using scale_9179.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9313) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9313^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9313^2)) (by simpa using scale_9313.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5183) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5183^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5183^2)) (by simpa using scale_5183.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5609) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5609^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5609^2)) (by simpa using scale_5609.1))
  exact .nil

def uppersBlock_041 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5893 (86815199441/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6319 (43756578521/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6887 (88373903111/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7171 (11097249811/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7313 (88974083199/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7597 (11169385207/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7739 (89540272131/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8023 (89900671491/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9017 (45534332077/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9301 (91378766519/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9727 (91826602541/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,0,0,0,0,0,0⟩ 9869 (91971532613/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5767 (86599067531/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6059 (87092995069/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6497 (8779095267/500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7081 (88651698739/5000000000:ℝ))]

theorem uppersBlock_041_sum : sumCoeff uppersBlock_041 = ⟨(1251624514627906565324086531371976800522145465333869628798437141/1015059937703526428665219499687110613715536485796808269213250625000000:ℝ),(-44815004974543198779031390540925460405864631024358560605540990033/2030119875407052857330438999374221227431072971593616538426501250000000:ℝ),(2106525502453950857406451846532065891/99562516561886885041238374265703125000:ℝ),(-15:ℝ)⟩ := by
  norm_num [uppersBlock_041,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_041_bound {N:ℕ} (hlo:97397160≤N) (hhi:N≤97568046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5893,6319,6887,7171,7313,7597,7739,8023,9017,9301,9727,9869,5767,6059,6497,7081] uppersBlock_041 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_041
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5893) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5893^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5893^2)) (by simpa using scale_5893.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6319) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6319^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6319^2)) (by simpa using scale_6319.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6887) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6887^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6887^2)) (by simpa using scale_6887.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7171) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7171^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7171^2)) (by simpa using scale_7171.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7313) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7313^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7313^2)) (by simpa using scale_7313.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7597) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7597^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7597^2)) (by simpa using scale_7597.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7739) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7739^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7739^2)) (by simpa using scale_7739.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8023) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8023^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8023^2)) (by simpa using scale_8023.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9017) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9017^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9017^2)) (by simpa using scale_9017.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9301) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9301^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9301^2)) (by simpa using scale_9301.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9727) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9727^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9727^2)) (by simpa using scale_9727.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9869) hN1 (by decide) state_2 state_0 (by decide) (by decide) (Nat.le_trans (by decide : 0^2*9869^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9869^2)) (by simpa using scale_9869.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5767) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5767^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*5767^2)) (by simpa using scale_5767.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6059) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6059^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6059^2)) (by simpa using scale_6059.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6497) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6497^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6497^2)) (by simpa using scale_6497.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7081) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7081^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7081^2)) (by simpa using scale_7081.1))
  exact .nil

def uppersBlock_042 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7373 (22263948529/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7519 (89251878827/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7811 (22408219321/1250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7957 (89818067759/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8249 (90178467119/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9271 (45673229891/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9563 (91656562147/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6557 (5492679947/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7031 (88580836753/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7663 (44720791411/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7979 (89845678199/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8137 (9004176291/500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8453 (90422761367/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8611 (45303975921/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8927 (45484175601/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 7387 (89074764291/5000000000:ℝ))]

theorem uppersBlock_042_sum : sumCoeff uppersBlock_042 = ⟨(566857016097452044163172882130224239701891918428939/555270057552959459179991058596034701600368103055625000000:ℝ),(-10274570285362807079270120935218655727031408585835607/555270057552959459179991058596034701600368103055625000000:ℝ),(178779551288732760369572341462/9204753489867527848505048828125:ℝ),(-16:ℝ)⟩ := by
  norm_num [uppersBlock_042,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_042_bound {N:ℕ} (hlo:97397160≤N) (hhi:N≤97568046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [7373,7519,7811,7957,8249,9271,9563,6557,7031,7663,7979,8137,8453,8611,8927,7387] uppersBlock_042 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_042
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7373) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7373^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7373^2)) (by simpa using scale_7373.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7519) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7519^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7519^2)) (by simpa using scale_7519.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7811) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7811^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7811^2)) (by simpa using scale_7811.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7957) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7957^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7957^2)) (by simpa using scale_7957.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8249) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8249^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8249^2)) (by simpa using scale_8249.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9271) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9271^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9271^2)) (by simpa using scale_9271.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9563) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9563^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9563^2)) (by simpa using scale_9563.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6557) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6557^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*6557^2)) (by simpa using scale_6557.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7031) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7031^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7031^2)) (by simpa using scale_7031.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7663) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7663^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7663^2)) (by simpa using scale_7663.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7979) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7979^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7979^2)) (by simpa using scale_7979.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8137) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8137^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8137^2)) (by simpa using scale_8137.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8453) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8453^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8453^2)) (by simpa using scale_8453.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8611) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8611^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8611^2)) (by simpa using scale_8611.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8927) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8927^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8927^2)) (by simpa using scale_8927.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=7387) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*7387^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*7387^2)) (by simpa using scale_7387.1))
  exact .nil

def uppersBlock_043 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8051 (2248387759/125000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8383 (90339605737/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8549 (5658480653/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8881 (18183337781/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9047 (4555093969/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9379 (4573113937/250000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8633 (90633467961/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 8989 (45518781669/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9167 (91233648049/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9523 (45807323253/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9701 (91799836981/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 9797 (91898309407/5000000000:ℝ))]

theorem uppersBlock_043_sum : sumCoeff uppersBlock_043 = ⟨(14415741746511782067288689748999957/24127610341882077509360337374232250000000:ℝ),(-1325205331865109521983490785919224023/120638051709410387546801686871161250000000:ℝ),(396241752316751230237/30699914966979446875000:ℝ),(-12:ℝ)⟩ := by
  norm_num [uppersBlock_043,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_043_bound {N:ℕ} (hlo:97397160≤N) (hhi:N≤97568046) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [8051,8383,8549,8881,9047,9379,8633,8989,9167,9523,9701,9797] uppersBlock_043 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_043
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8051) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8051^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8051^2)) (by simpa using scale_8051.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8383) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8383^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8383^2)) (by simpa using scale_8383.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8549) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8549^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8549^2)) (by simpa using scale_8549.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8881) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8881^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8881^2)) (by simpa using scale_8881.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9047) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9047^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9047^2)) (by simpa using scale_9047.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9379) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9379^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9379^2)) (by simpa using scale_9379.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8633) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8633^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8633^2)) (by simpa using scale_8633.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=8989) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*8989^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*8989^2)) (by simpa using scale_8989.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9167) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9167^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9167^2)) (by simpa using scale_9167.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9523) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9523^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9523^2)) (by simpa using scale_9523.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9701) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9701^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9701^2)) (by simpa using scale_9701.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=9797) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*9797^2≤97397160) hlo) (Nat.le_trans hhi (by decide : 97568046≤2^2*9797^2)) (by simpa using scale_9797.1))
  exact .nil

end
end JSP233.PrimeWindowC132.Blocks
