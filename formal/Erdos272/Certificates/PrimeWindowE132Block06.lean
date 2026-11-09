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

def uppersBlock_024 : List Coeff := [(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2581 (7855931923/500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2813 (79420065299/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2929 (19956040169/1250000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2987 (80020245387/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3103 (20100310961/1250000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3161 (80586434319/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3277 (80946833679/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3683 (41057413171/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3799 (82424928707/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3973 (82872764729/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4031 (83017694801/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4321 (41856209261/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4379 (8384575383/500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4553 (10529426689/625000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4727 (84610457463/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4843 (84852893577/5000000000:ℝ))]

theorem uppersBlock_024_sum : sumCoeff uppersBlock_024 = ⟨(4620129027780277243472182708226981805918269649227513515293968541800095391/563594878924438096923021549062458640505156957514193759920075155224285000000000:ℝ),(-18717135371842716542634962102947715696448845832794605477534796555735339156646157699121/136671758139176238503832725647646220322500562197191986780618225141889112500000000000000000:ℝ),(1649509469528792800930681953431297099877/21054391238488997395249471195248847656250:ℝ),(-256:ℝ)⟩ := by
  norm_num [uppersBlock_024,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_024_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2581,2813,2929,2987,3103,3161,3277,3683,3799,3973,4031,4321,4379,4553,4727,4843] uppersBlock_024 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_024
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2581) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2581^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2581^2)) (by simpa using scale_2581.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2813) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2813^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2813^2)) (by simpa using scale_2813.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2929) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2929^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2929^2)) (by simpa using scale_2929.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2987) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2987^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2987^2)) (by simpa using scale_2987.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3103) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3103^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3103^2)) (by simpa using scale_3103.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3161) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3161^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3161^2)) (by simpa using scale_3161.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3277) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3277^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3277^2)) (by simpa using scale_3277.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3683) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3683^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3683^2)) (by simpa using scale_3683.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3799) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3799^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3799^2)) (by simpa using scale_3799.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3973) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3973^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3973^2)) (by simpa using scale_3973.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4031) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4031^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4031^2)) (by simpa using scale_4031.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4321) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4321^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4321^2)) (by simpa using scale_4321.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4379) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4379^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4379^2)) (by simpa using scale_4379.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4553) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4553^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4553^2)) (by simpa using scale_4553.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4727) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4727^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4727^2)) (by simpa using scale_4727.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4843) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4843^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4843^2)) (by simpa using scale_4843.1))
  exact .nil

def uppersBlock_025 : List Coeff := [(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5017 (17041174279/1000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5191 (85546813507/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5249 (133840509/7812500:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5539 (43097844861/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5597 (86299857329/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5713 (3460199709/200000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5771 (21651500921/1250000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1147 (7044904993/500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1271 (1429511819/100000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1333 (71951871261/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1457 (14568269173/1000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1643 (74042788753/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1829 (18778810981/1250000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1891 (2357769003/156250000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2077 (76386795579/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2201 (19241667031/1250000000:ℝ))]

theorem uppersBlock_025_sum : sumCoeff uppersBlock_025 = ⟨(3158536233935675822930331947002285542519458734220336133027206632182725661/82074884207223487520935358702850437067766074547930038345101995328136200000000:ℝ),(-6118613195949712294313565018069668916097770888453210271645429663229277351683724163179/10259360525902935940116919837856304633470759318491254793137749416017025000000000000000000:ℝ),(5274972385581561580446088862205991320886247/25322125362396685999416507629322863750000000:ℝ),(-1639:ℝ)⟩ := by
  norm_num [uppersBlock_025,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_025_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [5017,5191,5249,5539,5597,5713,5771,1147,1271,1333,1457,1643,1829,1891,2077,2201] uppersBlock_025 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_025
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5017) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5017^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5017^2)) (by simpa using scale_5017.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5191) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5191^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5191^2)) (by simpa using scale_5191.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5249) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5249^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5249^2)) (by simpa using scale_5249.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5539) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5539^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5539^2)) (by simpa using scale_5539.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5597) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5597^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5597^2)) (by simpa using scale_5597.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5713) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5713^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5713^2)) (by simpa using scale_5713.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5771) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5771^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5771^2)) (by simpa using scale_5771.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1147) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1147^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤9^2*1147^2)) (by simpa using scale_1147.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1271) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1271^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤8^2*1271^2)) (by simpa using scale_1271.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1333) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1333^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤8^2*1333^2)) (by simpa using scale_1333.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1457) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1457^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤7^2*1457^2)) (by simpa using scale_1457.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1643) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1643^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤7^2*1643^2)) (by simpa using scale_1643.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1829) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1829^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1829^2)) (by simpa using scale_1829.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1891) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1891^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1891^2)) (by simpa using scale_1891.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2077) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2077^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2077^2)) (by simpa using scale_2077.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2201) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2201^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2201^2)) (by simpa using scale_2201.1))
  exact .nil

def uppersBlock_026 : List Coeff := [(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2263 (9655557969/625000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2449 (15606869567/1000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2573 (78528275373/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2759 (39613116487/2500000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3007 (80086979043/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3131 (4024553721/250000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 3193 (80687159131/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3317 (20267039397/1250000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3379 (81253348063/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3503 (81613747423/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 3937 (41390870043/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4061 (83091842451/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4247 (83539678473/5000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4309 (16736921709/1000000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4619 (42189666133/2500000000:ℝ)),(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4681 (42256333787/2500000000:ℝ))]

theorem uppersBlock_026_sum : sumCoeff uppersBlock_026 = ⟨(80354644624041306210062467786169159174463741214738751539248291718515057/8078729404873323133292399679325028835544696684686367381714225929965000000000:ℝ),(-322194853971425082124619767389503107541269283998543457051121138981415854109967618017/1959091880681780859823406922236319492619588946036444090065699788016512500000000000000000:ℝ),(16213908819331360634233894971509069187/185009568256914526698559811959843750000:ℝ),(-334:ℝ)⟩ := by
  norm_num [uppersBlock_026,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_026_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [2263,2449,2573,2759,3007,3131,3193,3317,3379,3503,3937,4061,4247,4309,4619,4681] uppersBlock_026 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_026
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2263) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2263^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2263^2)) (by simpa using scale_2263.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2449) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2449^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2449^2)) (by simpa using scale_2449.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2573) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2573^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2573^2)) (by simpa using scale_2573.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2759) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2759^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*2759^2)) (by simpa using scale_2759.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3007) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3007^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3007^2)) (by simpa using scale_3007.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3131) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3131^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3131^2)) (by simpa using scale_3131.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3193) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*3193^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤4^2*3193^2)) (by simpa using scale_3193.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3317) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3317^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3317^2)) (by simpa using scale_3317.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3379) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3379^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3379^2)) (by simpa using scale_3379.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3503) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3503^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3503^2)) (by simpa using scale_3503.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=3937) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*3937^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*3937^2)) (by simpa using scale_3937.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4061) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4061^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4061^2)) (by simpa using scale_4061.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4247) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4247^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4247^2)) (by simpa using scale_4247.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4309) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4309^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4309^2)) (by simpa using scale_4309.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4619) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4619^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4619^2)) (by simpa using scale_4619.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4681) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4681^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4681^2)) (by simpa using scale_4681.1))
  exact .nil

def uppersBlock_027 : List Coeff := [(upperCut grid ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ 4867 (10612790907/625000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5053 (85277371207/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5177 (85519807321/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5363 (85872785139/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5549 (86213727251/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5611 (5395302469/312500000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5921 (43431301733/2500000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 5983 (86966771073/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6107 (87171906469/5000000000:ℝ)),(upperCut grid ⟨6931471803,6931471808,20000000000,20000000001,6931471803,6931471809,24142135624,3⟩ ⟨0,0,10000000000,10000000000,0,0,10000000000,1⟩ 6169 (21818229357/1250000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1517 (9155612103/625000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1591 (14744235427/1000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1739 (74610651739/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1961 (75812094627/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2183 (38442274899/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2257 (7721791397/500000000:ℝ))]

theorem uppersBlock_027_sum : sumCoeff uppersBlock_027 = ⟨(6961249364319872540699708992235783712304313341804345245230372587375102549989/393845094305365417372620355978120378207916034113120137603467603608119081000000000:ℝ),(-2762584022850326354428435834312744140597627826956487552299670040042139712710827541177227/9846127357634135434315508899453009455197900852828003440086690090202977025000000000000000000:ℝ),(5679923685962751899756751143997832210914539/49028967834560787807101118862001113984375000:ℝ),(-738:ℝ)⟩ := by
  norm_num [uppersBlock_027,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_027_bound {N:ℕ} (hlo:97818046≤N) (hhi:N≤97940000) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [4867,5053,5177,5363,5549,5611,5921,5983,6107,6169,1517,1591,1739,1961,2183,2257] uppersBlock_027 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_027
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=4867) hN1 (by decide) state_3 state_2 (by decide) (by decide) (Nat.le_trans (by decide : 2^2*4867^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤3^2*4867^2)) (by simpa using scale_4867.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5053) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5053^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5053^2)) (by simpa using scale_5053.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5177) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5177^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5177^2)) (by simpa using scale_5177.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5363) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5363^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5363^2)) (by simpa using scale_5363.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5549) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5549^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5549^2)) (by simpa using scale_5549.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5611) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5611^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5611^2)) (by simpa using scale_5611.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5921) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5921^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5921^2)) (by simpa using scale_5921.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=5983) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*5983^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*5983^2)) (by simpa using scale_5983.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6107) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6107^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6107^2)) (by simpa using scale_6107.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=6169) hN1 (by decide) state_2 state_1 (by decide) (by decide) (Nat.le_trans (by decide : 1^2*6169^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤2^2*6169^2)) (by simpa using scale_6169.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1517) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1517^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤7^2*1517^2)) (by simpa using scale_1517.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1591) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1591^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤7^2*1591^2)) (by simpa using scale_1591.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1739) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1739^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1739^2)) (by simpa using scale_1739.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1961) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1961^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤6^2*1961^2)) (by simpa using scale_1961.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2183) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2183^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2183^2)) (by simpa using scale_2183.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2257) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2257^2≤97818046) hlo) (Nat.le_trans hhi (by decide : 97940000≤5^2*2257^2)) (by simpa using scale_2257.1))
  exact .nil

end
end JSP233.PrimeWindowE132.Blocks
