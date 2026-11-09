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

def uppersBlock_012 : List Coeff := [(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 869 (67673428529/5000000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 913 (68167356067/5000000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 979 (17216328417/1250000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1067 (69726059737/5000000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1111 (35065077557/2500000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1133 (2813049593/200000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1177 (35353619141/2500000000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1199 (70892428757/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1243 (71252828117/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1397 (3621041039/250000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1441 (14546184629/1000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1507 (73178759167/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1529 (73323689239/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1639 (462615081/31250000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1661 (18537937067/1250000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1727 (1490828159/100000000:ℝ))]

theorem uppersBlock_012_sum : sumCoeff uppersBlock_012 = ⟨(14213929153859367360908502707742563214630371696774848872595714884114854647/114095987611382307165966325742629617183170678406299998213290003181951250000000:ℝ),(-3088270912970669705822308518079719515970853449887430445581278430478543140974153441/1641668886494709455625414758886757081772239977069064722493381340747500000000000000000:ℝ),(410785386088789103662597266071229199150883/746397557946636553509445091521744609375000:ℝ),(-5924:ℝ)⟩ := by
  norm_num [uppersBlock_012,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_012_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [869,913,979,1067,1111,1133,1177,1199,1243,1397,1441,1507,1529,1639,1661,1727] uppersBlock_012 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_012
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=869) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*869^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤12^2*869^2)) (by simpa using scale_869.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=913) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*913^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤11^2*913^2)) (by simpa using scale_913.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=979) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*979^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤11^2*979^2)) (by simpa using scale_979.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1067) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1067^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤10^2*1067^2)) (by simpa using scale_1067.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1111) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1111^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9^2*1111^2)) (by simpa using scale_1111.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1133) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1133^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9^2*1133^2)) (by simpa using scale_1133.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1177) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1177^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9^2*1177^2)) (by simpa using scale_1177.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1199) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1199^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9^2*1199^2)) (by simpa using scale_1199.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1243) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1243^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1243^2)) (by simpa using scale_1243.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1397) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1397^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1397^2)) (by simpa using scale_1397.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1441) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1441^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1441^2)) (by simpa using scale_1441.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1507) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1507^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1507^2)) (by simpa using scale_1507.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1529) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1529^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1529^2)) (by simpa using scale_1529.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1639) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1639^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1639^2)) (by simpa using scale_1639.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1661) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1661^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1661^2)) (by simpa using scale_1661.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1727) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1727^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1727^2)) (by simpa using scale_1727.1))
  exact .nil

def uppersBlock_013 : List Coeff := [(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1793 (74916451901/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1837 (15031777603/1000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1903 (75511865833/5000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1969 (15170561589/1000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 1991 (37981960099/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2101 (239067763/15625000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2123 (76605851767/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2167 (76810987163/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2189 (38455999061/2500000000:ℝ)),(upperCut grid ⟨38066622832,38066626284,121961738303,121961738347,269722154090,269722158019,423807373897,182⟩ ⟨37841894340,37841897681,120628404970,120628405013,264646604380,264646607847,414863101987,176⟩ 221 (26990813499/2500000000:ℝ)),(upperCut grid ⟨36888792903,36888795643,116407085546,116407085585,248806081913,248806084045,387300047003,158⟩ ⟨36635614944,36635617482,114407085546,114407085584,241428323333,241428324916,374650936355,150⟩ 247 (13773470837/1250000000:ℝ)),(upperCut grid ⟨35263604640,35263605658,108145415261,108145415294,218867887079,218867887445,336707739560,127⟩ ⟨34965075281,34965075844,106968944673,106968944705,214719227710,214719227955,329847796152,123⟩ 299 (57004435713/5000000000:ℝ)),(upperCut grid ⟨32958368645,32958368675,97737483191,97737483217,183234735442,183234735587,279027206320,95⟩ ⟨32580965366,32580965395,96256001710,96256001735,178352014162,178352014301,271329202728,91⟩ 377 (59322451851/5000000000:ℝ)),(upperCut grid ⟨32188758235,32188758263,94717540172,94717540196,173339557952,173339558086,263484557320,87⟩ ⟨31780538290,31780538317,93517540172,93517540195,169476906964,169476907094,257484557320,84⟩ 403 (11997873119/1000000000:ℝ)),(upperCut grid ⟨30445224365,30445224389,87496459804,87496459824,150536800308,150536800419,228456308758,70⟩ ⟨29957322724,29957322747,85591697900,85591697919,144737709953,144737710059,219727593146,66⟩ 481 (61758671469/5000000000:ℝ)),(upperCut grid ⟨29444389781,29444389803,82591697900,82591697918,135750513136,135750513234,206311185278,60⟩ ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ 533 (62785212489/5000000000:ℝ))]

theorem uppersBlock_013_sum : sumCoeff uppersBlock_013 = ⟨(357221521995428069471224005627897294963835618994699474467897369371887/233520722900410052374061099395656540044982565919603883885605837000000000:ℝ),(-444722413587739818368823613711893038191734150474776966394118585211340384506727239/21993223255922239846436357852565066379236504591997176133191756631250000000000000000:ℝ),(572709096309290170698563816404939325374027/199656497894155850891622156738664375000000:ℝ),(-92382:ℝ)⟩ := by
  norm_num [uppersBlock_013,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_013_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [1793,1837,1903,1969,1991,2101,2123,2167,2189,221,247,299,377,403,481,533] uppersBlock_013 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_013
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1793) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1793^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1793^2)) (by simpa using scale_1793.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1837) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1837^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1837^2)) (by simpa using scale_1837.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1903) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1903^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1903^2)) (by simpa using scale_1903.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1969) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1969^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1969^2)) (by simpa using scale_1969.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1991) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*1991^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*1991^2)) (by simpa using scale_1991.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2101) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2101^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2101^2)) (by simpa using scale_2101.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2123) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2123^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2123^2)) (by simpa using scale_2123.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2167) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2167^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2167^2)) (by simpa using scale_2167.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2189) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2189^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2189^2)) (by simpa using scale_2189.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=221) hN1 (by decide) state_45 state_44 (by decide) (by decide) (Nat.le_trans (by decide : 44^2*221^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤45^2*221^2)) (by simpa using scale_221.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=247) hN1 (by decide) state_40 state_39 (by decide) (by decide) (Nat.le_trans (by decide : 39^2*247^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤40^2*247^2)) (by simpa using scale_247.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=299) hN1 (by decide) state_34 state_33 (by decide) (by decide) (Nat.le_trans (by decide : 33^2*299^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤34^2*299^2)) (by simpa using scale_299.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=377) hN1 (by decide) state_27 state_26 (by decide) (by decide) (Nat.le_trans (by decide : 26^2*377^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤27^2*377^2)) (by simpa using scale_377.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=403) hN1 (by decide) state_25 state_24 (by decide) (by decide) (Nat.le_trans (by decide : 24^2*403^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤25^2*403^2)) (by simpa using scale_403.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=481) hN1 (by decide) state_21 state_20 (by decide) (by decide) (Nat.le_trans (by decide : 20^2*481^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤21^2*481^2)) (by simpa using scale_481.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=533) hN1 (by decide) state_19 state_18 (by decide) (by decide) (Nat.le_trans (by decide : 18^2*533^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤19^2*533^2)) (by simpa using scale_533.1))
  exact .nil

def uppersBlock_014 : List Coeff := [(upperCut grid ⟨28903717569,28903717590,81539066322,81539066339,132651103686,132651103781,201722870600,58⟩ ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ 559 (39538433/3125000:ℝ)),(upperCut grid ⟨28332133431,28332133451,78205732989,78205733005,123016531163,123016531250,187580734976,52⟩ ⟨27725887213,27725887232,77029262401,77029262416,119683338995,119683339079,182730022474,50⟩ 611 (16037741851/1250000000:ℝ)),(upperCut grid ⟨27080502002,27080502020,73904262401,73904262415,111018999241,111018999318,170230022474,45⟩ ⟨26390573288,26390573305,71237595735,71237595748,103797532041,103797532112,159902066882,41⟩ 689 (16338102573/1250000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 767 (66424865463/5000000000:ℝ)),(upperCut grid ⟨25649493567,25649493583,68380452878,68380452890,96257368245,96257368310,149211617202,37⟩ ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ 793 (13351645927/1000000000:ℝ)),(upperCut grid ⟨24849066491,24849066506,66841991340,66841991351,92311292312,92311292374,143664615238,35⟩ ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ 871 (33848208559/2500000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 923 (68276289663/5000000000:ℝ)),(upperCut grid ⟨23978952722,23978952736,61841991340,61841991350,79886759067,79886759120,126344107162,29⟩ ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ 949 (68554085291/5000000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1027 (34671984687/2500000000:ℝ)),(upperCut grid ⟨23025850924,23025850937,60023809522,60023809531,75526949482,75526949531,120313880270,27⟩ ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ 1079 (4364868557/312500000:ℝ)),(upperCut grid ⟨21972245768,21972245780,56023809522,56023809530,66316609113,66316609156,107664769626,23⟩ ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ 1157 (70535854513/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1261 (35698300291/2500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1313 (71800695959/5000000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1339 (7199678067/500000000:ℝ)),(upperCut grid ⟨20794415412,20794415423,52690476189,52690476196,58992527191,58992527229,97664769624,20⟩ ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ 1391 (72377779127/5000000000:ℝ)),(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1417 (36281484801/2500000000:ℝ))]

theorem uppersBlock_014_sum : sumCoeff uppersBlock_014 = ⟨(15108649472838872527211573611605205937125489711473179903707796804669/54947132957237734352810703626849741385934447970906764330744985000000000:ℝ),(-7164140213707164183782287490581882355691874000866706149955683204123665719493023/1785781821110226366466347867872616595042869559054469840749212012500000000000000000:ℝ),(197153945864729118553496238915057895723/204666303216980104438590498128750000000:ℝ),(-14312:ℝ)⟩ := by
  norm_num [uppersBlock_014,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_014_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [559,611,689,767,793,871,923,949,1027,1079,1157,1261,1313,1339,1391,1417] uppersBlock_014 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_014
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=559) hN1 (by decide) state_18 state_17 (by decide) (by decide) (Nat.le_trans (by decide : 17^2*559^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤18^2*559^2)) (by simpa using scale_559.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=611) hN1 (by decide) state_17 state_16 (by decide) (by decide) (Nat.le_trans (by decide : 16^2*611^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤17^2*611^2)) (by simpa using scale_611.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=689) hN1 (by decide) state_15 state_14 (by decide) (by decide) (Nat.le_trans (by decide : 14^2*689^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤15^2*689^2)) (by simpa using scale_689.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=767) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*767^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤13^2*767^2)) (by simpa using scale_767.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=793) hN1 (by decide) state_13 state_12 (by decide) (by decide) (Nat.le_trans (by decide : 12^2*793^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤13^2*793^2)) (by simpa using scale_793.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=871) hN1 (by decide) state_12 state_11 (by decide) (by decide) (Nat.le_trans (by decide : 11^2*871^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤12^2*871^2)) (by simpa using scale_871.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=923) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*923^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤11^2*923^2)) (by simpa using scale_923.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=949) hN1 (by decide) state_11 state_10 (by decide) (by decide) (Nat.le_trans (by decide : 10^2*949^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤11^2*949^2)) (by simpa using scale_949.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1027) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1027^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤10^2*1027^2)) (by simpa using scale_1027.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1079) hN1 (by decide) state_10 state_9 (by decide) (by decide) (Nat.le_trans (by decide : 9^2*1079^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤10^2*1079^2)) (by simpa using scale_1079.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1157) hN1 (by decide) state_9 state_8 (by decide) (by decide) (Nat.le_trans (by decide : 8^2*1157^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤9^2*1157^2)) (by simpa using scale_1157.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1261) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1261^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1261^2)) (by simpa using scale_1261.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1313) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1313^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1313^2)) (by simpa using scale_1313.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1339) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1339^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1339^2)) (by simpa using scale_1339.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1391) hN1 (by decide) state_8 state_7 (by decide) (by decide) (Nat.le_trans (by decide : 7^2*1391^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤8^2*1391^2)) (by simpa using scale_1391.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1417) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1417^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1417^2)) (by simpa using scale_1417.1))
  exact .nil

def uppersBlock_015 : List Coeff := [(upperCut grid ⟨19459101486,19459101496,47690476189,47690476195,48595319485,48595319517,83522634000,16⟩ ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ 1469 (36461684481/2500000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1651 (592730893/40000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1703 (7440146399/500000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1781 (18712325003/1250000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1807 (18748557521/1250000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1937 (15137790761/1000000000:ℝ)),(upperCut grid ⟨17917594688,17917594697,44833333332,44833333337,43035576204,43035576232,75963344538,14⟩ ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ 1963 (75822289113/5000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2041 (15242389759/1000000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2119 (38293496373/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2171 (3841471443/250000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2249 (38591203339/2500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2327 (7752334879/500000000:ℝ)),(upperCut grid ⟨16094379121,16094379129,38166666666,38166666670,31090513079,31090513100,59633412918,10⟩ ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ 2353 (77634461043/5000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2483 (15634445001/1000000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2509 (19569098153/1250000000:ℝ)),(upperCut grid ⟨13862943608,13862943615,34166666666,34166666669,24652761431,24652761448,50689141008,8⟩ ⟨10986122884,10986122890,26666666666,26666666668,14255553725,14255553736,35689141008,5⟩ 2561 (9810191001/625000000:ℝ))]

theorem uppersBlock_015_sum : sumCoeff uppersBlock_015 = ⟨(5603369847315520999474396936227509095910869857612444956528326984915825214317/165896595683560657858709294421776535541820500966405908703978100664607296050000000:ℝ),(-5552835069272633094806528250922438383716000931153359550297246459598861543688485108732383/10368537230222541116169330901361033471363781310400369293998631291537956003125000000000000000:ℝ),(242627278682678308597854575944879954438419987/1138449451569026686718203262795825680625000000:ℝ),(-1255:ℝ)⟩ := by
  norm_num [uppersBlock_015,sumCoeff,addCoeff,zeroCoeff,upperCut,lowerCut,aL,aU,jL,jU,sU,chooseUpper,chooseLower,grid]

theorem uppersBlock_015_bound {N:ℕ} (hlo:97370944≤N) (hhi:N≤97397160) :
    List.Forall₂ (fun r c => (DivCount 3 (N/(r*r)):ℝ)≤eval c N) [1469,1651,1703,1781,1807,1937,1963,2041,2119,2171,2249,2327,2353,2483,2509,2561] uppersBlock_015 := by
  have hN1 : 1≤N := by omega
  unfold uppersBlock_015
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1469) hN1 (by decide) state_7 state_6 (by decide) (by decide) (Nat.le_trans (by decide : 6^2*1469^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤7^2*1469^2)) (by simpa using scale_1469.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1651) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1651^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1651^2)) (by simpa using scale_1651.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1703) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1703^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1703^2)) (by simpa using scale_1703.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1781) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1781^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1781^2)) (by simpa using scale_1781.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1807) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1807^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1807^2)) (by simpa using scale_1807.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1937) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1937^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1937^2)) (by simpa using scale_1937.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=1963) hN1 (by decide) state_6 state_5 (by decide) (by decide) (Nat.le_trans (by decide : 5^2*1963^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤6^2*1963^2)) (by simpa using scale_1963.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2041) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2041^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2041^2)) (by simpa using scale_2041.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2119) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2119^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2119^2)) (by simpa using scale_2119.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2171) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2171^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2171^2)) (by simpa using scale_2171.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2249) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2249^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2249^2)) (by simpa using scale_2249.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2327) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2327^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2327^2)) (by simpa using scale_2327.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2353) hN1 (by decide) state_5 state_4 (by decide) (by decide) (Nat.le_trans (by decide : 4^2*2353^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤5^2*2353^2)) (by simpa using scale_2353.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2483) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2483^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤4^2*2483^2)) (by simpa using scale_2483.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2509) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2509^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤4^2*2509^2)) (by simpa using scale_2509.1))
  refine .cons ?_ ?_
  · simpa only [pow_two,grid] using (actual_upper_cut (N:=N) (r:=2561) hN1 (by decide) state_4 state_3 (by decide) (by decide) (Nat.le_trans (by decide : 3^2*2561^2≤97370944) hlo) (Nat.le_trans hhi (by decide : 97397160≤4^2*2561^2)) (by simpa using scale_2561.1))
  exact .nil

end
end JSP233.PrimeWindowB132.Blocks
